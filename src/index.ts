import {
  Subject,
  interval,
  fromEvent,
  merge,
  Observable,
  OperatorFunction,
  of,
  empty,
  Subscription,
  PartialObserver,
  iif,
  animationFrameScheduler,
} from "rxjs";
import {
  scan,
  map,
  filter,
  withLatestFrom,
  retryWhen,
  takeUntil,
  concatAll,
  mergeAll,
} from "rxjs/operators";
import compile = WebAssembly.compile;

type Rect = {
  x: number;
  y: number;
  width: number;
  height: number;
}

type RotateRect = {
  weightX: number,
  weightY: number,
  width: number,
  height: number,
  angle: number // 顺时针偏移x轴的角度
}

type RotateRectPoints = {
  point1: {
    x: number,
    y: number
  }
  point2: {
    x: number,
    y: number
  }
  point3: {
    x: number,
    y: number
  }
  point4: {
    x: number,
    y: number
  }
}

type State = {
  bricks: {
    position: Rect;
    exist: boolean;
  }[];
  paddle: {
    position: RotateRect;
    speed: number;
  };
  ball: {
    position: {
      x: number;
      y: number;
      radius: number;
    };
    speed: {
      vx: number;
      vy: number;
    };
  };
  status: "gameover" | "playing" | "notstart";
  timeUsed: number;
  currentTime: number
};

type Ticker = {
  deltaTime: number;
  currentTime: number;
};

type MoveEvent = {
  target: "left" | "right";
  action: 'up' | 'move'
};

type LineParam = {
  k:  number
  b:  number
  c: number
  special: boolean // x = c
}

const stageBackground = "#B3F0E8";
const spiritColor = "#08979c";
const ballColor = "#5cdbd3";
const leftButton = document.getElementById("left-move") as HTMLDivElement;
const rightButton = document.getElementById("right-move") as HTMLDivElement;
const retryButton = document.getElementById("retry") as HTMLDivElement;
const leftUpButton = document.getElementById('left-up') as HTMLDivElement
const rightUpButton = document.getElementById('right-up') as HTMLDivElement
const stage = document.getElementById("stage-canvas") as HTMLCanvasElement;
const score = document.getElementById('score') as HTMLSpanElement
const ctx = stage.getContext("2d")!;
const width = stage.getBoundingClientRect().width;
const height = stage.getBoundingClientRect().height;
ctx.fillStyle = stageBackground;
ctx.fillRect(0, 0, width, height);
const paddleWidth = width / 4;
const paddleHeight = 15;
const ballRadius = 10;
const brickRow = 5;
const brickCol = 7;
const brickHeight = 20;
const brickGap = 3;
const bricksMargin = 10;
const brickWidth =
  (width - (brickCol - 1) * brickGap - 2 * bricksMargin) / brickCol;
const ballVMax = 0.2;
const ballVMin = 0.15;

// 旋转paddle
const parseRotateRectCoordinate = (rect: RotateRect): RotateRectPoints => {
  // 获取4个顶点的坐标
  const anglePi = rect.angle / 180 * Math.PI
  const point1 = {
    x: paddleWidth / 2 * Math.cos(anglePi) + paddleHeight / 2 * Math.sin(anglePi) + rect.weightX,
    y: paddleWidth / 2 * Math.sin(anglePi) - paddleHeight / 2 * Math.cos(anglePi) + rect.weightY
  }
  const point2 = {
    x: paddleWidth / 2 * Math.cos(anglePi) - paddleHeight / 2 * Math.sin(anglePi) + rect.weightX,
    y: paddleWidth / 2 * Math.sin(anglePi) + paddleHeight / 2 * Math.cos(anglePi) + rect.weightY
  }
  const point3 = {
    x: rect.weightX - paddleHeight / 2 * Math.sin(anglePi) - paddleWidth / 2 * Math.cos(anglePi),
    y: rect.weightY - paddleWidth / 2 * Math.sin(anglePi) + paddleHeight / 2 * Math.cos(anglePi)
  }
  const point4 = {
    x: rect.weightX + paddleHeight / 2 * Math.sin(anglePi) - paddleWidth / 2 * Math.cos(anglePi),
    y: rect.weightY - paddleWidth / 2 * Math.sin(anglePi) - paddleHeight / 2 * Math.cos(anglePi)
  }
  return {
    point1, point2, point3, point4
  }
}

const initBricks = () => {
  const bricks: State['bricks'] = []
  for (let i=0; i<brickCol; i++) {
    for (let j=0; j<brickRow; j++) {
      const x = bricksMargin + i * (brickGap + brickWidth)
      const y = bricksMargin + j * (brickGap + brickHeight)
      bricks.push({
        position: {
          x,
          y,
          width: brickWidth,
          height: brickHeight
        },
        exist: true
      })
    }
  }
  return bricks
};

const getBoundRect = (ball: State['ball']['position']) => {
  return {
    x: ball.x - ball.radius,
    y: ball.y - ball.radius,
    width: ball.radius * 2,
    height: ball.radius * 2
  }
}

// 检测在x和y两个轴上的投影是否都重叠
const analyseTwoRectKnockedStatus = (rect1: Rect, rect2: Rect) => {
  const minX = Math.min(rect1.x, rect1.x + rect1.width, rect2.x, rect2.x + rect2.width)
  const maxX = Math.max(rect1.x, rect1.x + rect1.width, rect2.x, rect2.x + rect2.width)
  const minY = Math.min(rect1.y, rect1.y + rect1.height, rect2.y, rect2.y + rect2.height)
  const maxY = Math.max(rect1.y, rect1.y + rect1.height, rect2.y, rect2.y + rect2.height)
  const xGap = rect1.width + rect2.width - (maxX - minX)
  const yGap = rect1.height + rect2.height - (maxY - minY)
  const isKnocked = xGap >= 0 && yGap >= 0
  // 判断碰撞方向
  return {
    isKnocked,
    direction: isKnocked ? xGap > yGap ? 'vertical' : 'horizontal' : undefined
  }
}

// 计算两点所在的直线的公式
const getLineParam = (point1: {x: number, y: number}, point2: {x: number, y: number}): LineParam => {
  if (point2.x === point1.x) {
    return {
      k: 0,
      c: point1.x,
      b: 0,
      special: true
    }
  }
  const k = (point2.y - point1.y) / (point2.x - point1.x)
  const b = point1.y - k * point1.x
  return {
    k,
    b,
    c: 0,
    special: false
  }
}

// 计算点到直线的距离
const getDistance = (point: {x: number, y: number}, line: LineParam) => {
  if (line.special) {
    return Math.abs(point.x - line.c)
  }
  if (line.k === 0) {
    return Math.abs(point.y - line.b)
  }
  return Math.abs((point.y - line.k * point.x - line.b) * Math.cos(Math.atan(line.k)))
}

const getMediumPoint = (point1: {x: number, y: number}, point2: {x: number, y: number}) => {
  return {
    x: (point1.x + point2.x) / 2,
    y: (point1.y + point2.y) / 2
  }
}

const drawLine = (line: LineParam, ctx: CanvasRenderingContext2D, strokeColor = 'red') => {
  const points: {x: number, y: number}[] = []
  if (line.special) {
    points.push({x: line.c, y: 0})
    points.push({x: line.c, y: height})
  } else {
    points.push({x: 0, y: line.b})
    points.push({x: width, y: line.k * width + line.b})
  }
  ctx.beginPath()
  ctx.strokeStyle = strokeColor
  ctx.moveTo(points[0].x, points[0].y)
  ctx.lineTo(points[1].x, points[1].y)
  ctx.stroke()
  ctx.closePath()
}

// 检测ball和paddle的碰撞情况
const analysePaddleKnockedStatus = (ball: State['ball'], paddle: RotateRect) => {
  const points = parseRotateRectCoordinate(paddle)
  // 穿过重心与长边平行的线
  const longLine = getLineParam(getMediumPoint(points.point1, points.point2), getMediumPoint(points.point3, points.point4))
  // 穿过重心与短边平行的线
  const shortLine = getLineParam(getMediumPoint(points.point1, points.point4), getMediumPoint(points.point2, points.point3))
  const longDis = getDistance({x: ball.position.x, y: ball.position.y}, longLine)
  const shortDis = getDistance({x: ball.position.x, y: ball.position.y}, shortLine)
  // 未发生碰撞
  if (longDis - ball.position.radius > paddle.height / 2 || shortDis - ball.position.radius > paddle.width / 2) {
    return {
      isKnocked: false,
      vx: ball.speed.vx,
      vy: ball.speed.vy
    }
  }
  // 与长边碰撞
  if (Math.abs(paddle.height / 2 - longDis - ball.position.radius) < Math.abs(paddle.width / 2 - shortDis - ball.position.radius)) {
    const alpha = paddle.angle / 180 * Math.PI
    const beta = ball.speed.vy === 0 ? Math.PI / 2
      : ball.speed.vx === 0 ? 0 : Math.atan(ball.speed.vx / ball.speed.vy)
    const gama = Math.PI / 2 - (Math.PI / 2 - alpha - beta + Math.PI / 2 - alpha)
    const speed = Math.sqrt(ball.speed.vx * ball.speed.vx + ball.speed.vy * ball.speed.vy)
    const newVx = speed * Math.cos(gama)
    const newVy = speed * Math.sin(gama)
    return {
      isKnocked: true,
      vx: newVx,
      vy: newVy
    }
  } else {
    const alpha = paddle.angle / 180 * Math.PI
    const beta = ball.speed.vy === 0 ? 0
      : ball.speed.vx === 0 ? Math.PI / 2 : Math.atan(ball.speed.vy / ball.speed.vx)
    const gama = Math.PI / 2 - alpha - (alpha - beta)
    const speed = Math.sqrt(ball.speed.vx * ball.speed.vx + ball.speed.vy * ball.speed.vy)
    const newVx = speed * Math.sin(gama)
    const newVy = speed * Math.cos(gama)
    return {
      isKnocked: true,
      vx: newVx,
      vy: newVy
    }
  }

}

// 判断小球是否与墙面相撞
const isKnockedWithWall = (
  ball: State["ball"]
) => {
  const boundRect = getBoundRect(ball.position)
  return boundRect.x <= 0 ||
    boundRect.x >= width - boundRect.width ||
    boundRect.y <= 0 ||
    boundRect.y >= height - boundRect.height
};

const randomDeltaValue = (value: number, disturbance: number) => {
  return Math.random() * disturbance * value;
};

const getBoundingRectOfPaddle = (paddle: RotateRect): Rect => {
  const points = parseRotateRectCoordinate(paddle)
  const x = Math.min(points.point1.x, points.point2.x, points.point3.x, points.point4.x)
  const y = Math.min(points.point1.y, points.point2.y, points.point3.y, points.point4.y)
  const width = Math.max(points.point1.x, points.point2.x, points.point3.x, points.point4.x) - x
  const height = Math.max(points.point1.y, points.point2.y, points.point3.y, points.point4.y) - y
  return {
    x, y, width, height
  }
}

// 碰撞完毕反弹后，方向增加扰动
const analyseBallSpeed = (
  ball: State["ball"],
  width: number,
  height: number,
  bricks: State['bricks'],
  paddle: State['paddle']
) => {
  // const randomDeltaVx = randomDeltaValue(ball.speed.vx, 0.05);
  // const randomDeltaVy = randomDeltaValue(ball.speed.vy, 0.05);
  const randomDeltaVx = 0
  const randomDeltaVy = 0
  const newSpeed = {
    vx: ball.speed.vx + randomDeltaVx,
    vy: ball.speed.vy + randomDeltaVy,
  }
  const boundRect = getBoundRect(ball.position)
  const knockedWall = isKnockedWithWall(ball)
  if (knockedWall) {
    if (boundRect.x <= 0 || boundRect.x + boundRect.width >= width) {
      return {
        vx: -newSpeed.vx,
        vy: newSpeed.vy,
      };
    } else {
      return {
        vx: newSpeed.vx,
        vy: -newSpeed.vy,
      };
    }
  }
  // 分析是否与paddle相撞
  const knockedPaddleStatus = analysePaddleKnockedStatus(ball, paddle.position)
  if (knockedPaddleStatus.isKnocked) {
    return {
      vx: knockedPaddleStatus.vx,
      vy: knockedPaddleStatus.vy
    }
  }
  // 分析是否与砖块相撞
  for (let brick of bricks) {
    if (brick.exist) {
      const knockedStatus = analyseTwoRectKnockedStatus(boundRect, brick.position)
      if (knockedStatus.isKnocked) {
        if (knockedStatus.direction === 'vertical') {
          return {
            vx: newSpeed.vx,
            vy: -newSpeed.vy,
          };
        } else {
          return {
            vx: -newSpeed.vx,
            vy: newSpeed.vy,
          };
        }
      }
    }
  }
  // 什么都没碰到
  return { ...ball.speed };
};

const analyseBricks = (ball: State["ball"], bricks: State["bricks"]) => {
  const newBricks: State["bricks"] = [];
  const boundRect = getBoundRect(ball.position)
  for (let brick of bricks) {
    const newBrick = { ...brick };
    if (brick.exist && analyseTwoRectKnockedStatus(boundRect, brick.position).isKnocked) {
      newBrick.exist = false;
    }
    newBricks.push(newBrick);
  }
  return newBricks;
};

const createHiDPICanvas = (w: number, h: number, ratio: number = 3) => {
  const PIXEL_RATIO = () => {
    const c = document.createElement("canvas"),
      ctx = c.getContext("2d")! as any,
      dpr = window.devicePixelRatio || 1,
      bsr =
        ctx["webkitBackingStorePixelRatio"] ||
        ctx["mozBackingStorePixelRatio"] ||
        ctx["msBackingStorePixelRatio"] ||
        ctx["oBackingStorePixelRatio"] ||
        ctx["backingStorePixelRatio"] ||
        1;
    return dpr / bsr;
  };

  if (!ratio) {
    ratio = PIXEL_RATIO();
  }
  const can = document.createElement("canvas");
  can.width = w * ratio;
  can.height = h * ratio;
  can.style.width = w + "px";
  can.style.height = h + "px";
  can.getContext("2d")!.setTransform(ratio, 0, 0, ratio, 0, 0);
  return can;
};

const drawPaddle = (
  context: CanvasRenderingContext2D,
  position: State["paddle"]
) => {
  const points = parseRotateRectCoordinate(position.position)
  context.fillStyle = spiritColor;
  context.moveTo(points.point1.x, points.point1.y)
  context.beginPath()
  context.lineTo(points.point2.x, points.point2.y)
  context.lineTo(points.point3.x, points.point3.y)
  context.lineTo(points.point4.x, points.point4.y)
  context.lineTo(points.point1.x, points.point1.y)
  context.fill()
  context.closePath()
  context.fillStyle = stageBackground
  context.beginPath()
  context.arc(position.position.weightX, position.position.weightY, 2, 0, Math.PI * 2, false)
  context.fill()
  context.closePath()
};

const drawBricks = (
  context: CanvasRenderingContext2D,
  positions: State["bricks"]
) => {
  context.fillStyle = spiritColor;
  for (let position of positions) {
    if (position.exist) {
      context.fillRect(
        position.position.x,
        position.position.y,
        position.position.width,
        position.position.height
      );
    }
  }
};

const drawBall = (
  context: CanvasRenderingContext2D,
  position: State["ball"]
) => {
  context.fillStyle = ballColor;
  context.beginPath();
  context.arc(
    position.position.x,
    position.position.y,
    position.position.radius,
    0,
    Math.PI * 2
  );
  context.fill();
  context.closePath();
};

const movePaddle = (
  paddle: State["paddle"],
  event: MoveEvent,
  width: number
) => {
  if (event.action === 'move') {
    if (event.target === "left") {
      // 计算下一次paddle的位置和速度
      let nextX = paddle.position.weightX - paddle.speed;
      const boundRect = getBoundingRectOfPaddle({
        ...paddle.position,
        weightX: nextX
      })
      if (boundRect.x <= 0) nextX = boundRect.width / 2
      const nextPos: State["paddle"] = {
        position: {
          ...paddle.position,
          weightX: nextX,
        },
        speed: paddle.speed,
      };
      return nextPos;
    } else {
      let nextX = paddle.position.weightX + paddle.speed;
      const boundRect = getBoundingRectOfPaddle({
        ...paddle.position,
        weightX: nextX
      })
      if (boundRect.x + boundRect.width >= width)
        nextX = width - boundRect.width / 2;
      const nextPos: State["paddle"] = {
        position: {
          ...paddle.position,
          weightX: nextX,
        },
        speed: paddle.speed,
      };
      return nextPos;
    }
  } else {
    const maxAngle = 80
    const minAngle = -80
    let newAngle = event.target === 'left' ? paddle.position.angle + 4
      : paddle.position.angle - 4
    newAngle = newAngle < minAngle ? minAngle
      : newAngle > maxAngle ? maxAngle
      : newAngle
    return {
      position: {
        ...paddle.position,
        angle: newAngle
      },
      speed: paddle.speed
    }
  }
};

const initState = () => {
  const state = {} as State;
  state.paddle = {
    position: {
      weightX: width / 2,
      weightY: height - paddleWidth / 2 - 10,
      width: paddleWidth,
      height: paddleHeight,
      angle: 20
    },
    speed: 10,
  };
  state.ball = {
    position: {
      x: Math.random() * (width - 2 * ballRadius - 10) + ballRadius + 5,
      y: height - (Math.random() * 20 + paddleHeight + 15 + ballRadius),
      radius: ballRadius,
    },
    speed: {
      vx: 0.18 * (Math.random() < 0.5 ? -1 : 1),
      vy: -0.18,
    },
  };
  state.status = "notstart";
  state.bricks = initBricks();
  state.timeUsed = 0
  state.currentTime = new Date().getTime()
  return state;
};

const drawView = (state: State) => {
  const tempCanvas = document.createElement("canvas");
  tempCanvas.width = width;
  tempCanvas.height = height;
  const tempCtx = tempCanvas.getContext("2d")!;
  tempCtx.fillStyle = stageBackground;
  tempCtx.fillRect(0, 0, width, height);
  drawBall(tempCtx, state.ball);
  drawPaddle(tempCtx, state.paddle);
  drawBricks(tempCtx, state.bricks)
  stage.width = width;
  stage.height = height;
  stage.getContext("2d")!.drawImage(tempCanvas, 0, 0, width, height);
  score.innerText = `${Math.round(state.timeUsed / 100) / 10}s`
};

const drawGameOver = () => {
  const tempCanvas = createHiDPICanvas(width, height);
  const tempCtx = tempCanvas.getContext("2d")!;
  const text = "游戏结束";
  tempCtx.fillStyle = spiritColor;
  tempCtx.font = "20px sans-serif";
  tempCtx.textBaseline = "middle";
  tempCtx.textAlign = "center";
  tempCtx.fillText(text, width / 2, height / 2);
  stage.getContext("2d")!.drawImage(tempCanvas, 0, 0, width, height);
  console.log(`draw game over`);
};

// 实现长按移动paddle事件流
const longTap = (
  down$: Observable<MouseEvent | TouchEvent>,
  up$: Observable<MouseEvent | TouchEvent>,
  direction: "left" | "right",
  action: 'up' | 'move'
): Observable<MoveEvent> => {
  return down$.pipe(
    map(() => {
      return interval(1000 / 60).pipe(
        map(() => {
          return {
            target: direction,
            action
          };
        }),
        takeUntil(up$) // 这里实现了长按后持续产生事件，松开后取消事件
      );
    }),
    mergeAll()
  );
};

const baseEventMap = <T extends Event|MouseEvent|TouchEvent>(event: T) => {
  event.preventDefault()
  return event
}

const main = () => {
  const ticker$: Observable<Ticker> = interval(
    ~~(1000 / 60),
    animationFrameScheduler
  )
    .pipe(map(() => ({ currentTime: new Date().getTime(), deltaTime: 0 })))
    .pipe(
      scan((acc, value) => {
        const deltaTime = value.currentTime - acc.currentTime;
        return {
          deltaTime,
          currentTime: new Date().getTime(),
        };
      })
    );
  const leftMouseUp$: Observable<MouseEvent> = fromEvent<MouseEvent>(
    leftButton,
    "mouseup"
  ).pipe(
    map(baseEventMap)
  );
  const leftMouseDown$: Observable<MouseEvent> = fromEvent<MouseEvent>(
    leftButton,
    "mousedown"
  ).pipe(
    map(baseEventMap)
  );
  const rightMouseUp$: Observable<MouseEvent> = fromEvent<MouseEvent>(
    rightButton,
    "mouseup"
  ).pipe(
    map(baseEventMap)
  );
  const rightMouseDown$: Observable<MouseEvent> = fromEvent<MouseEvent>(
    rightButton,
    "mousedown"
  ).pipe(
    map(baseEventMap)
  );
  const leftTouchStart$: Observable<TouchEvent> = fromEvent<TouchEvent>(
    leftButton,
    "touchstart"
  ).pipe(
    map(baseEventMap)
  );
  const leftTouchEnd$: Observable<TouchEvent> = fromEvent<TouchEvent>(
    leftButton,
    "touchend"
  ).pipe(
    map(baseEventMap)
  );
  const rightTouchStart$: Observable<TouchEvent> = fromEvent<TouchEvent>(
    rightButton,
    "touchstart"
  ).pipe(
    map(baseEventMap)
  );
  const rightTouchEnd$: Observable<TouchEvent> = fromEvent<TouchEvent>(
    rightButton,
    "touchend"
  ).pipe(
    map(baseEventMap)
  );
  const leftUpMouseDown$: Observable<MouseEvent> = fromEvent<MouseEvent>(leftUpButton, 'mousedown').pipe(
    map(baseEventMap)
  )
  const leftUpMouseUp$: Observable<MouseEvent> = fromEvent<MouseEvent>(leftUpButton, 'mouseup').pipe(
    map(baseEventMap)
  )
  const leftUpTouchStart$: Observable<TouchEvent> = fromEvent<TouchEvent>(leftUpButton, 'touchstart').pipe(
    map(baseEventMap)
  )
  const leftUpTouchEnd$: Observable<TouchEvent> = fromEvent<TouchEvent>(leftUpButton, 'touchend').pipe(
    map(baseEventMap)
  )
  const rightUpMouseDown$: Observable<MouseEvent> = fromEvent<MouseEvent>(rightUpButton, 'mousedown').pipe(
    map(baseEventMap)
  )
  const rightUpMouseUp$: Observable<MouseEvent> = fromEvent<MouseEvent>(rightUpButton, 'mouseup').pipe(
    map(baseEventMap)
  )
  const rightUpTouchStart$: Observable<TouchEvent> = fromEvent<TouchEvent>(rightUpButton, 'touchstart').pipe(
    map(baseEventMap)
  )
  const rightUpTouchEnd$: Observable<TouchEvent> = fromEvent<TouchEvent>(rightUpButton, 'touchend').pipe(
    map(baseEventMap)
  )
  const leftLongClicks$ = longTap(leftMouseDown$, leftMouseUp$, "left", 'move');
  const rightLongClicks$ = longTap(rightMouseDown$, rightMouseUp$, "right", 'move');
  const leftLongTouches$ = longTap(leftTouchStart$, leftTouchEnd$, "left", 'move');
  const rightLongTouches$ = longTap(rightTouchStart$, rightTouchEnd$, "right", 'move');
  const leftUpLongClicks$ = longTap(leftUpMouseDown$, leftUpMouseUp$, 'left', 'up')
  const rightUpLongClicks$ = longTap(rightUpMouseDown$, rightUpMouseUp$, 'right', 'up')
  const leftUpLongTaps$ = longTap(leftUpTouchStart$, leftUpTouchEnd$, 'left', 'up')
  const rightUpLongTaps$ = longTap(rightUpTouchStart$, rightUpTouchEnd$, 'right', 'up')

  const paddleMoveEvent$ = merge<MoveEvent, MoveEvent>(
    // 监听键盘移动事件
    fromEvent<KeyboardEvent>(document, "keydown").pipe(
      filter((event) => event.keyCode === 37 || event.keyCode === 39),
      map<KeyboardEvent, MoveEvent>((event) => {
        if (event.keyCode === 37) {
          return {
            target: "left",
            action: 'move'
          };
        } else {
          return {
            target: "right",
            action: 'move'
          };
        }
      })
    ),
    leftLongClicks$,
    rightLongClicks$,
    leftLongTouches$,
    rightLongTouches$,
    leftUpLongClicks$,
    rightUpLongClicks$,
    leftUpLongTaps$,
    rightUpLongTaps$
  ).pipe<State["paddle"]>(
    scan((state, event) => movePaddle(state, event, width), initState().paddle)
  );

  // paddle移动流
  const paddle$: Observable<State["paddle"]> = merge(
    paddleMoveEvent$,
    of(initState().paddle)
  );

  const createState = (): Observable<State> => {
    return ticker$.pipe(
      withLatestFrom(paddle$),
      scan((state, item) => {
        const tick = item[0];
        const paddle = item[1];
        let nextX =
          state.ball.position.x + tick.deltaTime * state.ball.speed.vx;
        nextX = nextX <= state.ball.position.radius ? state.ball.position.radius
          : nextX >= width - state.ball.position.radius ? width - state.ball.position.radius
            : nextX
        let nextY =
          state.ball.position.y + tick.deltaTime * state.ball.speed.vy;
        nextY = nextY <= state.ball.position.radius ? state.ball.position.radius
          : nextY >= height - state.ball.position.radius ? height - state.ball.position.radius
            : nextY
        const nextPos: State["ball"] = {
          ...state.ball,
          position: {
            ...state.ball.position,
            x: nextX,
            y: nextY,
          },
        };
        // 分析砖块
        const newBricks = analyseBricks(nextPos, state.bricks);
        const brickNotExisted = newBricks.map(brick => !brick.exist ? 1 : 0).reduce((acc: number, value: number) => acc + value, 0)
        const status: State['status'] = nextPos.position.y + nextPos.position.radius >= height ? "gameover"
          : brickNotExisted === brickCol * brickRow ? 'gameover' : state.status
        // ball与wall或者paddle相撞
        nextPos.speed = analyseBallSpeed(
          nextPos,
          width,
          height,
          state.bricks,
          paddle
        );

        const nextState: State = {
          ...state,
          ball: nextPos,
          paddle: { ...paddle },
          bricks: newBricks,
          status,
          timeUsed: new Date().getTime() - state.currentTime + state.timeUsed,
          currentTime: new Date().getTime()
        };
        return nextState;
      }, initState())
    );
  };
  const retry$: Observable<MouseEvent> = fromEvent<MouseEvent>(
    retryButton,
    "click"
  );
  let subscription: Subscription;
  const observer: PartialObserver<State> = {
    next: (state: State) => {
      drawView(state);
      if (state.status === "gameover") {
        console.log("gameover");
        subscription.unsubscribe();
        drawGameOver();
      }
    },
    error: (err) => {
      throw err;
    },
  };
  subscription = createState().subscribe(observer);
  retry$.subscribe({
    next: () => {
      subscription.unsubscribe();
      subscription = createState().subscribe(observer);
    },
  });
};

main();
