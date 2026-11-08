-- Prove2me | Definitions.Def_BC1992_Simulation
-- name    : BC1992_Simulation
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-08T00:36:25.274019+00:00
-- url     : https://prove2.me/theorems/b3f93a5b-eb02-43aa-a99c-1557feee58e4
-- title:
--   Section 3 (Lemma 3.1): Safe Word Combinators, Block-Table Configuration Encoding, and Explicit BC Simulator for Multi-Tape Turing Machines
-- statement:
--   Formalizes Section 3 (Lemma 3.1) of Bellantoni and Cook (1992): safe word combinators (`prependConst`, `constWord`, bounded decision trees `branchPrefix`, block shifts `dropConst` and `dropBlock`, and polynomial clock generator `polyWord : Poly -> Fn 1 0`), the fixed-width block-table encoding of `k`-tape Turing machine configurations (`BlockData`, `blockWidth`, `encBlock`, `decBlock`, `cfgBlock`, `encCfg`), and the explicit Bellantoni-Cook programs `initCfgBC`, `stepCfgBC`, `runCfgBC`, `outputCfgBC`, and `simTM : TM -> Poly -> Fn 1 0`.
-- source:
--   Stephen Bellantoni and Stephen Cook, 'A new recursion-theoretic characterization of the polytime functions', Computational Complexity 2 (1992), pp. 97-110 (doi:10.1007/BF01201998). Section 3, Lemma 3.1, pp. 102-105.

/-
  Source: Stephen Bellantoni and Stephen Cook,
  "A new recursion-theoretic characterization of the polytime functions",
  Computational Complexity 2 (1992), 97–110, DOI: 10.1007/BF01201998.

  Part III (`BC1992_Simulation`):
  Explicit Bellantoni–Cook encodings and safe-recursion programs simulating an arbitrary
  deterministic multi-tape Turing machine `M : TM` for `p(|x|)` transitions (§3, Lemma 3.1):
  polynomial clock generation (`polyWord`), block-table configuration encoding (`BlockData`,
  `encBlock`, `decBlock`, `encCfg`), initial configuration (`initCfgBC`), single-step
  sliding-window transition (`stepCfgBC`), `T`-step iteration (`runCfgBC`), output extraction
  (`outputCfgBC`), and full simulator (`simTM`).
-/
import Definitions.Def_BC1992_Syntax
import Definitions.Def_BC1992_Machines

namespace BC1992

/-! ## 1. Finite-Arity Tuple Helpers and Safe Word Combinators -/

def vec1 {α : Type _} (a : α) : Fin 1 → α := fun _ => a

def vec2 {α : Type _} (a b : α) : Fin 2 → α
  | ⟨0, _⟩ => a
  | ⟨_ + 1, _⟩ => b

def vec3 {α : Type _} (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨_ + 2, _⟩ => c

def vec4 {α : Type _} (a b c d : α) : Fin 4 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨_ + 3, _⟩ => d

/-- Constant empty word `ε` at any arity `(n; m)`. -/
def constZero {n m : Nat} : Fn n m :=
  .comp .zero Fin.elim0 Fin.elim0

/-- Prepend a constant word `u` onto the `j`-th safe argument (`Fn n m`). -/
def prependConstAt {n m : Nat} (j : Fin m) : Word → Fn n m
  | [] => .projS j
  | false :: u => .comp .s0 Fin.elim0 (vec1 (prependConstAt j u))
  | true :: u => .comp .s1 Fin.elim0 (vec1 (prependConstAt j u))

/-- Prepend a constant word `u` onto safe argument `0` (`Fn 0 1`). -/
def prependConst (u : Word) : Fn 0 1 :=
  prependConstAt ⟨0, Nat.zero_lt_one⟩ u

/-- Constant word `u` at any arity `(n; m)`. -/
def constWord {n m : Nat} (u : Word) : Fn n m :=
  .comp (prependConst u) Fin.elim0 (vec1 constZero)

/-- Take/pad a word to exact length `B` with `false` bits. -/
def padFalse : Nat → Word → Word
  | 0, _ => []
  | B + 1, [] => false :: padFalse B []
  | B + 1, b :: y => b :: padFalse B y

/-- Shift the safe arguments of `f : Fn 0 m` right by 1 (ignoring safe argument `0`). -/
def shiftSafe {m : Nat} (f : Fn 0 m) : Fn 0 (m + 1) :=
  .comp f Fin.elim0 (fun j => .projS j.succ)

/-- Apply `pred` to safe argument `0` before calling `g : Fn 0 (m + 1)`. -/
def predFirstSafe {m : Nat} (g : Fn 0 (m + 1)) : Fn 0 (m + 1) :=
  .comp g Fin.elim0 (Fin.cases (.comp .pred Fin.elim0 (vec1 (.projS ⟨0, Nat.zero_lt_succ m⟩)))
                               (fun j => .projS j.succ))

/--Bounded decision tree of depth `B` reading `padFalse B y₀` of safe argument `0`
   and dispatching to `K w : Fn 0 m` on the remaining `m` safe arguments. -/
def branchPrefix : {m : Nat} → (B : Nat) → (Word → Fn 0 m) → Fn 0 (m + 1)
  | _, 0, K => shiftSafe (K [])
  | _, B + 1, K =>
      let bFalse := predFirstSafe (branchPrefix B (fun w => K (false :: w)))
      let bTrue  := predFirstSafe (branchPrefix B (fun w => K (true :: w)))
      .comp .cond Fin.elim0
        (vec4 (.projS ⟨0, Nat.zero_lt_succ _⟩) bFalse bFalse bTrue)

/-- Drop `D` bits from safe argument `0` (`Fn 0 1`). -/
def dropConst : Nat → Fn 0 1
  | 0 => .projS ⟨0, Nat.zero_lt_one⟩
  | D + 1 => .comp .pred Fin.elim0 (vec1 (dropConst D))

/-- Drop `|u| * D` bits from safe argument `y` (`Fn 1 1`). -/
def dropBlock (D : Nat) : Fn 1 1 :=
  let step : Fn 1 2 := .comp (dropConst D) Fin.elim0 (vec1 (.projS ⟨0, by decide⟩))
  .srec (.projS ⟨0, Nat.zero_lt_one⟩) step step

/-- Prepend `|u|` `false` bits onto safe argument `y` (`Fn 1 1`). -/
def appendSafe : Fn 1 1 :=
  let s0_rec : Fn 1 2 := .comp .s0 Fin.elim0 (vec1 (.projS ⟨0, by decide⟩))
  .srec (.projS ⟨0, Nat.zero_lt_one⟩) s0_rec s0_rec

/-- Unary length multiplication (`Fn 2 0`): produces `false^(|u| * |v|)`. -/
def mulWord : Fn 2 0 :=
  let step : Fn 2 1 :=
    .comp appendSafe (vec1 (.projN ⟨1, by decide⟩)) (vec1 (.projS ⟨0, Nat.zero_lt_one⟩))
  .srec constZero step step

/-- Construct a BC program `polyWord p : Fn 1 0` whose output on `[x], []` has length `p.eval |x|`. -/
def polyWord : Poly → Fn 1 0
  | .const c => constWord (List.replicate c false)
  | .var => .projN ⟨0, Nat.zero_lt_one⟩
  | .add p q => .comp appendSafe (vec1 (polyWord p)) (vec1 (polyWord q))
  | .mul p q => .comp mulWord (vec2 (polyWord p) (polyWord q)) Fin.elim0
  | .comp p q => .comp (polyWord p) (vec1 (polyWord q)) Fin.elim0

/-! ## 2. Block-Table Encoding of Multi-Tape TM Configurations -/

/-- Concatenate `f (n - 1) ++ ... ++ f 0`. -/
def concatRev (f : Nat → Word) : Nat → Word
  | 0 => []
  | n + 1 => f n ++ concatRev f n

/-- Concatenate `f 0 ++ f 1 ++ ... ++ f (N - 1)`. -/
def tableOf (f : Nat → Word) (N : Nat) : Word :=
  concatRev (fun k => f (N - 1 - k)) N

/-- Reverse `|u|` blocks of width `D` from safe argument `y` (`Fn 1 1`). -/
def revBlocks (D : Nat) : Fn 1 1 :=
  let extractAndPrepend : Fn 1 2 :=
    .comp (branchPrefix D prependConst)
      Fin.elim0
      (vec2 (.comp (dropBlock D) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 (.projS ⟨1, by decide⟩)))
            (.projS ⟨0, by decide⟩))
  .srec constZero extractAndPrepend extractAndPrepend

/-- Unary encoding of `v : Fin W` as `W` bits: `v.val` `true`s followed by `W - v.val` `false`s. -/
def encFin {W : Nat} (v : Fin W) : Word :=
  List.replicate v.val true ++ List.replicate (W - v.val) false

/-- Count leading `true` bits of a word. -/
def countTrue : Word → Nat
  | [] => 0
  | false :: _ => 0
  | true :: w => countTrue w + 1

/-- Decode a word into `Fin W` (with `0 < W`). -/
def decFin {W : Nat} (hW : 0 < W) (w : Word) : Fin W :=
  if h : countTrue w < W then ⟨countTrue w, h⟩ else ⟨0, hW⟩

/-- Encode a tuple `Fin k → α` by concatenating fixed-width encodings. -/
def encTuple {α : Type _} (enc : α → Word) : {k : Nat} → (Fin k → α) → Word
  | 0, _ => []
  | _ + 1, f => enc (f ⟨0, Nat.zero_lt_succ _⟩) ++ encTuple enc (fun i => f i.succ)

/-- Decode a tuple `Fin k → α` from fixed-width slices of width `E`. -/
def decTuple {α : Type _} (E : Nat) (dec : Word → α) : (k : Nat) → Word → (Fin k → α)
  | 0, _, i => i.elim0
  | _ + 1, w, ⟨0, _⟩ => dec (padFalse E w)
  | k + 1, w, ⟨i + 1, hi⟩ => decTuple E dec k (w.drop E) ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Data stored at cell index `j` of the block-table representation of a configuration of `M`. -/
structure BlockData (M : TM) where
  isZero : Bool
  state : Fin M.Q
  headSym : Fin M.k → Fin M.G
  leftSym : Fin M.k → Fin M.G
  rightSym : Fin M.k → Fin M.G

/-- Fixed bit-width of one block for machine `M`. -/
def blockWidth (M : TM) : Nat :=
  1 + M.Q + (M.k * M.G + (M.k * M.G + M.k * M.G))

/-- The all-blank block (for out-of-bounds cell index `j > 0`). -/
def blankBlock (M : TM) : BlockData M where
  isZero := false
  state := ⟨0, M.hQ⟩
  headSym := fun _ => M.blank
  leftSym := fun _ => M.blank
  rightSym := fun _ => M.blank

/-- Encode `BlockData M` into a word of length `blockWidth M`. -/
def encBlock (M : TM) (b : BlockData M) : Word :=
  [b.isZero] ++
    (encFin b.state ++
      (encTuple encFin b.headSym ++
        (encTuple encFin b.leftSym ++
          encTuple encFin b.rightSym)))

/-- Decode a word of length `blockWidth M` back into `BlockData M`. -/
def decBlock (M : TM) (w : Word) : BlockData M :=
  let hG0 : 0 < M.G := by have := M.hG; omega
  let w1 := w.drop 1
  let w2 := w1.drop M.Q
  let w3 := w2.drop (M.k * M.G)
  let w4 := w3.drop (M.k * M.G)
  { isZero := w.headD false
    state := decFin M.hQ (padFalse M.Q w1)
    headSym := decTuple M.G (decFin hG0) M.k (padFalse (M.k * M.G) w2)
    leftSym := decTuple M.G (decFin hG0) M.k (padFalse (M.k * M.G) w3)
    rightSym := decTuple M.G (decFin hG0) M.k (padFalse (M.k * M.G) w4) }

/-- Extract the `j`-th `BlockData M` from a configuration `c : Cfg M.k M.Q M.G`. -/
def cfgBlock (M : TM) (c : Cfg M.k M.Q M.G) (j : Nat) : BlockData M :=
  if j = 0 then
    { isZero := true
      state := c.state
      headSym := fun i => (c.tapes i).head
      leftSym := fun i => (c.tapes i).left.getD 0 M.blank
      rightSym := fun i => (c.tapes i).right.getD 0 M.blank }
  else
    { isZero := false
      state := ⟨0, M.hQ⟩
      headSym := fun _ => M.blank
      leftSym := fun i => (c.tapes i).left.getD j M.blank
      rightSym := fun i => (c.tapes i).right.getD j M.blank }

/-- Encode a TM configuration `c` across `N` blocks of width `blockWidth M`. -/
def encCfg (M : TM) (N : Nat) (c : Cfg M.k M.Q M.G) : Word :=
  tableOf (fun j => encBlock M (cfgBlock M c j)) N

/-! ## 3. BC Programs for Initial Configuration, Transition Step, Run, and Output -/

/-- Branch on `y.head? : Option Bool` of safe argument `0`. -/
def branchHead {m : Nat} (K : Option Bool → Fn 0 m) : Fn 0 (m + 1) :=
  .comp .cond Fin.elim0
    (vec4 (.projS ⟨0, Nat.zero_lt_succ m⟩)
          (shiftSafe (K none))
          (shiftSafe (K (some false)))
          (shiftSafe (K (some true))))

/-- Construct `cfgBlock M (M.init x) j` from `isZero = (j = 0)` and `(x.drop j).head?`, `(x.drop j).tail.head?`. -/
def initBlockFromDrop (M : TM) (isZero : Bool) (h0 r0 : Option Bool) : BlockData M :=
  let optSym : Option Bool → Fin M.G
    | none => M.blank
    | some b => M.bitSym b
  if isZero then
    { isZero := true
      state := ⟨0, M.hQ⟩
      headSym := fun i => if i.val = 0 then optSym h0 else M.blank
      leftSym := fun _ => M.blank
      rightSym := fun i => if i.val = 0 then optSym r0 else M.blank }
  else
    { isZero := false
      state := ⟨0, M.hQ⟩
      headSym := fun _ => M.blank
      leftSym := fun _ => M.blank
      rightSym := fun i => if i.val = 0 then optSym r0 else M.blank }

def initBlockBranch (M : TM) (isZero : Bool) : Fn 0 3 :=
  branchHead (fun h0 =>
    branchHead (fun r0 =>
      prependConst (encBlock M (initBlockFromDrop M isZero h0 r0))))

def initStepBC (M : TM) : Fn 1 2 :=
  let yDrop : Fn 1 2 :=
    .comp (dropBlock 1) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 (.projS ⟨1, by decide⟩))
  let yTail : Fn 1 2 :=
    .comp .pred Fin.elim0 (vec1 yDrop)
  let branchTrue : Fn 1 2 :=
    .comp (initBlockBranch M true) Fin.elim0 (vec3 yDrop yTail (.projS ⟨0, by decide⟩))
  let branchFalse : Fn 1 2 :=
    .comp (initBlockBranch M false) Fin.elim0 (vec3 yDrop yTail (.projS ⟨0, by decide⟩))
  .comp .cond Fin.elim0 (vec4 (.projS ⟨0, by decide⟩) branchTrue branchFalse branchFalse)

/-- BC program `initCfgBC M : Fn 1 1` computing `encCfg M W.length (M.init x)`
    on normal clock `[W]` and safe input `[x]`. -/
def initCfgBC (M : TM) : Fn 1 1 :=
  let buildRev : Fn 1 1 := .srec constZero (initStepBC M) (initStepBC M)
  .comp (revBlocks (blockWidth M))
    (vec1 (.projN ⟨0, Nat.zero_lt_one⟩))
    (vec1 buildRev)

/-- One transition of `M`, returning `c` unchanged if `M` has already halted (`M.step c = none`). -/
def TM.stepOrSelf (M : TM) (c : Cfg M.k M.Q M.G) : Cfg M.k M.Q M.G :=
  match M.step c with
  | none => c
  | some c' => c'

/-- Tape-length bound: every tape in `c` has `left.length ≤ L` and `right.length ≤ L`. -/
def TM.TapeBounded (M : TM) (L : Nat) (c : Cfg M.k M.Q M.G) : Prop :=
  ∀ i : Fin M.k, (c.tapes i).left.length ≤ L ∧ (c.tapes i).right.length ≤ L

/-- Compute the new block `cfgBlock M (M.stepOrSelf c) j` from block `0` (`b0`) and the
    3-block window `(bPrev, bCur, bNext)` around `j`. -/
def nextBlockData (M : TM) (b0 bPrev bCur bNext : BlockData M) : BlockData M :=
  match M.δ b0.state b0.headSym with
  | none => bCur
  | some (q', w, d) =>
    if bCur.isZero then
      { isZero := true
        state := q'
        headSym := fun i =>
          match d i with
          | .L => bCur.leftSym i
          | .R => bCur.rightSym i
          | .S => w i
        leftSym := fun i =>
          match d i with
          | .L => bNext.leftSym i
          | .R => w i
          | .S => bCur.leftSym i
        rightSym := fun i =>
          match d i with
          | .L => w i
          | .R => bNext.rightSym i
          | .S => bCur.rightSym i }
    else
      { isZero := false
        state := ⟨0, M.hQ⟩
        headSym := fun _ => M.blank
        leftSym := fun i =>
          match d i with
          | .L => bNext.leftSym i
          | .R => bPrev.leftSym i
          | .S => bCur.leftSym i
        rightSym := fun i =>
          match d i with
          | .L => bPrev.rightSym i
          | .R => bNext.rightSym i
          | .S => bCur.rightSym i }

def stepBlockWord (M : TM) (w0 wWin : Word) : Word :=
  let D := blockWidth M
  let b0 := decBlock M (padFalse D w0)
  let bPrev := decBlock M (padFalse D wWin)
  let bCur := decBlock M (padFalse D (wWin.drop D))
  let bNext := decBlock M (padFalse D ((wWin.drop D).drop D))
  encBlock M (nextBlockData M b0 bPrev bCur bNext)

def stepBlockBranch (M : TM) : Fn 0 3 :=
  let D := blockWidth M
  branchPrefix D (fun w0 =>
    branchPrefix (D + (D + D)) (fun wWin =>
      prependConst (stepBlockWord M w0 wWin)))

def stepCfgStepBC (M : TM) : Fn 1 2 :=
  let D := blockWidth M
  let padY : Fn 1 2 :=
    .comp (prependConst (List.replicate D false)) Fin.elim0 (vec1 (.projS ⟨1, by decide⟩))
  let wShift : Fn 1 2 :=
    .comp (dropBlock D) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 padY)
  .comp (stepBlockBranch M) Fin.elim0
    (vec3 (.projS ⟨1, by decide⟩) wShift (.projS ⟨0, by decide⟩))

/-- BC program `stepCfgBC M : Fn 1 1` simulating one transition `M.stepOrSelf` on an
    encoded configuration of `W.length` blocks. -/
def stepCfgBC (M : TM) : Fn 1 1 :=
  let buildRev : Fn 1 1 := .srec constZero (stepCfgStepBC M) (stepCfgStepBC M)
  .comp (revBlocks (blockWidth M))
    (vec1 (.projN ⟨0, Nat.zero_lt_one⟩))
    (vec1 buildRev)

/-- BC program `runCfgBC M : Fn 2 1` iterating `stepCfgBC M` for `|T|` steps on normal
    inputs `[T, W]` and safe initial configuration `[y]`. -/
def runCfgBC (M : TM) : Fn 2 1 :=
  let step : Fn 2 2 :=
    .comp (stepCfgBC M) (vec1 (.projN ⟨1, by decide⟩)) (vec1 (.projS ⟨0, by decide⟩))
  .srec (.projS ⟨0, Nat.zero_lt_one⟩) step step

def outStepWord (M : TM) (b : BlockData M) (r : Word) : Word :=
  let r1 :=
    match M.decodeBit (b.rightSym ⟨0, M.hk⟩) with
    | some bit => bit :: r
    | none => []
  if b.isZero then
    match M.decodeBit (b.headSym ⟨0, M.hk⟩) with
    | some bit0 => bit0 :: r1
    | none => []
  else
    r1

def outBlockFn (M : TM) (w : Word) : Fn 0 1 :=
  let b := decBlock M w
  if b.isZero then
    match M.decodeBit (b.headSym ⟨0, M.hk⟩), M.decodeBit (b.rightSym ⟨0, M.hk⟩) with
    | none, _ => constZero
    | some bit0, none => constWord [bit0]
    | some bit0, some bit1 => prependConst [bit0, bit1]
  else
    match M.decodeBit (b.rightSym ⟨0, M.hk⟩) with
    | none => constZero
    | some bit => prependConst [bit]

def outCfgStepBC (M : TM) : Fn 1 2 :=
  let D := blockWidth M
  let wBlock : Fn 1 2 :=
    .comp (dropBlock D) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 (.projS ⟨1, by decide⟩))
  .comp (branchPrefix D (outBlockFn M)) Fin.elim0
    (vec2 wBlock (.projS ⟨0, by decide⟩))

/-- BC program `outputCfgBC M : Fn 1 1` extracting `M.output c` from `encCfg M W.length c`. -/
def outputCfgBC (M : TM) : Fn 1 1 :=
  let yRev : Fn 1 1 :=
    .comp (revBlocks (blockWidth M))
      (vec1 (.projN ⟨0, Nat.zero_lt_one⟩))
      (vec1 (.projS ⟨0, Nat.zero_lt_one⟩))
  let extract : Fn 1 1 := .srec constZero (outCfgStepBC M) (outCfgStepBC M)
  .comp extract (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 yRev)

/-- Full BC simulator `simTM M p : Fn 1 0` running `M : TM` for `p(|x|)` transitions on `[x], []`. -/
def simTM (M : TM) (p : Poly) : Fn 1 0 :=
  let clockPoly : Poly := .add (.add .var p) (.const 1)
  let wClock : Fn 1 0 := polyWord clockPoly
  let tSteps : Fn 1 0 := polyWord p
  let initCfg : Fn 1 0 := .comp (initCfgBC M) (vec1 wClock) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩))
  let finalCfg : Fn 1 0 := .comp (runCfgBC M) (vec2 tSteps wClock) (vec1 initCfg)
  .comp (outputCfgBC M) (vec1 wClock) (vec1 finalCfg)

end BC1992


