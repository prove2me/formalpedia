-- Prove2me | Definitions.Def_TetrisHard_Rows_Game
-- name    : TetrisHard_Rows_Game
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T22:49:59.549476+00:00
-- url     : https://prove2.me/theorems/68ea3e72-0f6b-4a90-b093-c51297e3f93b
-- title:
--   Offline Tetris pieces, boards, local rotations and trajectories
-- statement:
--   A board is a finite Boolean rectangle with rows ordered from bottom to top. Legal initial boards have positive dimensions, no full row, and no empty row below any occupied cell. Integer coordinates outside the rectangle are occupied sentinels. Seven tetrominoes have exactly the centers and base footprints of Figures 1–2; square footprints are rotation invariant. A state contains type, orientation, position and fixed flag. The spawn column is floor(width/2) in the source’s one-based coordinates. A local rotation rule is represented by a finite neighborhood table returning either failure or an integer displacement; successful turns update the orientation and preserve type and fixed status. Admissibility requires an empty neighborhood to permit rotation and legal rotations to avoid collisions. The instantaneous model checks the rotated footprint at unchanged center. Legal moves are rotations, one-cell horizontal slides, one-row drops, and supported fixing. A trajectory starts at the prescribed clear spawn and ends fixed. Fixing adds cells, simultaneously removes full rows and shifts survivors downward. Reachable play prefixes use the ordered input pieces; a blocked next spawn admits no further step. Prefix scores count cleared rows and include the zero-score empty prefix. They extend without decreasing score, so they determine the same row optimum as completed play.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, §2, pp. 4–7; Figures 1–2, https://arxiv.org/abs/cs/0210020v1

import Mathlib

namespace TetrisHard.Rows

abbrev Cell := ℤ × ℤ

inductive Piece where
  | Sq | LG | RG | LS | RS | I | T
  deriving DecidableEq, Repr

/-- Offsets in Figures 1--2. The square's position is its upper-left cell. -/
def Piece.base : Piece → List Cell
  | .Sq => [(0,0), (1,0), (0,-1), (1,-1)]
  | .LG => [(0,1), (0,0), (0,-1), (-1,-1)]
  | .RG => [(0,1), (0,0), (0,-1), (1,-1)]
  | .LS => [(0,1), (0,0), (-1,0), (-1,-1)]
  | .RS => [(-1,1), (-1,0), (0,0), (0,-1)]
  | .I => [(-1,0), (0,0), (1,0), (2,0)]
  | .T => [(-1,0), (0,0), (1,0), (0,-1)]

def clockwise (z : Cell) : Cell := (z.2, -z.1)

structure PieceState where
  kind : Piece
  orientation : Fin 4
  position : Cell
  fixed : Bool
  deriving DecidableEq, Repr

def PieceState.cells (q : PieceState) : List Cell :=
  q.kind.base.map fun z =>
    let u := if q.kind = .Sq then z else clockwise^[q.orientation.val] z
    (q.position.1 + u.1, q.position.2 + u.2)

structure Board where
  height : ℕ
  width : ℕ
  cell : Fin height → Fin width → Bool

/-- Coordinates are zero-based; outside the finite rectangle is occupied. -/
def Board.occupied (B : Board) (z : Cell) : Bool :=
  if hy : 0 ≤ z.2 ∧ z.2 < B.height then
    if hx : 0 ≤ z.1 ∧ z.1 < B.width then
      B.cell ⟨z.2.toNat, by omega⟩ ⟨z.1.toNat, by omega⟩
    else true
  else true

def Board.Clear (B : Board) (q : PieceState) : Prop :=
  ∀ z ∈ q.cells, B.occupied z = false

instance (B : Board) (q : PieceState) : Decidable (B.Clear q) :=
  inferInstanceAs (Decidable (∀ z ∈ q.cells, B.occupied z = false))

def Board.Legal (B : Board) : Prop :=
  0 < B.height ∧ 0 < B.width ∧
  (∀ y, ∃ x, B.cell y x = false) ∧
  ∀ y, (∃ y' x, y.val < y'.val ∧ B.cell y' x = true) →
    ∃ x, B.cell y x = true

def spawn (B : Board) (t : Piece) : PieceState :=
  { kind := t, orientation := 0, fixed := false,
    position := ((B.width / 2 : ℕ) - (1 : ℤ),
      (B.height : ℤ) - 1 - (t.base.map Prod.snd).foldl max 0) }

def translate (q : PieceState) (dx dy : ℤ) : PieceState :=
  {q with position := (q.position.1 + dx, q.position.2 + dy)}

/-- A finite neighborhood table makes the local rule computable. A successful entry
returns a displacement; `none` leaves the state unchanged. -/
structure Rotation where
  radius : ℕ
  rule : Piece → Fin 4 → Bool → Bool →
    (Fin (2 * radius + 1) → Fin (2 * radius + 1) → Bool) → Option Cell

def Rotation.apply (R : Rotation) (B : Board) (q : PieceState) (cw : Bool) : PieceState :=
  let patch := fun y x => B.occupied
    (q.position.1 + (x.val : ℤ) - R.radius, q.position.2 + (y.val : ℤ) - R.radius)
  match R.rule q.kind q.orientation q.fixed cw patch with
  | none => q
  | some d =>
    {q with
      orientation := ⟨(q.orientation.val + if cw then 1 else 3) % 4, Nat.mod_lt _ (by decide)⟩
      position := (q.position.1 + d.1, q.position.2 + d.2)}

/-- Section 2's admissibility conditions, independent of reduction correctness. -/
def Rotation.Admissible (R : Rotation) : Prop :=
  (∀ t o f d, (R.rule t o f d (fun _ _ => false)).isSome = true) ∧
  ∀ (B : Board) q d, B.Clear q → B.Clear (R.apply B q d)

/-- Radius two contains every rotated footprint in the instantaneous model. -/
def instantaneous : Rotation where
  radius := 2
  rule := fun t o f cw patch =>
    let q : PieceState :=
      {kind := t, orientation := ⟨(o.val + if cw then 1 else 3) % 4, Nat.mod_lt _ (by decide)⟩,
       position := (0,0), fixed := f}
    if q.cells.all (fun z =>
      if hy : 0 ≤ z.2 + 2 ∧ z.2 + 2 < 5 then
        if hx : 0 ≤ z.1 + 2 ∧ z.1 + 2 < 5 then
          !patch ⟨(z.2 + 2).toNat, by omega⟩ ⟨(z.1 + 2).toNat, by omega⟩
        else false
      else false)
    then some (0,0) else none

/-- No moves start from fixed states. Illegal rotations return the same state. -/
def Move (R : Rotation) (B : Board) (q q' : PieceState) : Prop :=
  q.fixed = false ∧ B.Clear q ∧ B.Clear q' ∧
  ((∃ d, q' = R.apply B q d) ∨
    q' = translate q (-1) 0 ∨ q' = translate q 1 0 ∨ q' = translate q 0 (-1) ∨
    (q' = {q with fixed := true} ∧ ¬ B.Clear (translate q 0 (-1))))

def Trajectory (R : Rotation) (B : Board) (t : Piece) (q : PieceState) : Prop :=
  B.Clear (spawn B t) ∧
  Relation.ReflTransGen (Move R B) (spawn B t) q ∧ q.fixed = true

def Board.insert (B : Board) (q : PieceState) : Board :=
  {B with cell := fun y x => B.cell y x || decide (((x.val : ℤ), (y.val : ℤ)) ∈ q.cells)}

def Board.rows (B : Board) : List (List Bool) :=
  List.ofFn fun y => List.ofFn fun x => B.cell y x

def Board.fullCount (B : Board) : ℕ :=
  (B.rows.filter (fun r => r.all id)).length

/-- Simultaneous deletion preserves the bottom-to-top order of surviving rows. -/
def Board.compress (B : Board) : Board :=
  let survivors := B.rows.filter (fun r => !(r.all id))
  {B with cell := fun y x => (survivors.getD y.val []).getD x.val false}

def Board.settle (B : Board) (q : PieceState) : Board := (B.insert q).compress

def Board.gain (B : Board) (q : PieceState) : ℕ := (B.insert q).fullCount

structure Game where
  board : Board
  pieces : List Piece

def Game.Legal (G : Game) : Prop := G.board.Legal

/-- Reachable finite prefixes. Continuing requires the next prescribed spawn to be clear,
so a blocked spawn terminates play. Prefix scores can always be extended without decreasing. -/
inductive Play (R : Rotation) : Board → List Piece → List PieceState → Board → ℕ → Prop
  | stop (B ts) : Play R B ts [] B 0
  | step {B t ts q qs B' v} : Trajectory R B t q →
      Play R (B.settle q) ts qs B' v →
      Play R B (t :: ts) (q :: qs) B' (B.gain q + v)

def Attainable (R : Rotation) (G : Game) (v : ℕ) : Prop :=
  ∃ qs B', Play R G.board G.pieces qs B' v

def Board.Empty (B : Board) : Prop := ∀ y x, B.cell y x = false

end TetrisHard.Rows


