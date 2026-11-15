-- Prove2me | Definitions.Def_CatalyticTreeEval_WorkLanes
-- name    : CatalyticTreeEval_WorkLanes
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T06:37:48.219209+00:00
-- url     : https://prove2.me/theorems/23f6bd05-4a5b-411e-b900-4eccfb4d483b
-- title:
--   Finite native work-lane compiler with an origin-marker track
-- statement:
--   Fix a native source machine, K work lanes and a lane index j<K. Store logical cell p at physical address b+(K+1)p+j, and use the extra column as a marker that is true only at logical origin. The compiled machine has finite outward, inward and movement-control states. It reads the origin marker by a fixed shuttle, performs one source instruction, and pads the physical work movement to stride K+1, respecting the source left clamp. The definitions specify the actual native table, physical/source configuration correspondence and constant macro duration $$L=2(K-j)+1+K.$$ No run-time width or arithmetic oracle is part of the finite control.
-- source:
--   Infrastructure for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, uniform native machine construction and work-bank arithmetic.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

/-- Outward/inward origin-marker shuttles and the padded source work move.
Every component of the control state has a finite type. -/
abbrev Control (A : Machine) (lanes : ℕ) :=
  (Fin A.states × Fin (lanes + 1)) ⊕
    ((Fin A.states × Bool × Fin (lanes + 1)) ⊕
      (Option (Fin A.states) × Option Bool × Fin (lanes + 1)))

def outward (A : Machine) (lanes : ℕ) (q : Fin A.states) (r : Fin (lanes + 1)) :
    Control A lanes := .inl (q, r)

def inward (A : Machine) (lanes : ℕ) (q : Fin A.states) (origin : Bool)
    (r : Fin (lanes + 1)) : Control A lanes := .inr (.inl (q, origin, r))

def pending (A : Machine) (lanes : ℕ) (next : Option (Fin A.states))
    (direction : Option Bool) (r : Fin (lanes + 1)) : Control A lanes :=
  .inr (.inr (next, direction, r))

noncomputable def encode (A : Machine) (lanes : ℕ) :
    Control A lanes ≃ Fin (Fintype.card (Control A lanes)) := Fintype.equivFin _

def distance {lanes : ℕ} (lane : Fin lanes) : ℕ := lanes - lane.val

def counter {lanes : ℕ} (lane : Fin lanes) : Fin (lanes + 1) :=
  ⟨distance lane, by dsimp [distance]; omega⟩

def predecessor {lanes : ℕ} (r : Fin (lanes + 1)) : Fin (lanes + 1) :=
  ⟨r.val - 1, by omega⟩

def remaining {lanes : ℕ} (r : Fin (lanes + 1)) (steps : ℕ) : Fin (lanes + 1) :=
  ⟨r.val - steps, by omega⟩

def moveCode : Move → Option Bool
  | .left => some false
  | .stay => none
  | .right => some true

def decodeMove : Option Bool → Move
  | some false => .left
  | none => .stay
  | some true => .right

def drift (direction : Option Bool) (head steps : ℕ) : ℕ :=
  match direction with
  | some false => head - steps
  | none => head
  | some true => head + steps

/-- The source's left origin clamp is driven by the physical origin track. -/
def clippedMove (origin : Bool) : Move → Move
  | .left => if origin then .stay else .left
  | .stay => .stay
  | .right => .right

def resumed (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (next : Option (Fin A.states)) : Option (Control A lanes) :=
  next.map fun q => outward A lanes q (counter lane)

def pendingNext (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (next : Option (Fin A.states)) (direction : Option Bool) (r : Fin (lanes + 1)) :
    Option (Control A lanes) :=
  if r.val ≤ 1 then resumed A lanes lane next
  else some (pending A lanes next direction (predecessor r))

def quietInstruction (A : Machine) (lanes : ℕ)
    (next : Option (Fin (Fintype.card (Control A lanes)))) (work : Bool) (move : Move) :
    Instruction (Fintype.card (Control A lanes)) where
  next := next
  workWrite := work
  catalystWrite := none
  inputMove := .stay
  workMove := move
  catalystMove := .stay
  emit := none

noncomputable def applyInstruction (A : Machine) (lanes : ℕ)
    (a : Instruction A.states) (origin : Bool) :
    Instruction (Fintype.card (Control A lanes)) :=
  { a with
    next := some (encode A lanes (pending A lanes a.next
      (moveCode (clippedMove origin a.workMove)) ⟨lanes, by omega⟩))
    workMove := clippedMove origin a.workMove }

noncomputable def instruction (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (q : Control A lanes) (input : Option Bool) (work : Bool) (catalyst : Option Bool)
    (inputOrigin catalystOrigin : Bool) : Instruction (Fintype.card (Control A lanes)) :=
  match q with
  | .inl (q, r) =>
    if r.val = 0 then
      quietInstruction A lanes
        (some (encode A lanes (inward A lanes q work (predecessor (counter lane))))) work .left
    else
      quietInstruction A lanes
        (some (encode A lanes (outward A lanes q (predecessor r)))) work .right
  | .inr (.inl (q, origin, r)) =>
    if r.val = 0 then
      applyInstruction A lanes (A.table q input work catalyst inputOrigin origin catalystOrigin) origin
    else
      quietInstruction A lanes
        (some (encode A lanes (inward A lanes q origin (predecessor r)))) work .left
  | .inr (.inr (next, direction, r)) =>
    quietInstruction A lanes
      ((pendingNext A lanes lane next direction r).map (encode A lanes)) work
      (if r.val = 0 then .stay else decodeMove direction)

/-- A finite binary machine operating one logical work lane. The last physical
column is an immutable origin marker. Source work moves are padded so every
simulated live transition has a constant number of native steps. -/
noncomputable def machine (A : Machine) (lanes : ℕ) (lane : Fin lanes) : Machine where
  states := Fintype.card (Control A lanes)
  start := encode A lanes (outward A lanes A.start (counter lane))
  table q input work catalyst io _ co :=
    instruction A lanes lane ((encode A lanes).symm q) input work catalyst io co

def address {lanes : ℕ} (lane : Fin lanes) (base position : ℕ) : ℕ :=
  base + (lanes + 1) * position + lane.val

def markerAddress (lanes base position : ℕ) : ℕ := base + (lanes + 1) * position + lanes

def OriginTrack (lanes base : ℕ) (physical : ℕ → Bool) : Prop :=
  ∀ p, physical (markerAddress lanes base p) = decide (p = 0)

def Matches {lanes : ℕ} (lane : Fin lanes) (base : ℕ)
    (source physical : ℕ → Bool) : Prop :=
  ∀ p, physical (address lane base p) = source p

/-- Proof-level descriptions of a source transition, never arguments to the
compiled transition table. -/
def sourceInstruction (A : Machine) (input : List Bool) (c : Configuration A)
    (q : Fin A.states) : Instruction A.states :=
  A.table q (if c.inputHead = 0 then none else input[c.inputHead - 1]?)
    (c.work c.workHead) c.catalyst[c.catalystHead]?
    (c.inputHead == 0) (c.workHead == 0) (c.catalystHead == 0)

def Legal (A : Machine) (input : List Bool) (c : Configuration A) (a : Instruction A.states) : Prop :=
  a.inputMove.apply c.inputHead ≤ input.length + 1 ∧
    a.catalystMove.apply c.catalystHead ≤ c.catalyst.length ∧
    (a.catalystWrite.isSome → c.catalystHead < c.catalyst.length)

instance (A : Machine) (input : List Bool) (c : Configuration A) (a : Instruction A.states) :
    Decidable (Legal A input c a) := by
  unfold Legal
  infer_instance

def sourceResult (A : Machine) (c : Configuration A) (a : Instruction A.states) : Configuration A :=
  ⟨a.next, a.inputMove.apply c.inputHead, a.workMove.apply c.workHead,
    a.catalystMove.apply c.catalystHead, Function.update c.work c.workHead a.workWrite,
    (match a.catalystWrite with | none => c.catalyst | some b => c.catalyst.set c.catalystHead b),
    c.output ++ a.emit.toList⟩

noncomputable def snapshot (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (source : Configuration A) (physical : ℕ → Bool)
    (control : Option (Control A lanes)) (head : ℕ) : Configuration (machine A lanes lane) :=
  { source with state := control.map (encode A lanes), workHead := head, work := physical }

noncomputable def embed (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (source : Configuration A) (physical : ℕ → Bool) : Configuration (machine A lanes lane) :=
  snapshot A lanes lane source physical
    (source.state.map fun q => outward A lanes q (counter lane))
    (address lane base source.workHead)

def macroTime {lanes : ℕ} (lane : Fin lanes) : ℕ := 2 * distance lane + 1 + lanes

end CatalyticTreeEval.Contracts.WorkLanes


