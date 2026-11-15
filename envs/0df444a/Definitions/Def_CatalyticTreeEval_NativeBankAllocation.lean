-- Prove2me | Definitions.Def_CatalyticTreeEval_NativeBankAllocation
-- name    : CatalyticTreeEval_NativeBankAllocation
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T10:23:27.432661+00:00
-- url     : https://prove2.me/theorems/690af5b8-aa11-4ae1-80bd-3dada5a0a1df
-- title:
--   Native counted allocation of tagged binary work banks
-- statement:
--   Fixed finite native machines for allocating tagged binary operand banks on a fixed set of work lanes. A separately encoded binary counter controls the number of columns. A single physical bookmark locates the next column; actual fixed-stride searches and origin returns shuttle between it and the counter. Seeding, counter-controlled allocation and final bookmark erasure are all explicit code. The module bundles the prerequisite finite arithmetic and composition definitions; the exact execution, framing and quadratic-time claims are subsequent proof obligations. Lane IDs are fixed at compilation; no input-dependent count, width or address occurs in the finite control.
-- source:
--   Native machine infrastructure for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, shared arithmetic and charged workspace initialization.

import Definitions.Def_CatalyticTreeEval_MachineContracts

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_BankColumnInitialize -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BankColumnInitialize

open CatalyticMatching.General

def steps (lanes : ℕ) : ℕ := 3 * (lanes + 1)

/-- The selected lane set is fixed at compilation. The origin column is never
selected; counter/bookmark lanes are omitted by the caller's fixed lane set. -/
def literal (lanes : ℕ) (selected : Finset (Fin lanes)) (phase : ℕ) : Option Bool :=
  if h : phase % (lanes + 1) < lanes then
    if (⟨phase % (lanes + 1), h⟩ : Fin lanes) ∈ selected then
      some (decide (phase < lanes + 1))
    else none
  else none

/-- Initialize one tag/A/B column across a fixed collection of operand lanes.
No input-dependent width, row index or memory address is supplied to the table. -/
def machine (lanes : ℕ) (selected : Finset (Fin lanes)) : Main.Machine where
  states := steps lanes
  start := ⟨0, by dsimp [steps]; omega⟩
  table q _ work _ _ _ _ :=
    { next := if h : q.val + 1 < steps lanes then some ⟨q.val + 1, h⟩ else none
      workWrite := (literal lanes selected q.val).getD work
      catalystWrite := none
      inputMove := .stay
      workMove := .right
      catalystMove := .stay
      emit := none }

def prefixWork (lanes : ℕ) (selected : Finset (Fin lanes))
    (work : ℕ → Bool) (start elapsed : ℕ) (p : ℕ) : Bool :=
  if start ≤ p ∧ p < start + elapsed then
    (literal lanes selected (p - start)).getD (work p)
  else work p

def snapshot (lanes : ℕ) (selected : Finset (Fin lanes))
    (c : Config (machine lanes selected)) (elapsed : ℕ) : Config (machine lanes selected) :=
  { c with
    state := if h : elapsed < steps lanes then some ⟨elapsed, h⟩ else none
    workHead := c.workHead + elapsed
    work := prefixWork lanes selected c.work c.workHead elapsed }

def footprint (lanes : ℕ) (selected : Finset (Fin lanes)) (start : ℕ) : Footprint :=
  ⟨{p | start ≤ p ∧ p < start + steps lanes ∧
    (literal lanes selected (p - start)).isSome}, ∅⟩

end CatalyticTreeEval.Contracts.BankColumnInitialize

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeLiteral -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeLiteral

open CatalyticMatching.General

/-- A finite code template. `moves` is a compile-time constant, not an input
parameter supplied to an oracle. It moves the work head, then performs one
halting literal-write transition. Input/catalyst/output are preserved. -/
def machine (direction : Move) (moves : ℕ) (literal : Option Bool) : Main.Machine where
  states := moves + 1
  start := ⟨0, by omega⟩
  table q _ work _ _ _ _ :=
    if h : q.val < moves then
      { next := some ⟨q.val + 1, by omega⟩
        workWrite := work
        catalystWrite := none
        inputMove := .stay
        workMove := direction
        catalystMove := .stay
        emit := none }
    else
      { next := none
        workWrite := literal.getD work
        catalystWrite := none
        inputMove := .stay
        workMove := .stay
        catalystMove := .stay
        emit := none }

def position (direction : Move) (head : ℕ) : ℕ → ℕ
  | 0 => head
  | n + 1 => direction.apply (position direction head n)

def live (direction : Move) (moves : ℕ) (literal : Option Bool)
    (c : Config (machine direction moves literal)) (u : ℕ) (hu : u ≤ moves) :
    Config (machine direction moves literal) :=
  { c with
    state := some ⟨u, by dsimp [machine]; omega⟩
    workHead := position direction c.workHead u }

def finished (direction : Move) (moves : ℕ) (literal : Option Bool)
    (c : Config (machine direction moves literal)) : Config (machine direction moves literal) :=
  { c with
    state := none
    workHead := position direction c.workHead moves
    work := Function.update c.work (position direction c.workHead moves)
      (literal.getD (c.work (position direction c.workHead moves))) }

end CatalyticTreeEval.Contracts.NativeLiteral

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeMarkerSeek -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeMarkerSeek

open CatalyticMatching.General

/-- A fixed-stride marker search. Only phase zero tests the scanned work bit;
the remaining phases move to the next cell of the chosen marker track. -/
def machine (direction : Move) (padding : ℕ) : Main.Machine where
  states := padding + 1
  start := ⟨0, by omega⟩
  table q _ work _ _ _ _ :=
    if q.val = 0 ∧ work = true then
      { next := none, workWrite := work, catalystWrite := none,
        inputMove := .stay, workMove := .stay, catalystMove := .stay, emit := none }
    else
      { next := some ⟨(q.val + 1) % (padding + 1), Nat.mod_lt _ (by omega)⟩,
        workWrite := work, catalystWrite := none,
        inputMove := .stay, workMove := direction, catalystMove := .stay, emit := none }

def cursor (direction : Move) (padding : ℕ) (c : Config (machine direction padding))
    (u : ℕ) : Config (machine direction padding) :=
  { c with
    state := some ⟨u % (padding + 1), Nat.mod_lt _ (by omega)⟩
    workHead := NativeLiteral.position direction c.workHead u }

def finished (direction : Move) (padding : ℕ) (c : Config (machine direction padding))
    (rows : ℕ) : Config (machine direction padding) :=
  { c with
    state := none
    workHead := NativeLiteral.position direction c.workHead (rows * (padding + 1)) }

end CatalyticTreeEval.Contracts.NativeMarkerSeek

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_WorkLanes -/

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

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_ShiftAppend -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.ShiftAppend

open CatalyticMatching.General

def marker (carry : Bool) : Fin 6 := ⟨if carry then 1 else 0, by cases carry <;> decide⟩
def writeA (carry : Bool) : Fin 6 := ⟨if carry then 3 else 2, by cases carry <;> decide⟩
def skipB (carry : Bool) : Fin 6 := ⟨if carry then 5 else 4, by cases carry <;> decide⟩

def sumBit (carry _a _b : Bool) : Bool := carry
def carryBit (_carry a _b : Bool) : Bool := a

def markerInstruction (carry bit : Bool) : Instruction 6 where
  next := if bit then some (writeA carry) else none
  workWrite := if bit then bit else carry
  catalystWrite := none
  inputMove := .stay
  workMove := if bit then .right else .stay
  catalystMove := .stay
  emit := none

def writeAInstruction (carry bit : Bool) : Instruction 6 where
  next := some (skipB bit)
  workWrite := carry
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

def skipBInstruction (carry bit : Bool) : Instruction 6 where
  next := some (marker carry)
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

/-- Scan tagged columns `true,A,B`, shift A left one bit, and append the initial
carry at its least significant end. Physical B bits are preserved. Exactly three
transitions process each column, followed by the final carry-cell write. -/
def machine : Main.Machine where
  states := 6
  start := marker false
  table q _ bit _ _ _ _ :=
    match q.val with
    | 0 => markerInstruction false bit
    | 1 => markerInstruction true bit
    | 2 => writeAInstruction false bit
    | 3 => writeAInstruction true bit
    | 4 => skipBInstruction false bit
    | _ => skipBInstruction true bit

def cursor (c : Config machine) (head : ℕ) (q : Option (Fin 6)) : Config machine :=
  { c with state := q, workHead := head }

def writeSum (c : Config machine) (head : ℕ) (sum : Bool) : Config machine :=
  { c with work := Function.update c.work (head + 1) sum }

end CatalyticTreeEval.Contracts.ShiftAppend

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_ShiftAppendBank -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.ShiftAppend

def carryAt (a b : ℕ → Bool) (initial : Bool) : ℕ → Bool
  | 0 => initial
  | n + 1 => carryBit (carryAt a b initial n) (a n) (b n)

def sumAt (a b : ℕ → Bool) (initial : Bool) (n : ℕ) : Bool :=
  sumBit (carryAt a b initial n) (a n) (b n)

def bankContents (work : ℕ → Bool) (r width : ℕ) (a b : ℕ → Bool) : Prop :=
  work (r + 3 * width) = false ∧
  ∀ i < width, work (r + 3 * i) = true ∧
    work (r + 3 * i + 1) = a i ∧ work (r + 3 * i + 2) = b i

/-- Replace only the sum slots in the first `processed` columns. -/
def prefixWork (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool) (initial : Bool)
    (processed position : ℕ) : Bool :=
  if r ≤ position ∧ (position - r) % 3 = 1 ∧ (position - r) / 3 < processed
  then sumAt a b initial ((position - r) / 3) else work position

def finished (c : Config machine) (r width : ℕ) (a b : ℕ → Bool) (initial : Bool) :
    Config machine :=
  { c with
    state := none
    workHead := r + 3 * width
    work := Function.update (prefixWork c.work r a b initial width)
      (r + 3 * width) (carryAt a b initial width) }

def bankValue (bits : ℕ → Bool) (width : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, (bits i).toNat * 2 ^ i

end CatalyticTreeEval.Contracts.ShiftAppend

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_TaggedRewind -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.TaggedRewind

open CatalyticMatching.General

def instruction (next : Option (Fin 6)) (bit : Bool) (move : Move) : Instruction 6 where
  next := next
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := move
  catalystMove := .stay
  emit := none

/-- Rewind from a tagged-bank terminator, ignoring its possibly nonzero carry.
After the fixed false marker, return three cells right to the bank (true), or
three cells left to the caller's flag (false). No tape cell is changed. -/
def machine (toBank : Bool) : Main.Machine where
  states := 6
  start := 0
  table q _ bit _ _ _ _ :=
    match q.val with
    | 0 => instruction (some 1) bit .left
    | 1 => instruction (some 2) bit .left
    | 2 => instruction (some 3) bit .left
    | 3 => if bit then instruction (some 1) bit .left
        else instruction (some 4) bit (if toBank then .right else .left)
    | 4 => instruction (some 5) bit (if toBank then .right else .left)
    | _ => instruction none bit (if toBank then .right else .left)

def cursor {toBank : Bool} (c : Config (machine toBank)) (head : ℕ)
    (q : Option (Fin 6)) : Config (machine toBank) :=
  { c with state := q, workHead := head }

def leftCursor {toBank : Bool} (c : Config (machine toBank)) (top u : ℕ) :
    Config (machine toBank) :=
  cursor c (top - u) (some (if u = 0 then (0 : Fin 6) else
    if u % 3 = 0 then (3 : Fin 6) else if u % 3 = 1 then (1 : Fin 6) else (2 : Fin 6)))

def exitCursor {toBank : Bool} (c : Config (machine toBank)) (base u : ℕ) :
    Config (machine toBank) :=
  cursor c (if toBank then base + 3 + u else base + 3 - u)
    (if u = 0 then some (3 : Fin 6) else if u = 1 then some (4 : Fin 6)
      else if u = 2 then some (5 : Fin 6) else none)

def envelope {toBank : Bool} (c : Config (machine toBank)) (base width : ℕ) : Envelope :=
  ⟨base, base + 6 + 3 * width + 1, c.catalystHead, c.catalystHead + 1⟩

def footprint : Footprint := ⟨∅, ∅⟩

end CatalyticTreeEval.Contracts.TaggedRewind

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_SequentialMachine -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.Sequential

open CatalyticMatching.General

def leftState (A B : Machine) (q : Fin A.states) : Fin (A.states + B.states) :=
  finSumFinEquiv (Sum.inl q)

def rightState (A B : Machine) (q : Fin B.states) : Fin (A.states + B.states) :=
  finSumFinEquiv (Sum.inr q)

/-- Redirect A's halting transition to B's initial state. All tape actions and
emission remain those of A; the handoff is folded into that transition. -/
def leftInstruction (A B : Machine) (a : Instruction A.states) :
    Instruction (A.states + B.states) :=
  { a with next := some (a.next.elim (rightState A B B.start) (leftState A B)) }

def rightInstruction (A B : Machine) (a : Instruction B.states) :
    Instruction (A.states + B.states) :=
  { a with next := a.next.map (rightState A B) }

/-- Native finite-table sequential composition on the same physical tapes.
It neither initializes B's work tape nor resets any head. -/
def machine (A B : Machine) : Machine where
  states := A.states + B.states
  start := leftState A B A.start
  table q input work catalyst io wo co :=
    match finSumFinEquiv.symm q with
    | .inl qa => leftInstruction A B (A.table qa input work catalyst io wo co)
    | .inr qb => rightInstruction A B (B.table qb input work catalyst io wo co)

def leftConfig (A B : Machine) (c : Configuration A) : Configuration (machine A B) :=
  { c with state := some (c.state.elim (rightState A B B.start) (leftState A B)) }

def rightConfig (A B : Machine) (c : Configuration B) : Configuration (machine A B) :=
  { c with state := c.state.map (rightState A B) }

/-- B begins on exactly A's final tapes, heads and output. -/
def handoff (A B : Machine) (c : Configuration A) : Configuration B :=
  { c with state := some B.start }

end CatalyticTreeEval.Contracts.Sequential

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_BranchMachine -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.Branch

open CatalyticMatching.General

def gateState (A B : Machine) : Fin (1 + (A.states + B.states)) :=
  finSumFinEquiv (Sum.inl 0)

def leftState (A B : Machine) (q : Fin A.states) : Fin (1 + (A.states + B.states)) :=
  finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl q)))

def rightState (A B : Machine) (q : Fin B.states) : Fin (1 + (A.states + B.states)) :=
  finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr q)))

def gateInstruction (A B : Machine) (work : Bool) : Instruction (1 + (A.states + B.states)) where
  next := some (if work then leftState A B A.start else rightState A B B.start)
  workWrite := work
  catalystWrite := none
  inputMove := .stay
  workMove := .stay
  catalystMove := .stay
  emit := none

def leftInstruction (A B : Machine) (a : Instruction A.states) :
    Instruction (1 + (A.states + B.states)) :=
  { a with next := a.next.map (leftState A B) }

def rightInstruction (A B : Machine) (a : Instruction B.states) :
    Instruction (1 + (A.states + B.states)) :=
  { a with next := a.next.map (rightState A B) }

/-- One charged test of the scanned work bit selects between two fixed native
finite machines. Neither branch receives freshly initialized physical tapes. -/
def machine (A B : Machine) : Machine where
  states := 1 + (A.states + B.states)
  start := gateState A B
  table q input work catalyst io wo co :=
    match finSumFinEquiv.symm q with
    | .inl _ => gateInstruction A B work
    | .inr r =>
      match finSumFinEquiv.symm r with
      | .inl qa => leftInstruction A B (A.table qa input work catalyst io wo co)
      | .inr qb => rightInstruction A B (B.table qb input work catalyst io wo co)

def gateConfig (A B : Machine) (c : Configuration A) : Configuration (machine A B) :=
  { c with state := some (gateState A B) }

def leftConfig (A B : Machine) (c : Configuration A) : Configuration (machine A B) :=
  { c with state := c.state.map (leftState A B) }

def rightConfig (A B : Machine) (c : Configuration B) : Configuration (machine A B) :=
  { c with state := c.state.map (rightState A B) }

def startLeft (A : Machine) (c : Configuration A) : Configuration A :=
  { c with state := some A.start }

def startRight (A B : Machine) (c : Configuration A) : Configuration B :=
  { c with state := some B.start }

end CatalyticTreeEval.Contracts.Branch

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_ConsumeMSB -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.ConsumeMSB

/-- Clear the terminal carry, return across the tagged bank, and save the
selected bit in the caller's flag. The Boolean chooses finite control only. -/
def saveCarry (bit : Bool) : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .stay 0 (some false))
    (Sequential.machine (TaggedRewind.machine false)
      (NativeLiteral.machine .stay 0 (some bit)))

def carryDispatch : Main.Machine := Branch.machine (saveCarry true) (saveCarry false)

/-- Destructively consume the most significant bit of a tagged A bank. The
fixed machine shifts A left, clears its terminal carry, and returns that carry
in the caller flag. The bank's B slots and all tags are preserved. -/
def machine : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .right 6 none)
    (Sequential.machine ShiftAppend.machine carryDispatch)

end CatalyticTreeEval.Contracts.ConsumeMSB

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeLaneFlagCopy -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeLaneFlagCopy

open CatalyticMatching.General

def distance {lanes : ℕ} (source target : Fin lanes) : ℕ :=
  if source.val ≤ target.val then target.val - source.val else source.val - target.val

def forward {lanes : ℕ} (source target : Fin lanes) : Move :=
  if source.val ≤ target.val then .right else .left

def backward {lanes : ℕ} (source target : Fin lanes) : Move :=
  if source.val ≤ target.val then .left else .right

def arm {lanes : ℕ} (source target : Fin lanes) (bit : Bool) : Main.Machine :=
  Sequential.machine (NativeLiteral.machine (forward source target) (distance source target) (some bit))
    (NativeLiteral.machine (backward source target) (distance source target) none)

/-- Copy one logical flag between two fixed lanes in physical row zero and
return to the source. No origin track, input address, or variable seek occurs. -/
def machine {lanes : ℕ} (source target : Fin lanes) : Main.Machine :=
  Branch.machine (arm source target true) (arm source target false)

end CatalyticTreeEval.Contracts.NativeLaneFlagCopy

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_RippleAdder -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleAdder

open CatalyticMatching.General

def marker (carry : Bool) : Fin 14 := ⟨if carry then 1 else 0, by cases carry <;> decide⟩
def readA (carry : Bool) : Fin 14 := ⟨if carry then 3 else 2, by cases carry <;> decide⟩
def readB (carry a : Bool) : Fin 14 :=
  ⟨4 + 2 * carry.toNat + a.toNat, by cases carry <;> cases a <;> decide⟩
def writeA (carry sum : Bool) : Fin 14 :=
  ⟨8 + 2 * carry.toNat + sum.toNat, by cases carry <;> cases sum <;> decide⟩
def skipB (carry : Bool) : Fin 14 := ⟨if carry then 13 else 12, by cases carry <;> decide⟩

def sumBit (carry a b : Bool) : Bool := (carry ^^ a) ^^ b
def carryBit (carry a b : Bool) : Bool := (carry && a) || (carry && b) || (a && b)

def markerInstruction (carry bit : Bool) : Instruction 14 where
  next := if bit then some (readA carry) else none
  workWrite := if bit then bit else carry
  catalystWrite := none
  inputMove := .stay
  workMove := if bit then .right else .stay
  catalystMove := .stay
  emit := none

def readAInstruction (carry bit : Bool) : Instruction 14 where
  next := some (readB carry bit)
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

def readBInstruction (carry a bit : Bool) : Instruction 14 where
  next := some (writeA (carryBit carry a bit) (sumBit carry a bit))
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .left
  catalystMove := .stay
  emit := none

def writeAInstruction (carry sum : Bool) : Instruction 14 where
  next := some (skipB carry)
  workWrite := sum
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

def skipBInstruction (carry bit : Bool) : Instruction 14 where
  next := some (marker carry)
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

/-- A native 14-state ripple adder on work columns `true,a,b`, followed by one
false sentinel. Each column takes five transitions, preserves `b`, and replaces
`a` by its sum bit. The final transition writes the carry into the sentinel and
halts there. Input, catalyst, and output do not change. -/
def machine : Main.Machine where
  states := 14
  start := marker false
  table q _ bit _ _ _ _ :=
    match q.val with
    | 0 => markerInstruction false bit
    | 1 => markerInstruction true bit
    | 2 => readAInstruction false bit
    | 3 => readAInstruction true bit
    | 4 => readBInstruction false false bit
    | 5 => readBInstruction false true bit
    | 6 => readBInstruction true false bit
    | 7 => readBInstruction true true bit
    | 8 => writeAInstruction false false
    | 9 => writeAInstruction false true
    | 10 => writeAInstruction true false
    | 11 => writeAInstruction true true
    | 12 => skipBInstruction false bit
    | _ => skipBInstruction true bit

def cursor (c : Config machine) (head : ℕ) (q : Option (Fin 14)) : Config machine :=
  { c with state := q, workHead := head }

def writeSum (c : Config machine) (head : ℕ) (sum : Bool) : Config machine :=
  { c with work := Function.update c.work (head + 1) sum }

end CatalyticTreeEval.Contracts.RippleAdder

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_RippleAdderBank -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleAdder

def carryAt (a b : ℕ → Bool) (initial : Bool) : ℕ → Bool
  | 0 => initial
  | n + 1 => carryBit (carryAt a b initial n) (a n) (b n)

def sumAt (a b : ℕ → Bool) (initial : Bool) (n : ℕ) : Bool :=
  sumBit (carryAt a b initial n) (a n) (b n)

def bankContents (work : ℕ → Bool) (r width : ℕ) (a b : ℕ → Bool) : Prop :=
  work (r + 3 * width) = false ∧
  ∀ i < width, work (r + 3 * i) = true ∧
    work (r + 3 * i + 1) = a i ∧ work (r + 3 * i + 2) = b i

/-- Replace only the sum slots in the first `processed` columns. -/
def prefixWork (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool) (initial : Bool)
    (processed position : ℕ) : Bool :=
  if r ≤ position ∧ (position - r) % 3 = 1 ∧ (position - r) / 3 < processed
  then sumAt a b initial ((position - r) / 3) else work position

def finished (c : Config machine) (r width : ℕ) (a b : ℕ → Bool) (initial : Bool) :
    Config machine :=
  { c with
    state := none
    workHead := r + 3 * width
    work := Function.update (prefixWork c.work r a b initial width)
      (r + 3 * width) (carryAt a b initial width) }

def bankValue (bits : ℕ → Bool) (width : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, (bits i).toNat * 2 ^ i

end CatalyticTreeEval.Contracts.RippleAdder

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_RippleSubtractor -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleSubtractor

open CatalyticMatching.General

def marker (carry : Bool) : Fin 14 := ⟨if carry then 1 else 0, by cases carry <;> decide⟩
def readA (carry : Bool) : Fin 14 := ⟨if carry then 3 else 2, by cases carry <;> decide⟩
def readB (carry a : Bool) : Fin 14 :=
  ⟨4 + 2 * carry.toNat + a.toNat, by cases carry <;> cases a <;> decide⟩
def writeA (carry sum : Bool) : Fin 14 :=
  ⟨8 + 2 * carry.toNat + sum.toNat, by cases carry <;> cases sum <;> decide⟩
def skipB (carry : Bool) : Fin 14 := ⟨if carry then 13 else 12, by cases carry <;> decide⟩

def sumBit (carry a b : Bool) : Bool := (carry ^^ a) ^^ (!b)
def carryBit (carry a b : Bool) : Bool := (carry && a) || (carry && !b) || (a && !b)

def markerInstruction (carry bit : Bool) : Instruction 14 where
  next := if bit then some (readA carry) else none
  workWrite := if bit then bit else carry
  catalystWrite := none
  inputMove := .stay
  workMove := if bit then .right else .stay
  catalystMove := .stay
  emit := none

def readAInstruction (carry bit : Bool) : Instruction 14 where
  next := some (readB carry bit)
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

def readBInstruction (carry a bit : Bool) : Instruction 14 where
  next := some (writeA (carryBit carry a bit) (sumBit carry a bit))
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .left
  catalystMove := .stay
  emit := none

def writeAInstruction (carry sum : Bool) : Instruction 14 where
  next := some (skipB carry)
  workWrite := sum
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

def skipBInstruction (carry bit : Bool) : Instruction 14 where
  next := some (marker carry)
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

/-- A native 14-state ripple subtractor on work columns `true,a,b`, followed by one
false sentinel. Each column takes five transitions, preserves `b`, and replaces
`a` by its difference bit. With initial carry true this computes
`a-b` modulo the bank width, and the final carry means no borrow. The final transition writes the carry into the sentinel and
halts there. Input, catalyst, and output do not change. -/
def machine : Main.Machine where
  states := 14
  start := marker true
  table q _ bit _ _ _ _ :=
    match q.val with
    | 0 => markerInstruction false bit
    | 1 => markerInstruction true bit
    | 2 => readAInstruction false bit
    | 3 => readAInstruction true bit
    | 4 => readBInstruction false false bit
    | 5 => readBInstruction false true bit
    | 6 => readBInstruction true false bit
    | 7 => readBInstruction true true bit
    | 8 => writeAInstruction false false
    | 9 => writeAInstruction false true
    | 10 => writeAInstruction true false
    | 11 => writeAInstruction true true
    | 12 => skipBInstruction false bit
    | _ => skipBInstruction true bit

def cursor (c : Config machine) (head : ℕ) (q : Option (Fin 14)) : Config machine :=
  { c with state := q, workHead := head }

def writeSum (c : Config machine) (head : ℕ) (sum : Bool) : Config machine :=
  { c with work := Function.update c.work (head + 1) sum }

end CatalyticTreeEval.Contracts.RippleSubtractor

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_RippleSubtractorBank -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleSubtractor

def carryAt (a b : ℕ → Bool) (initial : Bool) : ℕ → Bool
  | 0 => initial
  | n + 1 => carryBit (carryAt a b initial n) (a n) (b n)

def sumAt (a b : ℕ → Bool) (initial : Bool) (n : ℕ) : Bool :=
  sumBit (carryAt a b initial n) (a n) (b n)

def bankContents (work : ℕ → Bool) (r width : ℕ) (a b : ℕ → Bool) : Prop :=
  work (r + 3 * width) = false ∧
  ∀ i < width, work (r + 3 * i) = true ∧
    work (r + 3 * i + 1) = a i ∧ work (r + 3 * i + 2) = b i

/-- Replace only the sum slots in the first `processed` columns. -/
def prefixWork (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool) (initial : Bool)
    (processed position : ℕ) : Bool :=
  if r ≤ position ∧ (position - r) % 3 = 1 ∧ (position - r) / 3 < processed
  then sumAt a b initial ((position - r) / 3) else work position

def finished (c : Config machine) (r width : ℕ) (a b : ℕ → Bool) (initial : Bool) :
    Config machine :=
  { c with
    state := none
    workHead := r + 3 * width
    work := Function.update (prefixWork c.work r a b initial width)
      (r + 3 * width) (carryAt a b initial width) }

def bankValue (bits : ℕ → Bool) (width : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, (bits i).toNat * 2 ^ i

end CatalyticTreeEval.Contracts.RippleSubtractor

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_RestoringRound -/

set_option autoImplicit false

namespace CatalyticTreeEval.BinaryArithmetic

open CatalyticTreeEval.Contracts

/-- Trial subtraction is accepted on nonborrow; an underflow is restored by
adding the modulus back. This matches the native terminal-carry branch. -/
def restoredBits (a b : ℕ → Bool) (width : ℕ) : ℕ → Bool :=
  if RippleSubtractor.carryAt a b true width then RippleSubtractor.sumAt a b true
  else RippleAdder.sumAt (RippleSubtractor.sumAt a b true) b false

def nextRemainderBits (a b : ℕ → Bool) (incoming : Bool) (width : ℕ) : ℕ → Bool :=
  restoredBits (ShiftAppend.sumAt a b incoming) b width

end CatalyticTreeEval.BinaryArithmetic

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_ReentryMachine -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.Reentry

open CatalyticMatching.General

/-- Select a fixed finite entry port without altering the transition table. -/
def machine (A : Machine) (entry : Fin A.states) : Machine := { A with start := entry }

def config (A : Machine) (entry : Fin A.states) (c : Configuration A) :
    Configuration (machine A entry) := { c with state := c.state }

end CatalyticTreeEval.Contracts.Reentry

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_RestoringRoundMachine -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RestoringRound

open CatalyticMatching.General

def clearCarry : Main.Machine := NativeLiteral.machine .stay 0 (some false)

/-- At a false terminal carry, rewind and add the modulus back, then normalize
the terminal carry to false. A nonborrow path only needs the final clear. -/
def restore : Main.Machine :=
  Sequential.machine (TaggedRewind.machine true)
    (Sequential.machine RippleAdder.machine clearCarry)

def acceptOrRestore : Main.Machine := Branch.machine clearCarry restore

def trial : Main.Machine := Sequential.machine RippleSubtractor.machine acceptOrRestore

/-- One native restoring-division round on an already packed tagged bank.
The only parameter is a Boolean finite entry choice; a uniform outer host can
dispatch between the two fixed machines after reading the incoming input bit. -/
def bankRound (incoming : Bool) : Main.Machine :=
  Sequential.machine (Reentry.machine ShiftAppend.machine (ShiftAppend.marker incoming))
    (Sequential.machine (TaggedRewind.machine true) trial)

/-- Return to the caller flag at `R-6` after the round. All rounds use the same
physical bank and fixed false marker at `R-3`. -/
def flagRound (incoming : Bool) : Main.Machine :=
  Sequential.machine (bankRound incoming) (TaggedRewind.machine false)

/-- A completely fixed finite machine reads the incoming bit from the caller
flag, advances six work cells onto the bank, runs the selected round, and returns
to the original flag. -/
def machine : Main.Machine :=
  Branch.machine
    (Sequential.machine (NativeLiteral.machine .right 6 none) (flagRound true))
    (Sequential.machine (NativeLiteral.machine .right 6 none) (flagRound false))

end CatalyticTreeEval.Contracts.RestoringRound

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeBankAdd -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBankAdd

def clearAndReturn : Main.Machine :=
  Sequential.machine RestoringRound.clearCarry (TaggedRewind.machine false)

/-- Add B into A in the shared flag/marker/tagged-bank ABI and return to the
flag. The terminal carry is always cleared before returning. -/
def machine : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .right 6 none)
    (Sequential.machine RippleAdder.machine clearAndReturn)

end CatalyticTreeEval.Contracts.NativeBankAdd

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeMultiplyRound -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeMultiplyRound

def addCase : Main.Machine := Sequential.machine ConsumeMSB.machine NativeBankAdd.machine

/-- One fixed Horner multiplication round: double the A accumulator, then add
the physically preserved B multiplicand exactly when the caller flag is true. -/
def machine : Main.Machine := Branch.machine addCase ConsumeMSB.machine

end CatalyticTreeEval.Contracts.NativeMultiplyRound

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_BinaryCountdown -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinaryCountdown

open CatalyticMatching.General

def entry (i : Fin 6) : Fin 30 := ⟨i.val, by omega⟩
def tag (borrow nonzero : Bool) : Fin 30 :=
  ⟨6 + 2 * borrow.toNat + nonzero.toNat, by cases borrow <;> cases nonzero <;> decide⟩
def digit (borrow nonzero : Bool) : Fin 30 :=
  ⟨10 + 2 * borrow.toNat + nonzero.toNat, by cases borrow <;> cases nonzero <;> decide⟩
def skip (borrow nonzero : Bool) : Fin 30 :=
  ⟨14 + 2 * borrow.toNat + nonzero.toNat, by cases borrow <;> cases nonzero <;> decide⟩
def rewind (nonzero : Bool) (phase : Fin 3) : Fin 30 :=
  ⟨18 + 3 * nonzero.toNat + phase.val, by cases nonzero <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩
def back (nonzero : Bool) (phase : Fin 2) : Fin 30 :=
  ⟨24 + 2 * nonzero.toNat + phase.val, by cases nonzero <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩
def writeFlag (nonzero : Bool) : Fin 30 :=
  ⟨28 + nonzero.toNat, by cases nonzero <;> decide⟩

def resultBit (borrow a : Bool) : Bool := a ^^ borrow
def nextBorrow (borrow a : Bool) : Bool := borrow && !a

def instruction (next : Option (Fin 30)) (bit : Bool) (move : Move)
    (catalystMove : Move := .stay) : Instruction 30 where
  next := next
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := move
  catalystMove := catalystMove
  emit := none

def tagInstruction (borrow nonzero bit : Bool) : Instruction 30 :=
  instruction (some (if bit then digit borrow nonzero else rewind nonzero 1)) bit
    (if bit then .right else .left)

def digitInstruction (borrow nonzero a : Bool) : Instruction 30 :=
  instruction (some (skip (nextBorrow borrow a) (nonzero || resultBit borrow a)))
    (resultBit borrow a) .right

def rewindInstruction (nonzero : Bool) (phase : Fin 3) (bit : Bool) : Instruction 30 :=
  instruction (some (if phase.val = 0 then
    if bit then rewind nonzero 1 else back nonzero 0
    else if phase.val = 1 then rewind nonzero 2 else rewind nonzero 0)) bit .left

def backInstruction (nonzero : Bool) (phase : Fin 2) (bit : Bool) : Instruction 30 :=
  instruction (some (if phase.val = 0 then back nonzero 1 else writeFlag nonzero)) bit .left

/-- A uniform native countdown on true,A,B triples. Six entry steps reach the
bank, three steps per digit decrement A and preserve B, tagged rewind returns
to the caller flag, and the last step stores whether the new A is nonzero.
The seek variant additionally moves the catalyst head right on this last step. -/
def machine (advance : Bool) : Main.Machine where
  states := 30
  start := entry 0
  table q _ bit _ _ _ _ :=
    match q.val with
    | 0 => instruction (some (entry 1)) bit .right
    | 1 => instruction (some (entry 2)) bit .right
    | 2 => instruction (some (entry 3)) bit .right
    | 3 => instruction (some (entry 4)) bit .right
    | 4 => instruction (some (entry 5)) bit .right
    | 5 => instruction (some (tag true false)) bit .right
    | 6 => tagInstruction false false bit
    | 7 => tagInstruction false true bit
    | 8 => tagInstruction true false bit
    | 9 => tagInstruction true true bit
    | 10 => digitInstruction false false bit
    | 11 => digitInstruction false true bit
    | 12 => digitInstruction true false bit
    | 13 => digitInstruction true true bit
    | 14 => instruction (some (tag false false)) bit .right
    | 15 => instruction (some (tag false true)) bit .right
    | 16 => instruction (some (tag true false)) bit .right
    | 17 => instruction (some (tag true true)) bit .right
    | 18 => rewindInstruction false 0 bit
    | 19 => rewindInstruction false 1 bit
    | 20 => rewindInstruction false 2 bit
    | 21 => rewindInstruction true 0 bit
    | 22 => rewindInstruction true 1 bit
    | 23 => rewindInstruction true 2 bit
    | 24 => backInstruction false 0 bit
    | 25 => backInstruction false 1 bit
    | 26 => backInstruction true 0 bit
    | 27 => backInstruction true 1 bit
    | 28 => instruction none false .stay (if advance then .right else .stay)
    | _ => instruction none true .stay (if advance then .right else .stay)

def cursor {advance : Bool} (c : Config (machine advance)) (head : ℕ)
    (q : Option (Fin 30)) : Config (machine advance) :=
  { c with state := q, workHead := head }

def writeAt {advance : Bool} (c : Config (machine advance)) (head : ℕ) (value : Bool) :
    Config (machine advance) := { c with work := Function.update c.work head value }

def borrowAt (a : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => nextBorrow (borrowAt a n) (a n)

def resultAt (a : ℕ → Bool) (i : ℕ) : Bool := resultBit (borrowAt a i) (a i)

def nonzeroAt (a : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => nonzeroAt a n || resultAt a n

def bankContents (work : ℕ → Bool) (base width : ℕ) (a b : ℕ → Bool) : Prop :=
  work (base + 3) = false ∧ work (base + 6 + 3 * width) = false ∧
  ∀ i < width, work (base + 6 + 3 * i) = true ∧
    work (base + 6 + 3 * i + 1) = a i ∧ work (base + 6 + 3 * i + 2) = b i

def prefixWork (work : ℕ → Bool) (base : ℕ) (a : ℕ → Bool) (processed position : ℕ) : Bool :=
  if base + 6 ≤ position ∧ (position - (base + 6)) % 3 = 1 ∧
      (position - (base + 6)) / 3 < processed
  then resultAt a ((position - (base + 6)) / 3) else work position

def bankValue (bits : ℕ → Bool) (width : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, (bits i).toNat * 2 ^ i

def finished {advance : Bool} (c : Config (machine advance)) (base width : ℕ)
    (a : ℕ → Bool) : Config (machine advance) :=
  { c with
    state := none
    workHead := base
    catalystHead := c.catalystHead + advance.toNat
    work := Function.update (prefixWork c.work base a width) base (nonzeroAt a width) }

def envelope {advance : Bool} (c : Config (machine advance)) (base width : ℕ) : Envelope :=
  ⟨base, base + 6 + 3 * width + 1, c.catalystHead, c.catalystHead + advance.toNat + 1⟩

def footprint (base width : ℕ) : Footprint :=
  ⟨{p | p = base ∨ ∃ i < width, p = base + 6 + 3 * i + 1}, ∅⟩

end CatalyticTreeEval.Contracts.BinaryCountdown

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_WhileFlag -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.WhileFlag

open CatalyticMatching.General

def gateState (A : Machine) : Fin (1 + A.states) := finSumFinEquiv (Sum.inl 0)

def bodyState (A : Machine) (q : Fin A.states) : Fin (1 + A.states) :=
  finSumFinEquiv (Sum.inr q)

/-- A controller examines only the scanned work bit. All physical data stay put. -/
def gateInstruction (A : Machine) (work : Bool) : Instruction (1 + A.states) where
  next := if work then some (bodyState A A.start) else none
  workWrite := work
  catalystWrite := none
  inputMove := .stay
  workMove := .stay
  catalystMove := .stay
  emit := none

/-- The body's first halting transition returns to the loop controller. -/
def bodyInstruction (A : Machine) (a : Instruction A.states) : Instruction (1 + A.states) :=
  { a with next := some (a.next.elim (gateState A) (bodyState A)) }

/-- A fixed finite binary while host; no input-dependent transition table is used. -/
def machine (A : Machine) : Machine where
  states := 1 + A.states
  start := gateState A
  table q input work catalyst io wo co :=
    match finSumFinEquiv.symm q with
    | .inl _ => gateInstruction A work
    | .inr qa => bodyInstruction A (A.table qa input work catalyst io wo co)

def startBody (A : Machine) (c : Configuration A) : Configuration A :=
  { c with state := some A.start }

def bodyConfig (A : Machine) (c : Configuration A) : Configuration (machine A) :=
  { c with state := some (c.state.elim (gateState A) (bodyState A)) }

def gateConfig (A : Machine) (c : Configuration A) : Configuration (machine A) :=
  { c with state := some (gateState A) }

def haltConfig (A : Machine) (c : Configuration A) : Configuration (machine A) :=
  { c with state := none }

/-- Dispatch costs one step per body call; the final false test costs one more. -/
def elapsed (time : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (1 + time i)

end CatalyticTreeEval.Contracts.WhileFlag

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeMSBFold -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeMSBFold

def moveFlag {lanes : ℕ} (fromLane toLane : Fin lanes) : Main.Machine :=
  NativeLiteral.machine (NativeLaneFlagCopy.forward fromLane toLane)
    (NativeLaneFlagCopy.distance fromLane toLane) none

/-- Enter the numerator lane, shift out its next MSB, copy that bit to the
arithmetic flag and enter the arithmetic lane. Every inter-lane move is fixed. -/
noncomputable def feed {lanes : ℕ} (counterLane sourceLane arithmeticLane : Fin lanes) : Main.Machine :=
  Sequential.machine (moveFlag counterLane sourceLane)
    (Sequential.machine (WorkLanes.machine ConsumeMSB.machine lanes sourceLane)
      (Sequential.machine (NativeLaneFlagCopy.machine sourceLane arithmeticLane)
        (moveFlag sourceLane arithmeticLane)))

/-- One real counted bank-stream iteration on three fixed lanes. All other
lanes remain available for the caller's retained operands. -/
noncomputable def bodyWith {lanes : ℕ} (counterLane sourceLane arithmeticLane : Fin lanes)
    (physicalRound : Main.Machine) : Main.Machine :=
  Sequential.machine (feed counterLane sourceLane arithmeticLane)
    (Sequential.machine physicalRound
      (Sequential.machine (moveFlag arithmeticLane counterLane)
        (WorkLanes.machine (BinaryCountdown.machine false) lanes counterLane)))

noncomputable def body {lanes : ℕ} (counterLane sourceLane arithmeticLane : Fin lanes)
    (round : Main.Machine) : Main.Machine :=
  bodyWith counterLane sourceLane arithmeticLane (WorkLanes.machine round lanes arithmeticLane)

/-- The physical callback permits a quotient-bit accumulator or a larger
native arithmetic circuit after each input bit. It is a fixed finite machine,
entered and returned at the arithmetic flag; its contracts remain obligatory. -/
noncomputable def machineWith {lanes : ℕ} (counterLane sourceLane arithmeticLane : Fin lanes)
    (physicalRound : Main.Machine) : Main.Machine :=
  WhileFlag.machine (bodyWith counterLane sourceLane arithmeticLane physicalRound)

/-- A computed-bank MSB fold: its loop test is the countdown's actual new-value
nonzero flag. Correctness and lifted native contracts are proved separately. -/
noncomputable def machine {lanes : ℕ} (counterLane sourceLane arithmeticLane : Fin lanes)
    (round : Main.Machine) : Main.Machine := WhileFlag.machine (body counterLane sourceLane arithmeticLane round)

noncomputable def remainder {lanes : ℕ} (counterLane sourceLane arithmeticLane : Fin lanes) : Main.Machine :=
  machine counterLane sourceLane arithmeticLane RestoringRound.machine
noncomputable def multiply {lanes : ℕ} (counterLane sourceLane arithmeticLane : Fin lanes) : Main.Machine :=
  machine counterLane sourceLane arithmeticLane NativeMultiplyRound.machine

end CatalyticTreeEval.Contracts.NativeMSBFold

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeBankAllocate -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBankAllocate

/-- All lane IDs and selected banks are fixed before the input. The variable
allocation length is represented by the actual binary counter, never by states. -/
def toBookmark {lanes : ℕ} (counter bookmark : Fin lanes) : Main.Machine :=
  NativeMSBFold.moveFlag counter bookmark

def findBookmark (lanes : ℕ) : Main.Machine := NativeMarkerSeek.machine .right lanes
def clearBookmark : Main.Machine := NativeLiteral.machine .stay 0 (some false)
def columnStart {lanes : ℕ} (bookmark : Fin lanes) : Main.Machine :=
  NativeLiteral.machine .left bookmark.val none
def markNext {lanes : ℕ} (bookmark : Fin lanes) : Main.Machine :=
  NativeLiteral.machine .right bookmark.val (some true)
def originStart {lanes : ℕ} (bookmark : Fin lanes) : Main.Machine :=
  NativeLiteral.machine .right (lanes - bookmark.val) none
def originHome (lanes : ℕ) : Main.Machine := NativeMarkerSeek.machine .left lanes
def counterFlag {lanes : ℕ} (counter : Fin lanes) : Main.Machine :=
  NativeLiteral.machine .left (lanes - counter.val) none

def advance {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) : Main.Machine :=
  Sequential.machine (toBookmark counter bookmark)
    (Sequential.machine (findBookmark lanes)
      (Sequential.machine clearBookmark
        (Sequential.machine (columnStart bookmark)
          (Sequential.machine (BankColumnInitialize.machine lanes selected)
            (Sequential.machine (markNext bookmark)
              (Sequential.machine (originStart bookmark)
                (Sequential.machine (originHome lanes) (counterFlag counter))))))))

noncomputable def body {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) : Main.Machine :=
  Sequential.machine (advance counter bookmark selected)
    (WorkLanes.machine (BinaryCountdown.machine false) lanes counter)

/-- Initialization of the bookmark and final bookmark cleanup are separately
charged caller obligations. This loop itself consumes the actual counter A. -/
noncomputable def machine {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) : Main.Machine :=
  WhileFlag.machine (body counter bookmark selected)

def advanceTime {lanes : ℕ} (counter bookmark : Fin lanes) (row : ℕ) : ℕ :=
  (NativeLaneFlagCopy.distance counter bookmark + 1) +
    ((row * (lanes + 1) + 1) + (1 + ((bookmark.val + 1) +
      (3 * (lanes + 1) + ((bookmark.val + 1) + ((lanes - bookmark.val + 1) +
        (((row + 3) * (lanes + 1) + 1) + (lanes - counter.val + 1))))))))

def advanceWork {lanes : ℕ} (bookmark : Fin lanes) (selected : Finset (Fin lanes))
    (base row : ℕ) (work : ℕ → Bool) : ℕ → Bool :=
  Function.update
    (BankColumnInitialize.prefixWork lanes selected
      (Function.update work (WorkLanes.address bookmark base row) false)
      (base + (lanes + 1) * row) (BankColumnInitialize.steps lanes))
    (WorkLanes.address bookmark base (row + 3)) true

def advanceFootprint (lanes base row : ℕ) : Footprint :=
  ⟨Set.Ico (base + (lanes + 1) * row) (base + (lanes + 1) * (row + 4)), ∅⟩

end CatalyticTreeEval.Contracts.NativeBankAllocate

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeBookmarkHome -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBookmarkHome

def machine {lanes : ℕ} (counter bookmark : Fin lanes) : Main.Machine :=
  Sequential.machine (NativeBankAllocate.originStart bookmark)
    (Sequential.machine (NativeBankAllocate.originHome lanes) (NativeBankAllocate.counterFlag counter))

def clear {lanes : ℕ} (counter bookmark : Fin lanes) : Main.Machine :=
  Sequential.machine NativeBankAllocate.clearBookmark (machine counter bookmark)

/-- Fixed seeding at logical row six. It is independent of the allocation count. -/
def seed {lanes : ℕ} (counter bookmark : Fin lanes) : Main.Machine :=
  Sequential.machine (NativeBankAllocate.toBookmark counter bookmark)
    (Sequential.machine (NativeLiteral.machine .right (6*(lanes+1)) (some true))
      (machine counter bookmark))

/-- Find and erase the single runtime bookmark, then return through the origin. -/
def cleanup {lanes : ℕ} (counter bookmark : Fin lanes) : Main.Machine :=
  Sequential.machine (NativeBankAllocate.toBookmark counter bookmark)
    (Sequential.machine (NativeBankAllocate.findBookmark lanes) (clear counter bookmark))

def time {lanes : ℕ} (counter bookmark : Fin lanes) (row : ℕ) : ℕ :=
  (lanes-bookmark.val+1)+((row*(lanes+1)+1)+(lanes-counter.val+1))

end CatalyticTreeEval.Contracts.NativeBookmarkHome

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeBankAllocateFull -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBankAllocateFull

/-- The complete allocator includes charged bookmark seeding and final erasure.
All lane IDs and machine tables are fixed independently of allocation count. -/
noncomputable def machine {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) : Main.Machine :=
  Sequential.machine (NativeBookmarkHome.seed counter bookmark)
    (Sequential.machine (NativeBankAllocate.machine counter bookmark selected)
      (NativeBookmarkHome.cleanup counter bookmark))

def seedTime {lanes : ℕ} (counter bookmark : Fin lanes) : ℕ :=
  (NativeLaneFlagCopy.distance counter bookmark+1)+
    ((6*(lanes+1)+1)+NativeBookmarkHome.time counter bookmark 6)

def cleanupTime {lanes : ℕ} (counter bookmark : Fin lanes) (count : ℕ) : ℕ :=
  (NativeLaneFlagCopy.distance counter bookmark+1)+
    (((6+3*count)*(lanes+1)+1)+(1+NativeBookmarkHome.time counter bookmark (6+3*count)))

end CatalyticTreeEval.Contracts.NativeBankAllocateFull

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_RestoringDivision -/

set_option autoImplicit false

namespace CatalyticTreeEval.BinaryArithmetic

structure DivisionState where
  quotient : ℕ
  remainder : ℕ
  deriving DecidableEq

/-- One most-significant-bit-first restoring-division round. The tentative
remainder is below `2*m`, so a single conditional subtraction suffices. -/
def divisionStep (m : ℕ) (s : DivisionState) (bit : Bool) : DivisionState :=
  let candidate := 2 * s.remainder + bit.toNat
  if m ≤ candidate then ⟨2 * s.quotient + 1, candidate - m⟩
  else ⟨2 * s.quotient, candidate⟩

def divisionLoop (m : ℕ) : DivisionState → List Bool → DivisionState
  | s, [] => s
  | s, bit :: rest => divisionLoop m (divisionStep m s bit) rest

def binaryValueLoop : ℕ → List Bool → ℕ
  | prefixValue, [] => prefixValue
  | prefixValue, bit :: rest => binaryValueLoop (2 * prefixValue + bit.toNat) rest

def binaryValueMSB (bits : List Bool) : ℕ := binaryValueLoop 0 bits

def restoringDivision (m : ℕ) (bits : List Bool) : DivisionState :=
  divisionLoop m ⟨0, 0⟩ bits

end CatalyticTreeEval.BinaryArithmetic

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeLaneWordTransfer -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeLaneWordTransfer

open CatalyticMatching.General

def sourceIndex {lanes : ℕ} (source : Fin lanes) : Fin (2 * lanes + 1) :=
  ⟨source.val, by omega⟩

def targetIndex {lanes : ℕ} (target : Fin lanes) (targetB : Bool) : Fin (2 * lanes + 1) :=
  ⟨(lanes + 1) * targetB.toNat + target.val, by cases targetB <;> simp <;> omega⟩

def distance {lanes : ℕ} (source target : Fin lanes) (targetB : Bool) : ℕ :=
  NativeLaneFlagCopy.distance (sourceIndex source) (targetIndex target targetB)

def bitArm {lanes : ℕ} (source target : Fin lanes) (targetB consume bit : Bool) : Main.Machine :=
  Sequential.machine
    (NativeLiteral.machine
      (NativeLaneFlagCopy.forward (sourceIndex source) (targetIndex target targetB))
      (distance source target targetB) (some bit))
    (NativeLiteral.machine
      (NativeLaneFlagCopy.backward (sourceIndex source) (targetIndex target targetB))
      (distance source target targetB) (if consume then some false else none))

def bitHop {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool) : Main.Machine :=
  Branch.machine (bitArm source target targetB consume true) (bitArm source target targetB consume false)

def forwardBody {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool) : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .right (lanes + 1) none)
    (Sequential.machine (bitHop source target targetB consume)
      (NativeLiteral.machine .right (2 * (lanes + 1)) none))

def forwardScan {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool) : Main.Machine :=
  WhileFlag.machine (forwardBody source target targetB consume)

def backStep (lanes : ℕ) : Main.Machine := NativeLiteral.machine .left (3 * (lanes + 1)) none

def rewind (lanes : ℕ) : Main.Machine :=
  Sequential.machine (backStep lanes)
    (Sequential.machine (WhileFlag.machine (backStep lanes)) (backStep lanes))

/-- Transfer every source A bit to the fixed destination A/B lane. Both banks
have the same padded width, discovered from the source's tags. Optional source
erasure is a fixed finite-control choice. The machine returns to source flag0. -/
def machine {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool) : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .right (6 * (lanes + 1)) none)
    (Sequential.machine (forwardScan source target targetB consume) (rewind lanes))

def sourceCell {lanes : ℕ} (source : Fin lanes) (base i : ℕ) : ℕ :=
  WorkLanes.address source base (7 + 3 * i)

def targetCell {lanes : ℕ} (target : Fin lanes) (targetB : Bool) (base i : ℕ) : ℕ :=
  WorkLanes.address target base (7 + 3 * i + targetB.toNat)

def footprint {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool)
    (base width : ℕ) : Footprint :=
  ⟨{p | (∃ i < width, p = targetCell target targetB base i) ∨
      (consume = true ∧ ∃ i < width, p = sourceCell source base i)}, ∅⟩

/-- Specification data only: each iteration updates its fixed destination and,
when requested, clears its source. It is not part of the transition table. -/
def prefixWork {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool)
    (base : ℕ) (original : ℕ → Bool) : ℕ → (ℕ → Bool)
  | 0 => original
  | n + 1 =>
    let updated := Function.update (prefixWork source target targetB consume base original n)
      (targetCell target targetB base n) (original (sourceCell source base n))
    if consume then Function.update updated (sourceCell source base n) false else updated

def time {lanes : ℕ} (source target : Fin lanes) (targetB : Bool) (width : ℕ) : ℕ :=
  width * (6 * (lanes + 1) + 2 * distance source target targetB + 8) + 12 * (lanes + 1) + 5

end CatalyticTreeEval.Contracts.NativeLaneWordTransfer

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_WorkLaneContracts -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.WorkLanes

/-- The source's writable work cells, mapped into its physical lane. -/
def liftedFootprint {lanes : ℕ} (lane : Fin lanes) (base : ℕ) (F : Footprint) : Footprint :=
  ⟨(address lane base) '' F.work, F.catalyst⟩

/-- Charge the entire addressed physical prefix, including origin-marker cells. -/
def liftedEnvelope (lanes base : ℕ) (E : Envelope) : Envelope :=
  ⟨base, base + (lanes + 1) * E.workHi, E.catalystLo, E.catalystHi⟩

/-- Every physical cell outside the active work lane is preserved. -/
def Inactive {lanes : ℕ} (lane : Fin lanes) (base : ℕ)
    (initial current : ℕ → Bool) : Prop :=
  ∀ p, p ∉ Set.range (address lane base) → current p = initial p

end CatalyticTreeEval.Contracts.WorkLanes

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_BinaryCountdownRewind -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinaryCountdown

def rewindCursor {advance : Bool} (c : Config (machine advance)) (top : ℕ)
    (borrow nonzero : Bool) (u : ℕ) : Config (machine advance) :=
  cursor c (top - u) (some (if u = 0 then tag borrow nonzero else
    if u % 3 = 0 then rewind nonzero 0 else if u % 3 = 1 then rewind nonzero 1 else rewind nonzero 2))

def exitCursor {advance : Bool} (c : Config (machine advance)) (base : ℕ)
    (nonzero : Bool) (u : ℕ) : Config (machine advance) :=
  { c with
    state := if u = 0 then some (rewind nonzero 0) else if u = 1 then some (back nonzero 0)
      else if u = 2 then some (back nonzero 1) else if u = 3 then some (writeFlag nonzero) else none
    workHead := base + 3 - min u 3
    catalystHead := if u ≤ 3 then c.catalystHead else c.catalystHead + advance.toNat
    work := if u ≤ 3 then c.work else Function.update c.work base nonzero }

end CatalyticTreeEval.Contracts.BinaryCountdown

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_BinaryCountdownTrace -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinaryCountdown

def entryCursor {advance : Bool} (c : Config (machine advance)) (base u : ℕ) :
    Config (machine advance) :=
  if h : u < 6 then cursor c (base + u) (some (entry ⟨u, h⟩))
  else cursor c (base + 6) (some (tag true false))

def columnCursor {advance : Bool} (c : Config (machine advance)) (base : ℕ)
    (a : ℕ → Bool) (n phase : ℕ) : Config (machine advance) :=
  if phase = 0 then
    cursor {c with work := prefixWork c.work base a n} (base + 6 + 3 * n)
      (some (tag (borrowAt a n) (nonzeroAt a n)))
  else if phase = 1 then
    cursor {c with work := prefixWork c.work base a n} (base + 6 + 3 * n + 1)
      (some (digit (borrowAt a n) (nonzeroAt a n)))
  else cursor {c with work := prefixWork c.work base a (n + 1)} (base + 6 + 3 * n + 2)
    (some (skip (borrowAt a (n + 1)) (nonzeroAt a (n + 1))))

def forwardCursor {advance : Bool} (c : Config (machine advance)) (base : ℕ)
    (a : ℕ → Bool) (u : ℕ) : Config (machine advance) := columnCursor c base a (u / 3) (u % 3)

end CatalyticTreeEval.Contracts.BinaryCountdown

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_BinaryCountdownContract -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinaryCountdown

/-- Explicit global phase snapshot, used only as the specification of the native trace. -/
def bankCursor {advance : Bool} (c : Config (machine advance)) (base width : ℕ)
    (a : ℕ → Bool) (u : ℕ) : Config (machine advance) :=
  if u ≤ 6 then entryCursor c base u
  else if u ≤ 6 + 3 * width then forwardCursor c base a (u - 6)
  else
    let C : Config (machine advance) := {c with work := prefixWork c.work base a width}
    let v := u - (6 + 3 * width)
    if v ≤ 3 * width + 3 then
      rewindCursor C (base + 6 + 3 * width) (borrowAt a width) (nonzeroAt a width) v
    else exitCursor C base (nonzeroAt a width) (v - (3 * width + 3))

end CatalyticTreeEval.Contracts.BinaryCountdown

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_BinarySeek -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinarySeek

open BinaryCountdown

/-- Thirty-one ordinary finite states: a binary countdown body and a one-state controller. -/
def machine (advance : Bool) : Main.Machine := WhileFlag.machine (BinaryCountdown.machine advance)

def digitsAt (a : ℕ → Bool) : ℕ → ℕ → Bool
  | 0 => a
  | n + 1 => BinaryCountdown.resultAt (digitsAt a n)

def phase {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool) : ℕ → Config (BinaryCountdown.machine advance)
  | 0 => BinaryCountdown.cursor c base none
  | n + 1 => BinaryCountdown.finished (phase c base width a n) base width (digitsAt a n)

end CatalyticTreeEval.Contracts.BinarySeek

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeCatalystStationary -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeHeadStationary

open CatalyticMatching.General

inductive Head where
  | input
  | catalyst
  deriving DecidableEq

def motion (head : Head) {states : ℕ} (a : Instruction states) : Move :=
  match head with
  | .input => a.inputMove
  | .catalyst => a.catalystMove

def position (head : Head) {M : Main.Machine} (c : Config M) : ℕ :=
  match head with
  | .input => c.inputHead
  | .catalyst => c.catalystHead

/-- A finite-table property, independent of input size, bank width, execution
time and catalyst suffix. Catalyst data preservation is a separate frame. -/
def Stationary (head : Head) (M : Main.Machine) : Prop :=
  ∀ q input work catalyst io wo co, motion head (M.table q input work catalyst io wo co)=.stay

abbrev CatalystStationary (M : Main.Machine) := Stationary .catalyst M
abbrev InputStationary (M : Main.Machine) := Stationary .input M

end CatalyticTreeEval.Contracts.NativeHeadStationary

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_TaggedReturn -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.TaggedReturn

open CatalyticMatching.General

abbrev Control (A : Machine) (tags : ℕ) := Fin (tags + 1) × Option (Fin A.states)

noncomputable def encode (A : Machine) (tags : ℕ) :
    Control A tags ≃ Fin (Fintype.card (Control A tags)) := Fintype.equivFin _

noncomputable def liftInstruction (A : Machine) (tags : ℕ) (tag : Fin (tags + 1))
    (a : Instruction A.states) : Instruction (Fintype.card (Control A tags)) where
  next := some (encode A tags (tag, a.next))
  workWrite := a.workWrite
  catalystWrite := a.catalystWrite
  inputMove := a.inputMove
  workMove := a.workMove
  catalystMove := a.catalystMove
  emit := a.emit

/-- Retain one fixed finite context through a native subroutine. Source halt
reaches a live tagged return port; a further quiet transition would halt. -/
noncomputable def machine (A : Machine) (tags : ℕ) : Main.Machine where
  states := Fintype.card (Control A tags)
  start := encode A tags (⟨0, by omega⟩, some A.start)
  table q input work catalyst io wo co :=
    let control := (encode A tags).symm q
    match control.2 with
    | some source => liftInstruction A tags control.1 (A.table source input work catalyst io wo co)
    | none =>
      { next := none, workWrite := work, catalystWrite := none,
        inputMove := .stay, workMove := .stay, catalystMove := .stay, emit := none }

noncomputable def entry (A : Machine) (tags : ℕ) (tag : Fin (tags + 1)) :
    Fin (machine A tags).states := encode A tags (tag, some A.start)

noncomputable def returned (A : Machine) (tags : ℕ) (tag : Fin (tags + 1)) :
    Fin (machine A tags).states := encode A tags (tag, none)

noncomputable def embed (A : Machine) (tags : ℕ) (tag : Fin (tags + 1))
    (c : Configuration A) : Configuration (machine A tags) :=
  { c with state := some (encode A tags (tag, c.state)) }

end CatalyticTreeEval.Contracts.TaggedReturn

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeQuotientRound -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeQuotientRound

/-- Restore an unsuccessful trial, then expose the zero quotient bit at flag0. -/
def reject : Main.Machine :=
  Sequential.machine RestoringRound.restore (ConsumeMSB.saveCarry false)

/-- Save the terminal trial carry in the caller flag while normalizing the bank. -/
def decision : Main.Machine := Branch.machine (ConsumeMSB.saveCarry true) reject

def trial : Main.Machine := Sequential.machine RippleSubtractor.machine decision

def bankRound (incoming : Bool) : Main.Machine :=
  Sequential.machine (Reentry.machine ShiftAppend.machine (ShiftAppend.marker incoming))
    (Sequential.machine (TaggedRewind.machine true) trial)

/-- One fixed restoring-division bit step, exporting its quotient bit at flag0. -/
def machine : Main.Machine :=
  Branch.machine
    (Sequential.machine (NativeLiteral.machine .right 6 none) (bankRound true))
    (Sequential.machine (NativeLiteral.machine .right 6 none) (bankRound false))

end CatalyticTreeEval.Contracts.NativeQuotientRound

/- Bundled native definition: Definitions.Def_CatalyticTreeEval_NativeModReduce -/

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeModReduce

def moveToBank : Main.Machine := NativeLiteral.machine .right 6 none

/-- A no-doubling trial reduction, entered and returned at the arithmetic flag.
For A < 2B its result is A modulo B. -/
def machine : Main.Machine := Sequential.machine moveToBank NativeQuotientRound.trial

def time (a b : ℕ → Bool) (width : ℕ) : ℕ :=
  7 + (5*width+1+if RippleSubtractor.carryAt a b true width then 3*width+9 else 11*width+17)

end CatalyticTreeEval.Contracts.NativeModReduce


