-- Prove2me | Definitions.Def_DynEdgeColorLLL_Main_Supplement_OracleRAM
-- name    : DynEdgeColorLLL_Main_Supplement_OracleRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:01:27.558555+00:00
-- url     : https://prove2.me/theorems/fd161462-77b0-4553-9bd0-62e83ab652eb
-- title:
--   Costed oracle RAM with opaque values and persistent private state
-- statement:
--   A program is a finite list of arithmetic, comparison, branch, pointer-memory, allocation, input, random-choice and output instructions. It can store and copy opaque values. Its only semantic oracle requests are sampling one variable, evaluating one clause on an explicitly supplied array of values, and inserting or deleting one clause incidence. Oracle implementations have private mutable state and return their actual nonnegative running costs.
--
--   Ordinary instructions and output writes cost one time unit. Evaluation-argument marshalling costs one additional cell access per entry. The charged cost is
--
--   $$\mathrm{cost}=\mathrm{ordinary\ steps}+\sum_{\text{executed calls}}\mathrm{actual\ oracle\ cost}.$$
--
--   Independent tapes supply fresh private oracle randomness and uniform finite hashing choices; the cursor persists across operations. Failed or nonterminating computations have infinite cost. Completed states are obtained by executing the program to its first successful completion, rather than by choosing a state satisfying a specification.
--
--   This supplies a reusable operational interface for implicit, arbitrary-domain randomized algorithms. It exposes neither truth-table code nor a whole-transcript transformation to the program.
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §3.1 and §3.4, printed pp. 9, 14–16 (PDF pp. 11, 16–18)

import Mathlib

set_option autoImplicit false

namespace DynEdgeColorLLL.Main.Supplement.OracleRAM

open MeasureTheory
open scoped ENNReal

/-! A finite counter/pointer RAM with opaque atoms and three costed oracle interfaces.
No instruction sees the oracle implementation, a truth table, or an execution transcript.
Oracle arguments are arrays prepared by ordinary loads/stores. Marshalling an array
charges one ordinary cell access per entry. Each output write is one ordinary step. -/

inductive Instr where
  | const (dst : ℕ) (value : ℕ)
  | copy (dst src : ℕ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | mod (dst a b : ℕ)
  | branch (a b yes no : ℕ)
  | jump (target : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | alloc (dst size : ℕ)
  | input (dst index : ℕ)
  | random (dst bound : ℕ)
  | sample (varReg dst : ℕ)
  | evaluate (clause pointer length dst : ℕ)
  | updateClause (clause varReg insert value dst : ℕ)
  | writeValue (varReg src : ℕ)
  | eraseValue (varReg : ℕ)
  | done
  deriving DecidableEq

abbrev Program := List Instr
abbrev Cell (A : Type*) := ℕ ⊕ A

/-- tag, clause, variable, argument array, insertion value. Tags 0,1,2 denote
sample, evaluate and updateClause. On an update, none denotes deletion. -/
abbrev Request (A : Type*) := ℕ × ℕ × ℕ × List A × Option A
abbrev Response (A H : Type*) := Option A × Bool × H × ℝ≥0∞

/-- Coproduct and finite-sequence measurable structures; atom equality is not inspected. -/
scoped instance optionMeasurable (A : Type*) [MeasurableSpace A] : MeasurableSpace (Option A) :=
  MeasurableSpace.comap (fun v : Option A => match v with
    | none => (Sum.inl () : Unit ⊕ A)
    | some a => Sum.inr a) inferInstance

scoped instance listMeasurable (A : Type*) [MeasurableSpace A] : MeasurableSpace (List A) :=
  MeasurableSpace.comap
    (fun v : List A => (⟨v.length, fun i : Fin v.length => v[i]⟩ : (n : ℕ) × (Fin n → A)))
    inferInstance

/-- Private state is opaque to the caller; only the reply and charged time are exposed. -/
structure Oracle (A H Ξ : Type*) where
  initial : H
  invoke : H → Request A → Ξ → Response A H

structure State (A H : Type*) where
  pc : ℕ
  reg : ℕ → Cell A
  mem : ℕ → Cell A
  heap : ℕ
  output : ℕ → Option A
  hidden : H
  used : ℕ
  done : Bool
  failed : Bool
  own : ℕ
  charged : ℝ≥0∞

def number {A : Type*} : Cell A → ℕ
  | .inl n => n
  | .inr _ => 0

def atom {A : Type*} : Cell A → Option A
  | .inl _ => none
  | .inr a => some a

def initial {A H Ξ : Type*} (O : Oracle A H Ξ) : State A H :=
  { pc := 0, reg := fun _ => .inl 0, mem := fun _ => .inl 0, heap := 1
    output := fun _ => none, hidden := O.initial, used := 0
    done := true, failed := false, own := 0, charged := 0 }

abbrev HashRow := (b : ℕ) → Fin (b + 1)
abbrev Tape (Ξ : Type*) := (ℕ → Ξ) × (ℕ → HashRow)

noncomputable def hashMeasure : Measure (ℕ → HashRow) :=
  Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun b : ℕ =>
    (PMF.uniformOfFintype (Fin (b + 1))).toMeasure

noncomputable def tapeMeasure {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] : Measure (Tape Ξ) :=
  (Measure.infinitePi fun _ : ℕ => ν).prod hashMeasure

def prepare {A H : Type*} (s : State A H) : State A H :=
  { s with pc := 0, done := false, own := 0, charged := 0 }

def getArray {A H : Type*} (s : State A H) (p len : ℕ) : Option (List A) :=
  (List.range len).mapM fun i => atom (s.mem (p + i))

def advance {A H : Type*} (s : State A H) (extra : ℕ := 1) : State A H :=
  { s with
    pc := s.pc + 1
    used := s.used + 1
    own := s.own + extra
    charged := s.charged + (extra : ℝ≥0∞) }

def setReg {A H : Type*} (s : State A H) (d : ℕ) (v : Cell A) : State A H :=
  { s with reg := Function.update s.reg d v }

def trap {A H : Type*} (s : State A H) : State A H :=
  { s with failed := true, done := false }

def call {A H Ξ : Type*} (O : Oracle A H Ξ) (ξ : Ξ)
    (s : State A H) (req : Request A) (dst : ℕ) (asAtom : Bool)
    (extra : ℕ := 1) : State A H :=
  let ans := O.invoke s.hidden req ξ
  let t := advance s extra
  let t := { t with hidden := ans.2.2.1, charged := t.charged + ans.2.2.2 }
  if asAtom then
    match ans.1 with
    | none => trap t
    | some a => setReg t dst (.inr a)
  else setReg t dst (.inl (if ans.2.1 then 1 else 0))

/-- One executed instruction. Ordinary arithmetic, tests and cell accesses cost one.
The only variable-size instruction marshals an evaluation array and charges its full length.
Failure and invalid instruction addresses cannot count as successful completion. -/
def step {A H Ξ : Type*} (tag : A → ℕ) (O : Oracle A H Ξ)
    (P : Program) (allowed : ℕ → Bool) (input : ℕ → ℕ) (ω : Tape Ξ) (s : State A H) : State A H :=
  if s.done || s.failed then s else
  let R := fun i => number (s.reg i)
  let t := advance s
  match P[s.pc]? with
  | none => trap t
  | some ins => match ins with
    | .const d n => setReg t d (.inl n)
    | .copy d a => setReg t d (s.reg a)
    | .add d a b => setReg t d (.inl (R a + R b))
    | .sub d a b => setReg t d (.inl (R a - R b))
    | .mul d a b => setReg t d (.inl (R a * R b))
    | .div d a b => setReg t d (.inl (R a / R b))
    | .mod d a b => setReg t d (.inl (R a % R b))
    | .branch a b yes no => { t with pc := if R a < R b then yes else no }
    | .jump target => { t with pc := target }
    | .load d a => setReg t d (s.mem (R a))
    | .store a v => { t with mem := Function.update s.mem (R a) (s.reg v) }
    | .alloc d n => setReg { t with heap := s.heap + R n } d (.inl s.heap)
    | .input d i => setReg t d (.inl (input (R i)))
    | .random d b => setReg t d (.inl ((ω.2 s.used (R b)).val))
    | .sample x d => if allowed (R x) then
        call O (ω.1 s.used) s (0, 0, R x, [], none) d true else trap t
    | .evaluate c p n d =>
        match getArray s (R p) (R n) with
        | none => trap t
        | some args => call O (ω.1 s.used) s (1, R c, 0, args, none) d false (1 + R n)
    | .updateClause c x ins v d =>
        if !allowed (R x) then trap t else if R ins = 0 then call O (ω.1 s.used) s (2, R c, R x, [], none) d false
        else match atom (s.reg v) with
          | none => trap t
          | some a =>
              if tag a = R x then call O (ω.1 s.used) s (2, R c, R x, [], some a) d false
              else trap t
    | .writeValue x a => match atom (s.reg a) with
        | none => trap t
        | some v => if tag v = R x then { t with output := Function.update s.output (R x) (some v) }
          else trap t
    | .eraseValue x => { t with output := Function.update s.output (R x) none }
    | .done => { t with done := true }

def run {A H Ξ : Type*} (tag : A → ℕ) (O : Oracle A H Ξ) (P : Program)
    (allowed : ℕ → Bool) (input : ℕ → ℕ) (ω : Tape Ξ) (s : State A H) (t : ℕ) : State A H :=
  (step tag O P allowed input ω)^[t] s

def Completes {A H Ξ : Type*} (tag : A → ℕ) (O : Oracle A H Ξ) (P : Program)
    (allowed : ℕ → Bool) (input : ℕ → ℕ) (ω : Tape Ξ) (s : State A H) : Prop :=
  ∃ t, (run tag O P allowed input ω s t).done = true ∧ (run tag O P allowed input ω s t).failed = false ∧
    (run tag O P allowed input ω s t).charged ≠ ⊤

noncomputable def completed {A H Ξ : Type*} (tag : A → ℕ) (O : Oracle A H Ξ) (P : Program)
    (allowed : ℕ → Bool) (input : ℕ → ℕ) (ω : Tape Ξ) (s : State A H) : State A H := by
  classical
  exact if h : Completes tag O P allowed input ω s then run tag O P allowed input ω s (Nat.find h) else trap s

noncomputable def time {A H Ξ : Type*} (tag : A → ℕ) (O : Oracle A H Ξ) (P : Program)
    (allowed : ℕ → Bool) (input : ℕ → ℕ) (ω : Tape Ξ) (s : State A H) : ℝ≥0∞ := by
  classical
  exact if Completes tag O P allowed input ω s then (completed tag O P allowed input ω s).charged else ⊤

end DynEdgeColorLLL.Main.Supplement.OracleRAM


