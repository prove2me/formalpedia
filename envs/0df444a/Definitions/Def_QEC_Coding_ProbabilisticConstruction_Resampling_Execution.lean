-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_Execution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:16.992486+00:00
-- url     : https://prove2.me/theorems/73bc6c56-b6ae-480d-8cf0-a4d08590a9ed
-- title:
--   Execution
-- statement:
--   Definitions and structural lemmas for Execution, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
instance finiteOptionMeasurableSpace {α : Type*} [Fintype α] : MeasurableSpace (Option α) := ⊤
instance finiteOptionMeasurableSingletonClass {α : Type*} [Fintype α] :
    MeasurableSingletonClass (Option α) := ⟨fun _ => trivial⟩
section OrderedScan
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
def firstBadFrom : List I → Ω → Option I
  | [], _ => none
  | i :: tail, ω => if ω ∈ B i then some i else firstBadFrom tail ω
variable [Fintype I] [LinearOrder I]
def select (ω : Ω) : Option I := firstBadFrom B (Finset.univ.sort (· ≤ ·)) ω
variable [MeasurableSpace Ω] [MeasurableSpace I]
end OrderedScan
section Execution
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
abbrev Table := ∀ p : V × ℕ, X p.1
abbrev Counters (V : Type*) := V → ℕ
def tableRead (R : Table (X := X)) (v : V) (n : ℕ) : X v := R (v, n)
def assignment (R : Table (X := X)) (c : Counters V) : ∀ v, X v :=
  fun v => tableRead R v (c v)
def advance (vars : I → Finset V) (i : I) (c : Counters V) : Counters V :=
  fun v => c v + if v ∈ vars i then 1 else 0
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
instance decidableLocalEvents : ∀ i, DecidablePred (· ∈ localEvent vars bad i) :=
  fun i ω => inferInstanceAs (Decidable ((vars i).restrict ω ∈ bad i))
def step (R : Table (X := X)) (c : Counters V) : Counters V :=
  match select (localEvent vars bad) (assignment R c) with
  | none => c
  | some i => advance vars i c
def counters (R : Table (X := X)) : ℕ → Counters V
  | 0 => fun _ => 0
  | n + 1 => step vars bad R (counters R n)
def selected (R : Table (X := X)) (n : ℕ) : Option I :=
  select (localEvent vars bad) (assignment R (counters vars bad R n))
end Execution
section Measurability
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
noncomputable def tableLaw (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)] :
    Measure (Table (X := X)) := Measure.infinitePi (fun p : V × ℕ => ν p.1)
instance (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)] :
    IsProbabilityMeasure (tableLaw ν) := by unfold tableLaw; infer_instance
end Measurability
end QEC.Coding.ProbabilisticConstruction.Resampling


