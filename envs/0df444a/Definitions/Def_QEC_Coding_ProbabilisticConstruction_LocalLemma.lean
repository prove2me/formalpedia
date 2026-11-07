-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
-- name    : QEC_Coding_ProbabilisticConstruction_LocalLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:07:49.495341+00:00
-- url     : https://prove2.me/theorems/600c46cf-931a-44bd-8c35-53b1d440e43e
-- title:
--   Local Lemma
-- statement:
--   Definitions and structural lemmas for Local Lemma, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
def avoid (B : I → Set Ω) (S : Finset I) : Set Ω :=
  {ω | ∀ i ∈ S, ω ∉ B i}
def HasDependencyGraph (μ : Measure Ω) (B : I → Set Ω) (G : SimpleGraph I) : Prop :=
  ∀ i, Indep (MeasurableSpace.generateFrom {B i})
    (MeasurableSpace.generateFrom
      {E | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ E = B j}) μ
section MeasureBounds
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
include hB
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable (hdep : HasDependencyGraph μ B G)
variable (hcrit : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j))
include hx0 hx1 hdep hcrit
end MeasureBounds
section ProductVariables
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
def supportGraph (vars : I → Finset V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ¬ Disjoint (vars i) (vars j)
  symm := by constructor; intro i j h; exact ⟨h.1.symm, fun hd => h.2 hd.symm⟩
  loopless := by constructor; intro i h; exact h.1 rfl
instance (vars : I → Finset V) : DecidableRel (supportGraph vars).Adj := by
  unfold supportGraph
  infer_instance
def localEvent (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
    (i : I) : Set (∀ v, X v) :=
  (vars i).restrict ⁻¹' bad i
end ProductVariables
end QEC.Coding.ProbabilisticConstruction


