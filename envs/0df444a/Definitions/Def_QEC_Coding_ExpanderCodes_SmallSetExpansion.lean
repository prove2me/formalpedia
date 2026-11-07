-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
-- name    : QEC_Coding_ExpanderCodes_SmallSetExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:45:25.710581+00:00
-- url     : https://prove2.me/theorems/9e968920-c6c6-436f-a8d0-3374baec56ed
-- title:
--   Small Set Expansion
-- statement:
--   Definitions and structural lemmas for Small Set Expansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
namespace QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
abbrev WeightedGraph (V : Type u) := V → V → Nat
def crossCount (M : WeightedGraph V) (S T : Finset V) : Nat :=
  ∑ v ∈ S, ∑ u ∈ T, M v u
def IsSmallSetEdgeExpanding
    (M : WeightedGraph V) (radius : Nat) (lambda : ℝ) : Prop :=
  ∀ S T : Finset V,
    S.card ≤ radius → T.card ≤ radius →
      (crossCount M S T : ℝ) ≤
        lambda * Real.sqrt ((S.card : ℝ) * T.card)
def HasForwardDegreeAtLeast
    (M : WeightedGraph V) (S T : Finset V) (degree : Nat) : Prop :=
  ∀ v ∈ S, degree ≤ ∑ u ∈ T, M v u
def square [Fintype V] (M : WeightedGraph V) : WeightedGraph V :=
  fun v u => ∑ x, M v x * M x u
def add (M N : WeightedGraph V) : WeightedGraph V :=
  fun v u => M v u + N v u
def relabel {U : Type*} (e : V ≃ U) (M : WeightedGraph V) : WeightedGraph U :=
  fun u u' => M (e.symm u) (e.symm u')
def disjointUnion {I : Type*} [DecidableEq I]
    (M : I → WeightedGraph V) : WeightedGraph (I × V) :=
  fun iv ju => if iv.1 = ju.1 then M iv.1 iv.2 ju.2 else 0
def productFiber {I : Type*} [DecidableEq I] [DecidableEq V]
    (S : Finset (I × V)) (i : I) : Finset V :=
  (S.filter fun iv => iv.1 = i).image Prod.snd
end QEC.Coding.SmallSetExpansion


