-- Prove2me | Definitions.Def_ProbabilisticMethod_BernoulliWeights
-- name    : ProbabilisticMethod_BernoulliWeights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:58:44.269868+00:00
-- url     : https://prove2.me/theorems/9a812c69-38ca-4082-9dfa-d1ca31291285
-- title:
--   Bernoulli Weights
-- statement:
--   Definitions and structural lemmas for Bernoulli Weights, from Brian Sanders (Egly443/lean-probabilistic-method; see pinned Apache-2.0 LICENSE and source headers)'s pinned The finite probabilistic method for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/BernoulliWeights.lean

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
noncomputable def bernoulliWeight (A : Finset α) : ℝ := p ^ #A * (1 - p) ^ #(U \ A)
noncomputable def bernoulliProb (P : Finset α → Prop) [DecidablePred P] : ℝ :=
  ∑ A ∈ U.powerset with P A, U.bernoulliWeight p A
variable {U p}
def DependsOnCoords (P : Finset α → Prop) (T : Finset α) : Prop :=
  ∀ A B, A ∩ T = B ∩ T → (P A ↔ P B)
end Finset


