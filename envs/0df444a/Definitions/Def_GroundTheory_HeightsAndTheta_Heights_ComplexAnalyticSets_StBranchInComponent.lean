-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInComponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:23:06.646206+00:00
-- url     : https://prove2.me/theorems/9f200430-2fa1-4fdd-90a5-59f8a0f58546
-- title:
--   St Branch In Component
-- statement:
--   Definitions and structural lemmas for St Branch In Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchInComponent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
def BranchInComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (q : Fin n → ℂ) (c : VarBranch I k q),
    ∃ J ∈ I.minimalPrimes, Set.MapsTo c.toFun (Metric.ball 0 c.radius) (zeroSet J)
def axisBranch : VarBranch (Ideal.span {X 0 * X 1} : Ideal (MvPolynomial (Fin 2) ℂ)) 1 0 where
  radius := 1
  radius_pos := one_pos
  toFun t := fun i ↦ if i = 0 then t 0 else 0
  differentiableOn := by
    refine Differentiable.differentiableOn (differentiable_pi.2 fun i ↦ ?_)
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact differentiable_apply 0
    · simp only [hi, if_false]
      exact differentiable_const 0
  injOn := by
    intro s _ t _ hst
    have h0 := congrFun hst 0
    simp only [if_true] at h0
    funext i
    rw [Subsingleton.elim i 0]
    exact h0
  map_zero := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  mapsTo := by
    intro t _ g hg
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    simp
end
end GroundTheory.Heights₂.Heights


