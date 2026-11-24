-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffLimit
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffLimit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:37.576922+00:00
-- url     : https://prove2.me/theorems/502047a3-c124-4bd7-ac98-c08cd1700776
-- title:
--   St Cut Off Limit
-- statement:
--   Definitions and structural lemmas for St Cut Off Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCutOffLimit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def CutOffLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        ∀ (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
          SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
          HasCompactSupport F →
            Tendsto (fun k => chartInt J A (fun x => χ k x * F x) (vecCons G φ)) atTop
                (𝓝 (chartInt J A F (vecCons G φ))) ∧
              Tendsto (fun k => chartInt J A G (vecCons (fun x => χ k x * F x) φ)) atTop
                (𝓝 (chartInt J A G (vecCons F φ)))
end
end GroundTheory.Heights₂.Heights


