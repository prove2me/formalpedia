-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffDominated
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffDominated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:28.732985+00:00
-- url     : https://prove2.me/theorems/0ab360ed-4a83-460e-b462-5c4def3ea047
-- title:
--   St Cut Off Dominated
-- statement:
--   Definitions and structural lemmas for St Cut Off Dominated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCutOffDominated.lean

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
noncomputable section
def CutOffDominated.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (P : MvPolynomial (Fin d) ℂ) (χ : ℕ → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A → P ≠ 0 →
    (∀ k, Measurable (χ k)) → (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    Integrable (chartAbsDens J A f ψ) →
      Tendsto (fun k => chartInt J A (fun x => χ k x * f x) ψ) atTop (𝓝 (chartInt J A f ψ))
end
end GroundTheory.Heights₂.Heights


