-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:17.791491+00:00
-- url     : https://prove2.me/theorems/2d888174-4327-4388-a718-9ef6ccd0113a
-- title:
--   Gradient At Point
-- statement:
--   Definitions and structural lemmas for Gradient At Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean

import Mathlib
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
open MvPolynomial
noncomputable section
namespace GradientAtPoint
variable {σ : Type*} (w : σ → ℂ)
def grad : MvPolynomial σ ℂ →ₗ[ℂ] (σ → ℂ) :=
  LinearMap.pi fun i => (aeval w).toLinearMap ∘ₗ (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap
def linPart [Fintype σ] (c : σ → ℂ) : MvPolynomial σ ℂ :=
  ∑ i, C (c i) * (X i - C (w i))
end GradientAtPoint
end
end GroundTheory.Heights₂.Heights


