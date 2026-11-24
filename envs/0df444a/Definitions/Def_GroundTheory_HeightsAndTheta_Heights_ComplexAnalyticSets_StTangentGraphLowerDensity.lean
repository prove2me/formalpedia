-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:19.328568+00:00
-- url     : https://prove2.me/theorems/336aef07-a3d4-40f3-8b13-42c72241929a
-- title:
--   St Tangent Graph Lower Density
-- statement:
--   Definitions and structural lemmas for St Tangent Graph Lower Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTangentGraphLowerDensity.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
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
open MeasureTheory
open scoped ENNReal
noncomputable section
def TangentGraphLowerDensity.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))) (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
    (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (w₀ : I₀ → ℂ),
    I₀.card = d → IsOpen Ω → IsOpen V → w₀ ∈ Ω → DifferentiableOn ℂ g Ω →
    (∀ w ∈ Ω, frameProj b I₀ (g w) = w) → S ∩ V = g '' Ω →
    (∀ j ∉ I₀, fderiv ℂ (fun w => inner ℂ (b j) (g w)) w₀ = 0) →
    ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ ∈ Set.Ioo (0 : ℝ) r₀,
      ENNReal.ofReal (θ * ρ ^ (2 * d)) *
          μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) ≤
        μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball (g w₀) ρ)
def TangentGraphLowerDensity.axisMap : (↥({0} : Finset (Fin 2)) → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin 2 =>
      if j = 0 then ContinuousLinearMap.proj (⟨0, Finset.mem_singleton_self 0⟩ : ↥({0} : Finset (Fin 2)))
      else 0)
end
end GroundTheory.Heights₂.Heights


