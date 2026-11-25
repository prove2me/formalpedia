-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusModulus
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusModulus
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:25.039801+00:00
-- url     : https://prove2.me/theorems/c2d474e7-8858-4d81-88b1-745163a7a69a
-- title:
--   Statements Torus Modulus
-- statement:
--   Definitions and structural lemmas for Statements Torus Modulus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsTorusModulus.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def TorusModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (g : archUnitary h v) (a : InfinitePlace E → ℂ),
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = a w • vecAt v x₀ w) →
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w) →
    (∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z) →
    ∀ (ν : Measure (vecFixGroup h v x₀)) [ν.IsHaarMeasure] (f : archUnitary h v → ℝ≥0∞),
      Measurable f →
      ∫⁻ x, f (g * x * g⁻¹) ∂ν = (∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))) * ∫⁻ x, f x ∂ν
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


