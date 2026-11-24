-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GaussIntegral
-- name    : Formalism_PeriodIntegrals_GaussIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:13.48444+00:00
-- url     : https://prove2.me/theorems/ece77c74-a15a-41e9-b1b0-8af6fb6e530e
-- title:
--   Gauss Integral
-- statement:
--   Definitions and structural lemmas for Gauss Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GaussIntegral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory
namespace PI
def GaussIntegral : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) F), H.IsSymm → H.det ≠ 0 →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, t ≠ 0 → (μ ((fun y => t * y) '' (𝒪[F] : Set F))).toReal < δ →
    ‖∫ x in (L : Set (Fin d → F)), ψ (dotProduct x (H.mulVec x) / (2 * t))
        ∂(Measure.pi fun _ : Fin d => μ)‖ =
      (μ ((fun y => (t⁻¹ • H).det * y) '' (𝒪[F] : Set F))).toReal ^ (-(1 / 2 : ℝ))
end PI


