-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:27.721863+00:00
-- url     : https://prove2.me/theorems/c7c42306-0d09-4c20-a5a1-2d520a33b8c5
-- title:
--   Statements Fibre Mahler
-- statement:
--   Definitions and structural lemmas for Statements Fibre Mahler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsFibreMahler.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
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
open MvPolynomial NumberField
noncomputable section
def FibreMahlerForms.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (W : Type) [AddCommGroup W] [Module (𝓞 F) W]
    [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W] (h : HermitianMetric F W) (n : ℕ)
    (w : Fin n → W), Submodule.span (𝓞 F) (Set.range w) = ⊤ →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] (τ : K →+* ℂ) (m : ℕ)
      (yv : Fin m → DualVec F W K), (∀ q, yv q ≠ 0) → ∀ a : ℂ, a ≠ 0 →
        fibreMahler h (τ.comp (algebraMap F K)) w (C a * ∏ q, ∑ k, C (τ (yv q (w k))) * X k) =
          Real.log ‖a‖ + ∑ q, (Real.log (archDualNorm h τ (yv q)) -
            (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2)
example : HermitianMetric ℚ (Fin 2 → 𝓞 ℚ) := HermitianMetric.standard ℚ (Fin 2)
end
end GroundTheory.Heights₂.Heights


