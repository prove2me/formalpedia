-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_HasLaw_F000
-- name    : BrownianMotion_Auxiliary_HasLaw_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:03:41.316267+00:00
-- url     : https://prove2.me/theorems/6ccd470f-bd10-4755-a356-166da6c2b82f
-- title:
--   Source declarations: BrownianMotion.Auxiliary.HasLaw
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Auxiliary.HasLaw, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Distributions.Gaussian.Real


@[expose] public section

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {μ : Measure 𝓧} {P : Measure Ω}

lemma hasLaw_map (hX : AEMeasurable X P) : HasLaw X (P.map X) P where
  aemeasurable := hX
  map_eq := rfl
section dirac

-- don't upstream this: it's too specific. Delete it here eventually.
lemma HasLaw.ae_eq_const_of_gaussianReal {X : Ω → ℝ} {μ : ℝ} (hX : HasLaw X (gaussianReal μ 0) P) :
    ∀ᵐ ω ∂P, X ω = μ := by
  rw [gaussianReal_zero_var] at hX
  exact hX.ae_eq_of_dirac
end dirac

end HasLaw

end ProbabilityTheory


