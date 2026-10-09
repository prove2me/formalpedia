-- Prove2me | Definitions.Def_OAI_PiExponent_WeightedSupport
-- name    : OAI_PiExponent_WeightedSupport
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-08T18:14:56.438771+00:00
-- url     : https://prove2.me/theorems/0828d7e5-6fc5-4395-9050-1edd8d30adb3
-- title:
--   Weighted support predicate for logarithmic formal jets
-- statement:
--   A formal jet has weighted support above B when every nonzero coefficient indexed by b has total coordinate weight at least B.
-- source:
--   Supporting definition for the weighted support theorem; coefficient indexing follows InterpolationMatrix.exponentVector.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open scoped BigOperators

noncomputable section

namespace OAI.PiExponent.FormalInterpolation

def hasWeightedSupport {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ)
    (F : MvPowerSeries (Fin (m + 1)) ℂ) : Prop :=
  ∀ b : Fin (m + 1) → ℕ,
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F ≠ 0 →
      B ≤ ∑ i, (b i : ℝ) * v i

end OAI.PiExponent.FormalInterpolation

end


