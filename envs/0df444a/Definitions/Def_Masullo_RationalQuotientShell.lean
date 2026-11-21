-- Prove2me | Definitions.Def_Masullo_RationalQuotientShell
-- name    : Masullo_RationalQuotientShell
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T03:14:33.066515+00:00
-- url     : https://prove2.me/theorems/9dd39c48-8ff7-45b5-a3bf-4dccf8d17f8a
-- title:
--   Weighted spherical orbital images on the rational idèle class group
-- statement:
--   On the rational idèle class group, weight Haar measure by $1+(\log|z|)^2$, the manuscript weight at Sobolev exponent two. For a family of actual rational adelic test functions, take their orbital sums averaged over the compact finite unit group. Require each average to belong to the full unmasked weighted Hilbert space before multiplying it by the indicator of a measurable set of logarithmic norms. The test image is the family of resulting Hilbert vectors. The corresponding weight on the real line uses Lebesgue measure.
-- source:
--   A. M. Masullo, The Music of the Primes, Theorem 11.1.2.1(2), equations (11.1.2.3), (11.1.2.6) and (11.1.2.9).

import Definitions.Def_Masullo_RationalSphericalCutoff
import Definitions.Def_MasulloRH_RationalIdeleClass

open MeasureTheory Set MasulloRH.RationalFinite MasulloRH.RationalClass

namespace MasulloAudit.RationalQuotientShell
noncomputable section

/-- The manuscript's log weight at Sobolev index two. -/
def weight (t : ℝ) := ENNReal.ofReal (1+t^2)

def realMeasure : Measure ℝ := volume.withDensity weight

def classMeasure [MeasurableSpace C] (ν : Measure C) : Measure C :=
  ν.withDensity (fun z => weight (logNorm z))

/-- Actual compact-unit averages, required to be in the full weighted Hilbert space
even before applying the mask. -/
def testImage [MeasurableSpace K] [MeasurableSpace C] (κ : Measure K) (ν : Measure C)
    (s : Set ℝ) (B : Set (Ad → ℂ)) : Set (Lp ℂ 2 (classMeasure ν)) :=
  {v | ∃ F ∈ B, MemLp (sphericalTheta κ F) 2 (classMeasure ν) ∧
    (v : C → ℂ) =ᵐ[classMeasure ν] (logNorm ⁻¹' s).indicator (sphericalTheta κ F)}

end
end MasulloAudit.RationalQuotientShell


