-- Prove2me | Definitions.Def_actuarial_credibilityWeightedExperience
-- name    : actuarial_credibilityWeightedExperience
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:51:47.757461+00:00
-- url     : https://prove2.me/theorems/37b2e406-1048-4cc9-91d3-24dd5270b763
-- title:
--   Weighted experience mean across unequal exposures
-- statement:
--   Observed claims per unit exposure may vary across periods. The experience mean weights each observation by its exposure and divides by total volume, as in the Bühlmann–Straub model. A nonzero exposure denominator is necessary for the ordinary weighted-mean interpretation.
--
--   **Mathematical statement**
--
--   $$
--   \bar X_P=\frac{\sum_i p_iX_i}{\sum_i p_i}
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityExposureTotal

namespace ActuarialValuation

noncomputable def credibilityWeightedExperience
  (exposure observed : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, exposure i * observed i) /
    credibilityExposureTotal exposure n

end ActuarialValuation


