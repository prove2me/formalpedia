-- Prove2me | Definitions.Def_actuarial_credibilityExposureTotal
-- name    : actuarial_credibilityExposureTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:51:15.251263+00:00
-- url     : https://prove2.me/theorems/34410da3-b2c7-4e3e-bd21-33016f32be60
-- title:
--   Aggregate observation exposure for weighted credibility
-- statement:
--   Bühlmann–Straub weighting allows different periods to represent different volumes of insured exposure. The total volume is the finite sum of the individual observation weights; it must be strictly positive to form a meaningful weighted sample mean.
--
--   **Mathematical statement**
--
--   $$
--   P=\sum_{i=0}^{n-1}p_i
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib

namespace ActuarialValuation

noncomputable def credibilityExposureTotal
  (exposure : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, exposure i

end ActuarialValuation


