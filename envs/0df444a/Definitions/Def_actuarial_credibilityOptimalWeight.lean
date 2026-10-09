-- Prove2me | Definitions.Def_actuarial_credibilityOptimalWeight
-- name    : actuarial_credibilityOptimalWeight
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:52:02.020921+00:00
-- url     : https://prove2.me/theorems/33ee6b00-6dc9-4f6a-b9f7-cbbf360df272
-- title:
--   Bühlmann–Straub variance-derived credibility factor
-- statement:
--   Expected process variance EPV describes conditional claim noise, whereas variance of hypothetical means VHM measures genuine between-risk heterogeneity. Exposure times VHM divided by exposure times VHM plus EPV is the least-squares credibility weight when the denominator is strictly positive.
--
--   **Mathematical statement**
--
--   $$
--   Z=\frac{P\,\mathrm{VHM}}{P\,\mathrm{VHM}+\mathrm{EPV}}
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib

namespace ActuarialValuation

noncomputable def credibilityOptimalWeight
  (totalExposure epv vhm : ℝ) : ℝ :=
  (totalExposure * vhm) / (totalExposure * vhm + epv)

end ActuarialValuation


