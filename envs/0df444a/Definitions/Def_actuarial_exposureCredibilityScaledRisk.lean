-- Prove2me | Definitions.Def_actuarial_exposureCredibilityScaledRisk
-- name    : actuarial_exposureCredibilityScaledRisk
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:46:04.727715+00:00
-- url     : https://prove2.me/theorems/4a7e7137-5904-4409-a67c-a3babcfad16c
-- title:
--   Exposure-scaled quadratic accuracy criterion
-- statement:
--   This is an original derived actuarial definition, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The strictly convex exposure-scaled risk criterion penalizes both underweighting of experience and excessive reliance on a noisy rate. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   Q_P(z)=P\,\mathrm{VHM}(1-z)^2+\mathrm{EPV}z^2
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration actuarial_exposureCredibilityScaledRisk is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def exposureCredibilityScaledRisk
  (EPV VHM P z : ℝ) : ℝ :=
  (P * VHM) * (1 - z) ^ 2 + EPV * z ^ 2

end ActuarialValuation


