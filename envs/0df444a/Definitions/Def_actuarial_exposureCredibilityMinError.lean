-- Prove2me | Definitions.Def_actuarial_exposureCredibilityMinError
-- name    : actuarial_exposureCredibilityMinError
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:45:57.284975+00:00
-- url     : https://prove2.me/theorems/7ebd1ed5-9035-4824-9c24-cc9b33139233
-- title:
--   Minimal normalized quadratic credibility error at exposure
-- statement:
--   This is an original derived actuarial definition, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The minimum mean-square error of a credibility-weighted risk estimator is represented by a rational expression in total exposure and variance components. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   R_{\min}(P)=\frac{\mathrm{EPV}\,\mathrm{VHM}}{P\,\mathrm{VHM}+\mathrm{EPV}}
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration actuarial_exposureCredibilityMinError is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def exposureCredibilityMinError
  (EPV VHM P : ℝ) : ℝ :=
  EPV * VHM / (P * VHM + EPV)

end ActuarialValuation


