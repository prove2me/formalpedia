-- Prove2me | Definitions.Def_actuarial_exposureCredibilityWeight
-- name    : actuarial_exposureCredibilityWeight
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:45:32.864977+00:00
-- url     : https://prove2.me/theorems/48af5d1a-2044-41f5-aa27-14d61de80aad
-- title:
--   Experience credibility weight for given exposure and structural variances
-- statement:
--   This is an original derived actuarial definition, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The classical exposure-based Bühlmann–Straub weight uses total exposure and structural process and between-risk variances. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   Z(P)=\frac{P\,\mathrm{VHM}}{P\,\mathrm{VHM}+\mathrm{EPV}}
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration actuarial_exposureCredibilityWeight is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def exposureCredibilityWeight (EPV VHM P : ℝ) : ℝ :=
  P * VHM / (P * VHM + EPV)

end ActuarialValuation


