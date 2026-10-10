-- Prove2me | Definitions.Def_actuarial_exposureCredibilityPremium
-- name    : actuarial_exposureCredibilityPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:45:44.161461+00:00
-- url     : https://prove2.me/theorems/205c7a07-2ac8-4ae9-9566-efee8b9df408
-- title:
--   Credibility-weighted per-unit premium for a risk
-- statement:
--   This is an original derived actuarial definition, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The estimated per-unit risk rate interpolates between the risk's own observed claim experience and the collective portfolio mean. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \widehat\mu(P)=Z(P)\bar x+(1-Z(P))\mu
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration actuarial_exposureCredibilityPremium is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

namespace ActuarialValuation

noncomputable def exposureCredibilityPremium
  (EPV VHM P experience collective : ℝ) : ℝ :=
  exposureCredibilityWeight EPV VHM P * experience +
    (1 - exposureCredibilityWeight EPV VHM P) * collective

end ActuarialValuation


