-- Prove2me | Definitions.Def_actuarial_exposureCredibilityGain
-- name    : actuarial_exposureCredibilityGain
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T16:46:20.137692+00:00
-- url     : https://prove2.me/theorems/35412138-e0f6-4a4e-9953-af8982e7bb96
-- title:
--   Increase in weight from higher total exposure
-- statement:
--   This is an original derived actuarial definition, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The change in credibility measures the shift toward the policyholder's own claims experience when total exposure increases. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   G(P_1,P_2)=Z(P_2)-Z(P_1)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration actuarial_exposureCredibilityGain is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

namespace ActuarialValuation

noncomputable def exposureCredibilityGain
  (EPV VHM P₁ P₂ : ℝ) : ℝ :=
  exposureCredibilityWeight EPV VHM P₂ -
    exposureCredibilityWeight EPV VHM P₁

end ActuarialValuation


