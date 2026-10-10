-- Prove2me | Definitions.Def_actuarial_trancheSchemeAdjustedPV
-- name    : actuarial_trancheSchemeAdjustedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T19:20:50.492213+00:00
-- url     : https://prove2.me/theorems/3cdf8708-489d-485a-aa5c-d53a4c4544cd
-- title:
--   TrancheSchemeAdjustedPV
-- statement:
--   Original derived definition for UK DB pension valuation. Aggregate monetary liability is the sum of tranche-specific adjusted liability contributions. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   V_{\rm adjusted}=\sum_{i<n}P_if_i A_i
--   $$
-- source:
--   Original derived result. Separate factor by pension tranche; multi-tranche actuarial equivalence, section 18 eq. (58)-(60). UK DB Retirement Factors Mathematical Framework, controlled version 5.3.0 (13 July 2026), Chapter 18, tranche equations (58)-(60); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/contents/9EAA5D04EA64E67BC84F7555AC82B4D1. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: UK_DB_Retirement_Factors_Mathematical_Framework_v5_3_0.pdf, Chapter 18, printed page 102, Eq. 58-60.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheAdjustedPV

namespace ActuarialValuation

noncomputable def trancheSchemeAdjustedPV (P immediate comparator : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, trancheAdjustedPV P immediate comparator i

end ActuarialValuation


