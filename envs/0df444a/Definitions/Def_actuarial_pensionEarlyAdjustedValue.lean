-- Prove2me | Definitions.Def_actuarial_pensionEarlyAdjustedValue
-- name    : actuarial_pensionEarlyAdjustedValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T19:22:03.335809+00:00
-- url     : https://prove2.me/theorems/874802e0-5d2a-45d7-8ec5-22050e3be563
-- title:
--   PensionEarlyAdjustedValue
-- statement:
--   Original derived definition for UK DB pension valuation. The value of early pension after reduction is its factor multiplied by the immediate early annuity package. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   V_E=F_EA_E
--   $$
-- source:
--   Original derived result. Per-tranche early retirement and late postponement value routes, early and late factor derivation, pure versus total LRF. UK DB Retirement Factors Mathematical Framework, controlled version 5.3.0 (13 July 2026), Chapters 8-11 and 18, early/late route equations; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/contents/9EAA5D04EA64E67BC84F7555AC82B4D1. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: UK_DB_Retirement_Factors_Mathematical_Framework_v5_3_0.pdf, Chapters 9-11 including printed page 68, cashflow reconciliation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionEarlyFactor

namespace ActuarialValuation

noncomputable def pensionEarlyAdjustedValue (comparator earlyAnnuity : ℝ) : ℝ :=
  pensionEarlyFactor comparator earlyAnnuity * earlyAnnuity

end ActuarialValuation


