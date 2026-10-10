-- Prove2me | Definitions.Def_actuarial_pensionLatePostponedValue
-- name    : actuarial_pensionLatePostponedValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T19:22:11.564556+00:00
-- url     : https://prove2.me/theorems/cefe5ead-eb25-4245-8021-789b5ac8617b
-- title:
--   PensionLatePostponedValue
-- statement:
--   Original derived definition for UK DB pension valuation. The postponement death benefit is independent of the retirement factor; the survival route includes calendar pension increases missed during deferment. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   V_L=V_{\rm death}+pv\,m A_LF_L
--   $$
-- source:
--   Original derived result. Per-tranche early retirement and late postponement value routes, early and late factor derivation, pure versus total LRF. UK DB Retirement Factors Mathematical Framework, controlled version 5.3.0 (13 July 2026), Chapters 8-11 and 18, early/late route equations; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/contents/9EAA5D04EA64E67BC84F7555AC82B4D1. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: UK_DB_Retirement_Factors_Mathematical_Framework_v5_3_0.pdf, Chapters 9-11 including printed page 68, cashflow reconciliation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pensionLatePostponedValue
  (deathBefore survival discount missedIncrease lateAnnuity pureFactor : ℝ) : ℝ :=
  deathBefore + survival * discount * missedIncrease * lateAnnuity * pureFactor

end ActuarialValuation


