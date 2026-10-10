-- Prove2me | Definitions.Def_actuarial_trancheAnnuityLedgerValue
-- name    : actuarial_trancheAnnuityLedgerValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T19:19:47.458529+00:00
-- url     : https://prove2.me/theorems/c038e32e-f511-4224-af62-b86d09a822e4
-- title:
--   TrancheAnnuityLedgerValue
-- statement:
--   Original derived definition for UK DB pension valuation. Each tranche i has its own finite indexed present-value payment ledger. Its terms may already embody discounts, member survival, survivor payments and benefit-specific increases. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   A_i=\sum_{k<H}w_{i,k}
--   $$
-- source:
--   Original derived result. Separate factor by pension tranche; multi-tranche actuarial equivalence, section 18 eq. (58)-(60). UK DB Retirement Factors Mathematical Framework, controlled version 5.3.0 (13 July 2026), Chapter 18, tranche equations (58)-(60); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/contents/9EAA5D04EA64E67BC84F7555AC82B4D1. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: UK_DB_Retirement_Factors_Mathematical_Framework_v5_3_0.pdf, Chapter 18, printed page 102, Eq. 58-60.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def trancheAnnuityLedgerValue (w : ℕ → ℕ → ℝ) (i H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range H, w i k

end ActuarialValuation


