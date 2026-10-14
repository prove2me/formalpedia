-- Prove2me | Definitions.Def_actuarial_bLevel
-- name    : actuarial_bLevel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:17:06.872221+00:00
-- url     : https://prove2.me/theorems/7ddb70d6-63d6-46bd-ad75-e56be0562777
-- title:
--   Level cash amount per instalment
-- statement:
--   Level cash amount per instalment.
--
--   Mathematical relation:
--
--   $$
--   b_j=c
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bLevel (c : ℝ) (_j : ℕ) : ℝ := c

end ActuarialAnnuities


