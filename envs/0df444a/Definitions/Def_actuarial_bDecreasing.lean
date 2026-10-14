-- Prove2me | Definitions.Def_actuarial_bDecreasing
-- name    : actuarial_bDecreasing
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:19:10.76566+00:00
-- url     : https://prove2.me/theorems/3b3bc0e6-b7cf-43c7-9ec8-4020b4c53564
-- title:
--   Temporary cashflow instalments n, n-1, ... one
-- statement:
--   Temporary cashflow instalments n, n-1, ... one.
--
--   Mathematical relation:
--
--   $$
--   b_j=n-(j-a)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bDecreasing (a n j : ℕ) : ℝ := ((n-(j-a) : ℕ) : ℝ)

end ActuarialAnnuities


