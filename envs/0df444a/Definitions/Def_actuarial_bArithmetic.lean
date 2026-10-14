-- Prove2me | Definitions.Def_actuarial_bArithmetic
-- name    : actuarial_bArithmetic
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:18:01.861225+00:00
-- url     : https://prove2.me/theorems/df745e96-cd62-4e3a-ae4d-1442111b2ae1
-- title:
--   Arithmetic escalating or reducing cash amount
-- statement:
--   Arithmetic escalating or reducing cash amount.
--
--   Mathematical relation:
--
--   $$
--   b_j=c+s(j-a)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bArithmetic (a : ℕ) (c step : ℝ) (j : ℕ) : ℝ := c + step*((j-a : ℕ) : ℝ)

end ActuarialAnnuities


