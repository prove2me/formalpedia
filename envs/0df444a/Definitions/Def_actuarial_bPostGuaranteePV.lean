-- Prove2me | Definitions.Def_actuarial_bPostGuaranteePV
-- name    : actuarial_bPostGuaranteePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:15:52.846789+00:00
-- url     : https://prove2.me/theorems/24cc89d3-425f-4df4-a5e7-b94387d727e6
-- title:
--   Survival-contingent component after the guarantee
-- statement:
--   Survival-contingent component after the guarantee.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{post}}=\sum_{\substack{a+g\le j<\min(h,a+n)}}b_jv^{j+\delta}S_h(j+\delta)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 159, Guaranteed annuities (Chapter 5, section 5.9). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

noncomputable def bPostGuaranteePV (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n ∧ a+g ≤ j then b j * v^(j+delta) * bSurvival h p (j+delta) else 0

end ActuarialAnnuities


