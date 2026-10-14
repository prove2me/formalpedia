-- Prove2me | Definitions.Def_actuarial_bSurvivalPV
-- name    : actuarial_bSurvivalPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:13:14.086307+00:00
-- url     : https://prove2.me/theorems/d3d34c4c-d405-4dff-a8c9-804c1d741d6d
-- title:
--   Independent survivor-projected present value
-- statement:
--   Independent survivor-projected present value.
--
--   Mathematical relation:
--
--   $$
--   V=\sum_{a\le j<\min(h,a+n)}b_jv^{j+\delta}\Pr(\text{payment at }j+\delta)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

noncomputable def bSurvivalPV (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n then b j * v^(j+delta) * (if j < a+g then bSurvival h p a else bSurvival h p (j+delta)) else 0

end ActuarialAnnuities


