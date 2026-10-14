-- Prove2me | Definitions.Def_actuarial_bGuaranteedPV
-- name    : actuarial_bGuaranteedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:15:37.192931+00:00
-- url     : https://prove2.me/theorems/f78ba7dc-e0dd-430b-93bb-0faecde82a66
-- title:
--   Activated period-certain guarantee component
-- statement:
--   Activated period-certain guarantee component.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{guaranteed}}=S_h(a)\sum_{a\le j<\min(h,a+n,a+g)}b_jv^{j+\delta}
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 159, Guaranteed annuities (Chapter 5, section 5.9). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

noncomputable def bGuaranteedPV (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n ∧ j < a+g then b j * v^(j+delta) * bSurvival h p a else 0

end ActuarialAnnuities


