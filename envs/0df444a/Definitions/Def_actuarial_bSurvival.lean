-- Prove2me | Definitions.Def_actuarial_bSurvival
-- name    : actuarial_bSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:04:48.251432+00:00
-- url     : https://prove2.me/theorems/bbb52228-7154-4bfb-acb4-730cc4fb8088
-- title:
--   Survival derived from actual censored lifetime states
-- statement:
--   Survival derived from actual censored lifetime states.
--
--   Mathematical relation:
--
--   $$
--   S_h(t)=\sum_{k=0}^{h}p_kI_k(t)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive

namespace ActuarialAnnuities

noncomputable def bSurvival (h : ℕ) (p : ℕ → ℝ) (t : ℕ) : ℝ := ∑ k ∈ Finset.range (h+1), p k * bAlive k t

end ActuarialAnnuities


