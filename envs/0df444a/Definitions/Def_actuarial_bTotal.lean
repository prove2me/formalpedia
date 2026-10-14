-- Prove2me | Definitions.Def_actuarial_bTotal
-- name    : actuarial_bTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:04:35.709003+00:00
-- url     : https://prove2.me/theorems/c22ccb66-f32d-4177-91c8-24cd438af091
-- title:
--   Total finite lifetime-state probability
-- statement:
--   Total finite lifetime-state probability.
--
--   Mathematical relation:
--
--   $$
--   M_h=\sum_{k=0}^{h}p_k
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bTotal (h : ℕ) (p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k

end ActuarialAnnuities


