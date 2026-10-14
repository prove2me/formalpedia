-- Prove2me | Definitions.Def_actuarial_bExpectedPV
-- name    : actuarial_bExpectedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:12:45.46467+00:00
-- url     : https://prove2.me/theorems/5142b44c-f507-4abb-b47b-64b0b089dbe1
-- title:
--   Actuarial expectation of realised present value
-- statement:
--   Actuarial expectation of realised present value.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E Z=\sum_{k=0}^{h}p_kZ_k
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV

namespace ActuarialAnnuities

noncomputable def bExpectedPV (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (h+1), p k * bPathPV h a n g delta v b k

end ActuarialAnnuities


