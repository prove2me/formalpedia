-- Prove2me | Definitions.Def_actuarial_bCertainPV
-- name    : actuarial_bCertainPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:16:06.641574+00:00
-- url     : https://prove2.me/theorems/123098bb-5699-40f3-9a90-c7605ac6ae42
-- title:
--   Annuity-certain without life contingency
-- statement:
--   Annuity-certain without life contingency.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{certain}}=\sum_{a\le j<\min(h,a+n)}b_jv^{j+\delta}
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 157, Deferred annuities (Chapter 5, section 5.8). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bCertainPV (h a n delta : ℕ) (v : ℝ) (b : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n then b j * v^(j+delta) else 0

end ActuarialAnnuities


