-- Prove2me | Definitions.Def_actuarial_bPathPV
-- name    : actuarial_bPathPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:12:28.559576+00:00
-- url     : https://prove2.me/theorems/3ce2fdcc-93d1-42e9-b9c2-62dc0ad9852c
-- title:
--   Realised discounted life-annuity cashflows
-- statement:
--   Realised discounted life-annuity cashflows.
--
--   Mathematical relation:
--
--   $$
--   Z_k=\sum_{a\le j<\min(h,a+n)}b_jv^{j+\delta}E_{a,g,\delta}(j,k)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bEntitlement

namespace ActuarialAnnuities

noncomputable def bPathPV (h a n g delta : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n then b j * v^(j+delta) * bEntitlement a g delta j k else 0

end ActuarialAnnuities


