-- Prove2me | Definitions.Def_actuarial_bEntitlement
-- name    : actuarial_bEntitlement
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:05:03.431151+00:00
-- url     : https://prove2.me/theorems/d91b1635-5d47-497d-8dfb-5d76cc70dcf5
-- title:
--   Activated estate guarantee or later survival entitlement
-- statement:
--   Activated estate guarantee or later survival entitlement.
--
--   Mathematical relation:
--
--   $$
--   E_{a,g,\delta}(j,k)=\begin{cases}I_k(a),&j<a+g,\\I_k(j+\delta),&j\ge a+g,\end{cases}
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 159, Guaranteed annuities (Chapter 5, section 5.9). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive

namespace ActuarialAnnuities

noncomputable def bEntitlement (a g delta j k : ℕ) : ℝ := if j < a+g then bAlive k a else bAlive k (j+delta)

end ActuarialAnnuities


