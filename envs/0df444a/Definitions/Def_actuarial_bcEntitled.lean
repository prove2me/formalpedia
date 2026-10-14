-- Prove2me | Definitions.Def_actuarial_bcEntitled
-- name    : actuarial_bcEntitled
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:28:39.479981+00:00
-- url     : https://prove2.me/theorems/f9c3ec95-d33a-4cb3-9d2c-acfecaf6e784
-- title:
--   Guarantee activated at continuous commencement, or later survival
-- statement:
--   Guarantee activated at continuous commencement, or later survival. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   E(t,T)=\begin{cases}I(T,a),&t<a+g,\\I(T,t),&t\ge a+g,\end{cases}
--   $$
--
--   Units: GBP per year and GBP discounted PV No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Guarantee activated at continuous commencement, or later survival

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcAlive

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcEntitled (a g t lifetime : ℝ) : ℝ := if t < a+g then bcAlive lifetime a else bcAlive lifetime t

end ActuarialAnnuitiesContinuous


