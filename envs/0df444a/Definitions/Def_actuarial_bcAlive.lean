-- Prove2me | Definitions.Def_actuarial_bcAlive
-- name    : actuarial_bcAlive
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:28:08.832621+00:00
-- url     : https://prove2.me/theorems/f6471de6-b38a-4d14-b215-e5980998ef2c
-- title:
--   Real-time survival event
-- statement:
--   Real-time survival event. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   I(T,t)=\mathbf1_{\{T\ge t\}}
--   $$
--
--   Units: dimensionless survival indicator/probability or years depending on argument No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Real-time survival event

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcAlive (lifetime t : ℝ) : ℝ := if t ≤ lifetime then 1 else 0

end ActuarialAnnuitiesContinuous


