-- Prove2me | Definitions.Def_actuarial_bcCertainPV
-- name    : actuarial_bcCertainPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:34:25.499351+00:00
-- url     : https://prove2.me/theorems/739ff6d4-cf5d-4e5f-a684-effa59bd9b47
-- title:
--   Continuous annuity certain paid at given rate
-- statement:
--   Continuous annuity certain paid at given rate. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{certain}}=\int_a^{a+n}b(t)e^{-\rho t}\,dt
--   $$
--
--   Units: GBP per year and GBP discounted PV No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Continuous annuity certain paid at given rate

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcCertainPV (a term rho : ℝ) (b : ℝ → ℝ) : ℝ := ∫ t in a..(a+term), b t * Real.exp (-rho*t)

end ActuarialAnnuitiesContinuous


