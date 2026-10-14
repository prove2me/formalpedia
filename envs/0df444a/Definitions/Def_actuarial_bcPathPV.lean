-- Prove2me | Definitions.Def_actuarial_bcPathPV
-- name    : actuarial_bcPathPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:29:03.478293+00:00
-- url     : https://prove2.me/theorems/9e146d0a-a205-4684-9c67-43c26126e361
-- title:
--   Actual realised discounted continuous annuity payments
-- statement:
--   Actual realised discounted continuous annuity payments. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   Z(T)=\int_a^{a+n}b(t)e^{-\rho t}E(t,T)\,dt
--   $$
--
--   Units: GBP per year and GBP discounted PV No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Actual realised discounted continuous annuity payments

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcEntitled

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcPathPV (a term g rho : ℝ) (b : ℝ → ℝ) (lifetime : ℝ) : ℝ := ∫ t in a..(a+term), b t * Real.exp (-rho*t) * bcEntitled a g t lifetime

end ActuarialAnnuitiesContinuous


