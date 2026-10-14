-- Prove2me | Definitions.Def_actuarial_bcProjectedPV
-- name    : actuarial_bcProjectedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:32:53.995176+00:00
-- url     : https://prove2.me/theorems/ed6ed14a-aaa9-4fce-8d13-ccdaa4e4fecc
-- title:
--   Survivor-projected continuous actuarial PV
-- statement:
--   Survivor-projected continuous actuarial PV. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   V=\int_a^{a+n}b(t)e^{-\rho t}[\mathbf1_{\{t<a+g\}}S(a)+\mathbf1_{\{t\ge a+g\}}S(t)]\,dt
--   $$
--
--   Units: GBP per year and GBP discounted PV No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Survivor-projected continuous actuarial PV

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcSurvival

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcProjectedPV (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ) (a term g rho : ℝ) (b : ℝ → ℝ) : ℝ := ∫ t in a..(a+term), b t * Real.exp (-rho*t) * (if t < a+g then bcSurvival N p life a else bcSurvival N p life t)

end ActuarialAnnuitiesContinuous


