-- Prove2me | Definitions.Def_actuarial_bcGuaranteedPV
-- name    : actuarial_bcGuaranteedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:35:40.064195+00:00
-- url     : https://prove2.me/theorems/5daf3c14-9a12-4c96-853e-b95ad9cdb8e6
-- title:
--   Continuous guaranteed estate payments while activated
-- statement:
--   Continuous guaranteed estate payments while activated. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{guarantee}}=S(a)\int_a^{\min(a+n,a+g)}b(t)e^{-\rho t}\,dt
--   $$
--
--   Units: GBP per year and GBP discounted PV No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Continuous guaranteed estate payments while activated

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcSurvival

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcGuaranteedPV (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ) (a term g rho : ℝ) (b : ℝ → ℝ) : ℝ := ∫ t in a..(a+term), if t < a+g then b t * Real.exp (-rho*t) * bcSurvival N p life a else 0

end ActuarialAnnuitiesContinuous


