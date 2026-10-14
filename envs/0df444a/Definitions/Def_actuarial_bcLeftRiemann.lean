-- Prove2me | Definitions.Def_actuarial_bcLeftRiemann
-- name    : actuarial_bcLeftRiemann
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:39:57.931713+00:00
-- url     : https://prove2.me/theorems/c6f26f6a-50b5-4222-ba32-63352d005d36
-- title:
--   Actual left-rectangle valuation of annualised payments
-- statement:
--   Actual left-rectangle valuation of annualised payments. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   R_m(f)=\frac1m\sum_{j=0}^{Hm-1}f(j/m)
--   $$
--
--   Units: dimensionless survival indicator/probability or years depending on argument No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 166. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Actual left-rectangle valuation of annualised payments

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcLeftRiemann (H m : ℕ) (f : ℝ → ℝ) : ℝ := ∑ j ∈ Finset.range (H*m), f ((j : ℝ)/(m : ℝ)) / (m : ℝ)

end ActuarialAnnuitiesContinuous


