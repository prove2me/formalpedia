-- Prove2me | Definitions.Def_actuarial_bcExpectedPV
-- name    : actuarial_bcExpectedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:30:51.723855+00:00
-- url     : https://prove2.me/theorems/00ca73ed-4d85-4fc2-8858-c6a3998baeea
-- title:
--   Finite expected value of real-time realised PV random variable
-- statement:
--   Finite expected value of real-time realised PV random variable. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z]=\sum_kp_kZ(T_k)
--   $$
--
--   Units: GBP per year and GBP discounted PV No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Finite expected value of real-time realised PV random variable

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcPathPV

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcExpectedPV (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ) (a term g rho : ℝ) (b : ℝ → ℝ) : ℝ := ∑ k ∈ Finset.range (N+1), p k * bcPathPV a term g rho b (life k)

end ActuarialAnnuitiesContinuous


