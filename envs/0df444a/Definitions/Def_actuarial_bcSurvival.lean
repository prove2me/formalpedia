-- Prove2me | Definitions.Def_actuarial_bcSurvival
-- name    : actuarial_bcSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:28:27.562137+00:00
-- url     : https://prove2.me/theorems/b42afcc1-ce00-45a3-aba8-71d312520ec8
-- title:
--   Survival probability derived from finite real-valued lifetime states
-- statement:
--   Survival probability derived from finite real-valued lifetime states. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   S(t)=\sum_k p_k I(T_k,t)
--   $$
--
--   Units: dimensionless survival indicator/probability or years depending on argument No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Survival probability derived from finite real-valued lifetime states

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcAlive

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

noncomputable def bcSurvival (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range (N+1), p k * bcAlive (life k) t

end ActuarialAnnuitiesContinuous


