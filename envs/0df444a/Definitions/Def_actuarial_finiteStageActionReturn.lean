-- Prove2me | Definitions.Def_actuarial_finiteStageActionReturn
-- name    : actuarial_finiteStageActionReturn
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:06:10.141519+00:00
-- url     : https://prove2.me/theorems/7e9ab8f0-04c7-40f3-a6bf-2c6b7741b7d4
-- title:
--   One-step discounted policy return
-- statement:
--   Immediate reward under a chosen action plus discounted, transition-weighted continuation.
--
--   **Mathematical statement**
--
--   $$
--   Q(s,a;U)=r(s,a)+v\sum_tP(s,a,t)U(t)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteStageActionReturn {S A : Type*} [Fintype S]
  (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S) (a : A) : ℝ :=
  reward s a + v * (∑ t : S, P s a t * next t)

end ActuarialValuation


