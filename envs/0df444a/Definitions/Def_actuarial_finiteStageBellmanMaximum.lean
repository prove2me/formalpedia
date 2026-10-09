-- Prove2me | Definitions.Def_actuarial_finiteStageBellmanMaximum
-- name    : actuarial_finiteStageBellmanMaximum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:06:47.796885+00:00
-- url     : https://prove2.me/theorems/aafc4de6-aff4-45cf-a387-af6467edde4f
-- title:
--   Bellman one-step maximum over finite actions
-- statement:
--   Attained maximum one-step discounted reward over the nonempty finite admissible action type.
--
--   **Mathematical statement**
--
--   $$
--   (TU)(s)=\max_a Q(s,a;U)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteStageBellmanMaximum {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : A => finiteStageActionReturn P reward v next s a)

end ActuarialValuation


