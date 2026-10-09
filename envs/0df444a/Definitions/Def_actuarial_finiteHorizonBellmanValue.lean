-- Prove2me | Definitions.Def_actuarial_finiteHorizonBellmanValue
-- name    : actuarial_finiteHorizonBellmanValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:08:22.605448+00:00
-- url     : https://prove2.me/theorems/c5b42291-1990-4c99-b765-8803ad4e069e
-- title:
--   Optimal finite-horizon backward Bellman value
-- statement:
--   Value with n decisions remaining, computed by backward induction from the terminal state payoff.
--
--   **Mathematical statement**
--
--   $$
--   V_0=h,\quad V_{n+1}=TV_n
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteStageBellmanMaximum
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteHorizonBellmanValue {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) :
  ℕ → S → ℝ
  | 0 => terminal
  | n + 1 => fun s =>
      finiteStageBellmanMaximum P reward v
        (finiteHorizonBellmanValue P reward v terminal n) s

end ActuarialValuation


