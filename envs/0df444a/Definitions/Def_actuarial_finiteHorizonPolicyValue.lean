-- Prove2me | Definitions.Def_actuarial_finiteHorizonPolicyValue
-- name    : actuarial_finiteHorizonPolicyValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:07:25.197976+00:00
-- url     : https://prove2.me/theorems/5c6a8bcf-5e96-4831-bd1a-74284076623c
-- title:
--   Finite deterministic nonstationary Markov policy value
-- statement:
--   Expected discounted policy reward indexed by remaining horizon. Policy at n stages remaining chooses an action at depth n-1.
--
--   **Mathematical statement**
--
--   $$
--   V^\pi_0=h,\quad V^\pi_{n+1}(s)=Q(s,\pi_n(s);V^\pi_n)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteHorizonPolicyValue {S A : Type*}
  [Fintype S] (P : S → A → S → ℝ)
  (reward : S → A → ℝ) (v : ℝ)
  (terminal : S → ℝ) (policy : ℕ → S → A) :
  ℕ → S → ℝ
  | 0 => terminal
  | n + 1 => fun s =>
      finiteStageActionReturn P reward v
        (finiteHorizonPolicyValue P reward v terminal policy n)
        s (policy n s)

end ActuarialValuation


