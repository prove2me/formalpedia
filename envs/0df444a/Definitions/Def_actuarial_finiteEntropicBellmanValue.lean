-- Prove2me | Definitions.Def_actuarial_finiteEntropicBellmanValue
-- name    : actuarial_finiteEntropicBellmanValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:35:22.899897+00:00
-- url     : https://prove2.me/theorems/771ee9ec-d594-4e0e-9f67-89789857994b
-- title:
--   Risk-sensitive finite-horizon Bellman value function
-- statement:
--   At zero years the cost is terminal reserve/loss. At an additional year, the optimiser compares all admissible actions using the risk-sensitive transition valuation of the preceding remaining-horizon optimal cost. The discount multiplier remains inside the exponential through the stage operator.
--
--   **Mathematical statement**
--
--   $$
--   V_0=h,\quad V_{n+1}(s)=\min_{a\in A}Q_{\gamma,\beta}(s,a;V_n)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanMinimum

namespace ActuarialValuation

noncomputable def finiteEntropicBellmanValue {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) :
  ℕ → S → ℝ
  | 0 => terminal
  | n + 1 => fun s =>
      finiteEntropicBellmanMinimum P cost beta gamma
        (finiteEntropicBellmanValue P cost beta gamma terminal n) s

end ActuarialValuation


