-- Prove2me | Definitions.Def_actuarial_finiteEntropicPolicyValue
-- name    : actuarial_finiteEntropicPolicyValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:33:47.489965+00:00
-- url     : https://prove2.me/theorems/4e070fb2-9713-46b8-aee1-0b604ae4920a
-- title:
--   Remaining-horizon entropic cost for a fixed Markov policy
-- statement:
--   For each remaining-horizon length, a deterministic time-dependent Markov policy prescribes one action for each state. The value at horizon zero is terminal cost, and every positive horizon applies the entropic transition operator at the selected action to the previous-horizon value. Here policy index n denotes remaining years.
--
--   **Mathematical statement**
--
--   $$
--   J^\pi_0=h,\quad J^\pi_{n+1}(s)=Q_{\gamma,\beta}(s,\pi(n,s);J^\pi_n)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicStageCost

namespace ActuarialValuation

noncomputable def finiteEntropicPolicyValue {S A : Type*}
  [Fintype S] (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (policy : ℕ → S → A) :
  ℕ → S → ℝ
  | 0 => terminal
  | n + 1 => fun s =>
      finiteEntropicStageCost P cost beta gamma
        (finiteEntropicPolicyValue P cost beta gamma terminal policy n)
        s (policy n s)

end ActuarialValuation


