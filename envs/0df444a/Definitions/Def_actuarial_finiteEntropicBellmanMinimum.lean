-- Prove2me | Definitions.Def_actuarial_finiteEntropicBellmanMinimum
-- name    : actuarial_finiteEntropicBellmanMinimum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:33:13.316556+00:00
-- url     : https://prove2.me/theorems/ab960186-aa8a-493a-98f2-56f1c0799b46
-- title:
--   Minimum entropic one-step cost across finite admissible actions
-- statement:
--   The action operator chooses the smallest one-step entropic valuation over a finite and nonempty action type. This is a cost minimisation problem, in contrast to the earlier Markov mission's reward maximisation. The definition requires no particular action interpretation, although retention decisions motivate its insurance use.
--
--   **Mathematical statement**
--
--   $$
--   T_{\gamma,\beta}F(s)=\min_{a\in A}Q_{\gamma,\beta}(s,a;F)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicStageCost

namespace ActuarialValuation

noncomputable def finiteEntropicBellmanMinimum {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun a : A => finiteEntropicStageCost P cost beta gamma next s a)

end ActuarialValuation


