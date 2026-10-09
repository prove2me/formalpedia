-- Prove2me | Definitions.Def_actuarial_finiteEntropicStageCost
-- name    : actuarial_finiteEntropicStageCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:32:38.41318+00:00
-- url     : https://prove2.me/theorems/468e798a-d2c6-4d87-93f8-cd46ee9b57b4
-- title:
--   Conditional entropic valuation of annual insurer and continuation cost
-- statement:
--   The one-step insurer valuation applies the real logarithm to the conditional exponential moment and divides by the cost-risk-aversion parameter. The function is syntactically defined for every real gamma, but its actuarial risk interpretation requires gamma positive and a positive normalised transition moment.
--
--   **Mathematical statement**
--
--   $$
--   Q_{\gamma,\beta}(s,a;F)=\log M_{\gamma,\beta}(s,a;F)/\gamma
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicTransitionMoment

namespace ActuarialValuation

noncomputable def finiteEntropicStageCost {S A : Type*} [Fintype S]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A) : ℝ :=
  Real.log (finiteEntropicTransitionMoment P cost beta gamma next s a) / gamma

end ActuarialValuation


