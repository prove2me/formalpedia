-- Prove2me | Definitions.Def_actuarial_finiteEntropicTransitionMoment
-- name    : actuarial_finiteEntropicTransitionMoment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:31:48.15421+00:00
-- url     : https://prove2.me/theorems/63bd561d-5354-44e1-9c26-32789dba89c1
-- title:
--   State-and-action conditional exponential loss moment
-- statement:
--   Under each current state and selected action, the exponential moment averages the exponentiated one-year insurer cost and discounted continuation cost over the finite next-state transition kernel. Each next-state probability multiplies its own combined exponential. No normalisation is assumed by the definition itself.
--
--   **Mathematical statement**
--
--   $$
--   M_{\gamma,\beta}(s,a;F)=\sum_t P(s,a,t)e^{\gamma(c(s,a,t)+\beta F(t))}
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def finiteEntropicTransitionMoment {S A : Type*} [Fintype S]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ t : S, P s a t * Real.exp (gamma * (cost s a t + beta * next t))

end ActuarialValuation


