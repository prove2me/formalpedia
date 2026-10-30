-- Prove2me | Definitions.Def_SturtRobustStop_Structure_Model
-- name    : SturtRobustStop_Structure_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:10:03.874073+00:00
-- url     : https://prove2.me/theorems/4a3a193e-1c71-41ac-a746-af5adde18ae4
-- title:
--   Real trajectories, robust instance data, and full-path nonnegative rewards
-- statement:
--   The state space is $X=\mathbb R^d$ and a path has $T$ states. An instance has positive horizon $T$, positive sample size $N$, arbitrary paths $x^1,\ldots,x^N\in X^T$, radius $\epsilon\ge0$, and arbitrary finite nonnegative rewards $g(t,x)$ for finite periods and full trajectories. Extend $g(\infty,x)=0$. Rewards may depend on past and future path coordinates; there is no continuity, global boundedness, or current-state-only restriction.
--
--   The instance is deterministic after samples are realized. The policy interface is imported separately. Lean uses Fin T and Fin N with index k corresponding to k+1, finite rewards in NNReal, and Option for finite/infinite stopping. Dimension zero is admitted in addition to positive dimensions.
-- source:
--   Bradley Sturt, A Nonparametric Algorithm for Optimal Stopping Based on Robust Optimization, arXiv:2103.03300v4, §2.1–2.2, states, rewards, samples and radius, printed p. 7, PDF p. 7. https://arxiv.org/abs/2103.03300v4

import Definitions.Def_SturtRobustStop_Structure_Policy

open scoped NNReal

namespace SturtRobustStop.Structure

abbrev State (d : ℕ) := Fin d → ℝ
abbrev Path (T d : ℕ) := Fin T → State d

/-- Deterministic data of (RO), §2.1–2.2, pp.6–7. Finite rewards may depend
on the entire original trajectory. No global bound or regularity is imposed. -/
structure Model (T N d : ℕ) where
  horizon_pos : 0 < T
  sample_pos : 0 < N
  sample : Fin N → Path T d
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  reward : Fin T → Path T d → ℝ≥0

/-- Extend the finite-time reward by the prescribed zero value at ∞. -/
def Model.payoff {T N d : ℕ} (D : Model T N d) (τ : Option (Fin T))
    (x : Path T d) : ℝ≥0 :=
  match τ with
  | none => 0
  | some t => D.reward t x

end SturtRobustStop.Structure


