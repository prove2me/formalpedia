-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_infReward
-- name    : EffHorizonProphet_Supplement_infReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:56:59.709492+00:00
-- url     : https://prove2.me/theorems/ea21e2d4-2b75-4996-8d6d-478d0e340a7c
-- title:
--   Geometrically discounted reward $X_i=\tilde\gamma^{i-1}Y_i$
-- statement:
--   In the infinite-horizon model the reward at stage $i\ge1$ is $X_i=\tilde\gamma^{i-1}Y_i$.
--
--   **Formalization Note** Stages are numbered from $0$, so the Lean reward at stage $i$ is $\tilde\gamma^{i}Y$, the paper's $X_{i+1}$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 7, p.11

import Mathlib

namespace EffHorizonProphet.Supplement

/-- The **geometrically discounted reward** `X_i = γ̃^{i−1} Y_i` of the infinite-horizon model
(Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 7, p.11).

**Formalization Note** `0`-based: stage `i : ℕ` here is the paper's stage `i + 1`, so the
reward is `γ^i · Y`, with `Y` the first component of the stage pair. -/
def infReward (γ : ℝ) (i : ℕ) (ω : ℕ → ℝ × unitInterval) : ℝ :=
  γ ^ i * (ω i).1

end EffHorizonProphet.Supplement


