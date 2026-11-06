-- Prove2me | Definitions.Def_AltRegret_play
-- name    : AltRegret_play
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:04:56.063985+00:00
-- url     : https://prove2.me/theorems/0cb6343a-7c3a-4e7d-a152-a012e4fce051
-- title:
--   The play $x_t$ of alternation-aware Hedge (Algorithm 1)
-- statement:
--   The **alternation-aware Hedge** algorithm with parameters $(\eta,\beta)$ plays in round $t\ge1$ the vector $x_t\in\mathbb R^d$ with
--   $$
--   x_{t,i}=p_{t,i}\Big(1-\frac{c_{t-1,i}-\theta_t}{2}\Big),\qquad i\in[d],
--   $$
--   where $\theta_t$ is the maximizer of line 3 and $p_t$ the weights of line 4. Algorithm 1 of the paper is the case $\eta=1/8$, $\beta=1/32$.
--
--   The play of round $t$ depends only on $c_1,\dots,c_{t-1}$, so the algorithm is deterministic and non-anticipating. Lemma 1 shows $x_t\in\Delta_d$.
--
--   **Formalization Note** The loss $c_0$ is $\mathbf 0$ by `AltRegret.lossAt`. The value at $t=0$ is never used.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.1, p.6, Algorithm 1, lines 1–6

import Mathlib
import Definitions.Def_AltRegret_weights

namespace AltRegret

/-- **The play `x_t` of Algorithm 1 (alternation-aware Hedge).** Tao–Zheng, arXiv:2608.24731,
§2.1, p.6, Algorithm 1, line 5: "Play `x_t` such that `x_{t,i} = p_{t,i}(1 − (c_{t−1,i} − θ_t)/2)`."

`play η β c t i = p_{t,i} (1 − (c_{t−1,i} − θ_t)/2)` with `p_t = weights η β c t` and
`θ_t = theta η β c t`.

**Formalization Note.** The algorithm is parametrized by `(η, β)`: Algorithm 1 as printed is
`play (1/8) (1/32)` (line 1: "Set `L₀ = 0`, `η = 1/8`, and `β = 1/32`"). The play of round `t`
reads only `c₁, …, c_{t−1}` (through `L_{t−1}` and `c_{t−1}`), so the algorithm is deterministic
and non-anticipating; `c₀ = 0` is forced by `lossAt`. Rounds are `t ≥ 1`; the value at `t = 0` is
never read. -/
noncomputable def play {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  fun i => weights η β c t i * (1 - (lossAt c (t - 1) i - theta η β c t) / 2)

end AltRegret


