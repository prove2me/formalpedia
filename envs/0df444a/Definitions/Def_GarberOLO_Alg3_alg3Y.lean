-- Prove2me | Definitions.Def_GarberOLO_Alg3_alg3Y
-- name    : GarberOLO_Alg3_alg3Y
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:57:19.4668+00:00
-- url     : https://prove2.me/theorems/86a5c498-f1e4-493f-84f2-1bf3cd8d016d
-- title:
--   Points $\tilde y_t$ of Algorithm 3
-- statement:
--   Algorithm 3 (online gradient descent with infeasible projections) receives $\eta > 0$, $\varepsilon > 0$ and a point $s_1 \in K$, sets $\tilde y_1 = \alpha s_1$, and in round $t \ge 1$, after receiving $f_t$, sets
--   $$y_{t+1} = \begin{cases}\tilde y_t - \eta f_t & \alpha \ge 1,\\ \tilde y_t + \eta f_t & \alpha < 1,\end{cases}$$
--   and lets $\tilde y_{t+1}$ be the point returned by Algorithm 2 on $(y_{t+1}, \varepsilon)$.
--
--   The sequence $(\tilde y_t)$ does not depend on the points sampled for play.
--
--   **Formalization Note** Rounds are numbered from $1$; $f_0$ and the value at index $0$ are unused.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Algorithm 3, p. 14

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_alg2

namespace GarberOLO.Alg3

/-- **The points ỹ_t of Algorithm 3** (online gradient descent with infeasible projections).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Algorithm 3, p. 14: "1: input: learning rate η > 0, projection error parameter ε > 0 2: s₁ ← some point in K 3: ỹ₁ ← αs₁ 4: for t = 1 . . . T do 5: play s_t 6: receive loss/payoff vector f_t ∈ 𝓕 7: y_{t+1} ← ỹ_t − ηf_t if α ≥ 1; ỹ_t + ηf_t if α < 1 8: call Algorithm 2 with inputs (y_{t+1}, ε) to obtain an approximated projection ỹ_{t+1}, a distribution (a₁, …, a_N) and {(v₁, s₁), …, (v_N, s_N)} ⊆ ℝᵈ × K, for some N ∈ ℕ. 9: sample s_{t+1} ∈ {s₁, …, s_N} according to distribution (a₁, …, a_N) 10: end for".

`alg3Y S OK sel c s₁ η ε f t` is ỹ_t for `t ≥ 1`: `ỹ₁ = α s₁`, and
`ỹ_{t+1} = (alg2 S OK sel c ε y_{t+1}).yt` with `y_{t+1} = ỹ_t − η f_t` if `α ≥ 1` and
`ỹ_t + η f_t` if `α < 1`. The value at `t = 0` is not used (set to `α s₁`).

**Formalization Note.** Rounds are numbered from 1; `f t` is the vector of round `t`
(`f 0` is unused). The sequence ỹ does not depend on the sampled points (line 9), which only
determine what is played. -/
noncomputable def alg3Y {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ)
    (c : ℝ) (s₁ : EuclideanSpace ℝ (Fin d)) (η ε : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => S.α • s₁
  | 1 => S.α • s₁
  | t + 2 =>
    (alg2 S OK sel c ε
      (if 1 ≤ S.α then alg3Y S OK sel c s₁ η ε f (t + 1) - η • f (t + 1)
       else alg3Y S OK sel c s₁ η ε f (t + 1) + η • f (t + 1))).yt

end GarberOLO.Alg3


