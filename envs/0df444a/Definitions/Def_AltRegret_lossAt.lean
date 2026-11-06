-- Prove2me | Definitions.Def_AltRegret_lossAt
-- name    : AltRegret_lossAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:37.733737+00:00
-- url     : https://prove2.me/theorems/0f1695fa-3331-468d-959e-3aee73fd0ae0
-- title:
--   The loss vector $c_s$ of round $s$, with $c_0=\mathbf 0$
-- statement:
--   In online linear optimization over the probability simplex $\Delta_d$, the adversary chooses in each round $t\ge1$ a loss vector $c_t\in[-1,1]^d$. The paper sets the loss of round $0$ to the all-zero vector:
--   $$
--   c_0=\mathbf 0 .
--   $$
--   Given any sequence $(c_s)_{s\in\mathbb N}$ of vectors in $\mathbb R^d$, this definition returns $c_s$ for $s\ge1$ and $\mathbf 0$ for $s=0$, whatever value the sequence holds at index $0$.
--
--   Every other object of the mission (the effective cumulative loss, Algorithm 1, the alternating regret and the potential) reads the losses through this definition, so the convention $c_0=\mathbf 0$ is built in.
--
--   **Formalization Note** A loss sequence is a function `c : ℕ → Fin d → ℝ`; coordinate `i : Fin d` is the paper's coordinate $i+1\in[d]$.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2, p.6 ("We define c0 = 0 to be the all-0 vector.")

import Mathlib

namespace AltRegret

/-- **The loss vector of round `s`, with `c₀ = 0`.** Tao–Zheng, *Optimal Alternating Regret for
Online Learning and Games*, arXiv:2608.24731, §2, p.6: "We define `c₀ = 0` to be the all-0 vector.
In each iteration `t ≥ 1`, … the adversary adaptively chooses `c_t ∈ [−1, 1]^d`."

`lossAt c s` is `c_s` for `s ≥ 1` and the all-zero vector for `s = 0`.

**Formalization Note.** A loss sequence is a function `c : ℕ → Fin d → ℝ`; coordinate `i : Fin d`
is the paper's coordinate `i + 1 ∈ [d]`. The value `c 0` is ignored: every later definition reads
round `s` through `lossAt`, so `c₀ = 0` holds whatever `c 0` is. -/
def lossAt {d : ℕ} (c : ℕ → Fin d → ℝ) (s : ℕ) : Fin d → ℝ :=
  if s = 0 then 0 else c s

end AltRegret


