-- Prove2me | Definitions.Def_DynAssortPers_TypeDist_Estimator
-- name    : DynAssortPers_TypeDist_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:14:58.485385+00:00
-- url     : https://prove2.me/theorems/0906efaf-4f7a-445c-8df5-9508d082ed42
-- title:
--   Sec. 3.2.1 and proof of Theorem 4 — empirical type frequencies $\hat\mu_i=\frac1N\sum_t\mathbb I[i_t=i]$ and the empirical Rademacher complexity $\widehat{\mathfrak R}_N$
-- statement:
--   Let $i_1,\dots,i_N\in\{1,\dots,m\}$ be the observed customer types. This module defines the following.
--
--   1. The **empirical type frequencies** (Sec. 3.2.1, p. 14), the estimator of the customer type distribution $\mu^\star$:
--   $$\hat\mu_i=\frac1N\sum_{t=1}^N\mathbb I[i_t=i],\qquad i=1,\dots,m.$$
--   2. **Rademacher signs**: a sign vector $\epsilon\in\{-1,+1\}^N$, each sign coded by a boolean ($\text{true}\mapsto+1$, $\text{false}\mapsto-1$).
--   3. The **empirical Rademacher complexity** (proof of Theorem 4, p. 44): with $I_t=e_{i_t}$ the indicator vector of the $t$-th observed type,
--   $$\widehat{\mathfrak R}_N=\frac1{2^N}\sum_{\epsilon\in\{-1,+1\}^N}\ \sup_{\|v\|_\infty\le 1}\ \frac1N\sum_{t=1}^N\epsilon_t\,v^TI_t ,$$
--   where the supremum is over $v\in\mathbb R^m$ with $|v_i|\le1$ for all $i$, and $v^TI_t=v_{i_t}$.
--
--   $\hat\mu$ is the estimator whose accuracy Theorem 4 quantifies, and $\widehat{\mathfrak R}_N$ is the complexity the proof of Theorem 4 uses to control its $\ell_1$ error.
--
--   **Formalization Note** Types are `Fin m` and draws `Fin N`, 0-based (Lean index $i$ is the paper's $i+1$). $\hat\mu$ is defined with real division by $N$; at $N=0$ Lean returns $0$, and every theorem of the mission assumes $N\ge1$, where the paper's formula is meant. The supremum is a real `⨆` over the subtype of vectors in the unit $\ell_\infty$ ball; that index set is nonempty (it contains $0$) and the objective is bounded by $1$ in absolute value, so the supremum is the true one and not Lean's default value. Only the types $i_t$ enter; the items and assortments $(j_t,S_t)$ of the observation model play no role here.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Sec. 3.2.1, p. 14 (μ̂); proof of Theorem 4, p. 44 (definition of ℜ̂_N)

import Mathlib

namespace DynAssortPers.TypeDist

open Finset

/-- The empirical frequency estimator of Kallus–Udell, Sec. 3.2.1, p. 14:
`μ̂_i = (1/N) ∑_{t=1}^N 𝕀[i_t = i]` for the observed types `i_t = x t`. Types are `Fin m` and draws
are `Fin N`, both 0-based. -/
noncomputable def muHat {m N : ℕ} (x : Fin N → Fin m) (i : Fin m) : ℝ :=
  ((univ.filter (fun t => x t = i)).card : ℝ) / N

/-- A Rademacher sign: `true ↦ +1`, `false ↦ −1`. A sign vector `ε ∈ {−1, +1}^N` is a map
`Fin N → Bool`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The empirical Rademacher complexity of Kallus–Udell, proof of Theorem 4, p. 44:
`ℜ̂_N = (1/2^N) ∑_{ε ∈ {−1,+1}^N} sup_{‖v‖_∞ ≤ 1} (1/N) ∑_{t=1}^N ε_t vᵀ I_t`,
where `I_t = e_{i_t}` is the indicator vector of the observed type, so `vᵀ I_t = v (x t)`. The
supremum runs over the vectors `v ∈ ℝ^m` with `|v_i| ≤ 1` for every `i` (a nonempty set on which
the objective is bounded by `1`). -/
noncomputable def radHat {m N : ℕ} (x : Fin N → Fin m) : ℝ :=
  (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
    ⨆ v : {v : Fin m → ℝ // ∀ i, |v i| ≤ 1}, (1 / N : ℝ) * ∑ t, sgn (ε t) * v.1 (x t)

end DynAssortPers.TypeDist


