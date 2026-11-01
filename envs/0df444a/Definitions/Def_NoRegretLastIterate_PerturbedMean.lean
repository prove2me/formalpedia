-- Prove2me | Definitions.Def_NoRegretLastIterate_PerturbedMean
-- name    : NoRegretLastIterate_PerturbedMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:51.280995+00:00
-- url     : https://prove2.me/theorems/65163eb2-c773-49ea-8bc0-7ecf12547281
-- title:
--   Proposition 3.1, (3.3)/(3.5) — expectation of $f_t$ on a perturbed i.i.d. Bernoulli history
-- statement:
--   Fix a self-agnostic strategy $f$ of player 1, $q\in[0,1]$, a history length $m$, a block length $L$ and a symbol $b\in\{0,1\}$. Let $J'_1,\dots,J'_m$ be the random history whose first $L$ entries are i.i.d. Bernoulli$(q)$ and whose remaining entries all equal $b$. This file defines
--   $$
--   \mathbb E\big[f_{m+1}(J'_1,\dots,J'_m)\big]=\sum_{x\in\{0,1\}^m}\Big(\prod_{i=1}^m q^{x_i}(1-q)^{1-x_i}\Big)\,f_{m+1}\big(x_1,\dots,x_{\min(L,m)},b,\dots,b\big).
--   $$
--   With $b=1$ this is the expectation over the sequence $J'(k)$ of (3.3); with $b=0$ it is the one over $J''(k)$ of (3.5). It is the quantity Proposition 3.1 bounds.
--
--   **Formalization Note** The coordinates after position $L$ are summed out with total weight $1$, so the sum is the expectation over the i.i.d. block only. If $L\ge m$ nothing is replaced. In Lean the strategy at round index $m$ (paper round $m+1$) is applied.
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Proposition 3.1, (3.3) and (3.5), pp.9–10

import Mathlib
import Definitions.Def_NoRegretLastIterate_Strategy

namespace NoRegretLastIterate

/-- The probability of the action string `x ∈ {0,1}^m` under i.i.d. Bernoulli(`q`) coordinates:
`Π_i q^{x_i} (1 − q)^{1 − x_i}`. -/
noncomputable def bernProd (q : ℝ) {m : ℕ} (x : Fin m → Fin 2) : ℝ :=
  ∏ i, if x i = 1 then q else 1 - q

/-- arXiv:2012.02125v3, Proposition 3.1, (3.3) and (3.5), pp.9–10: the expectation
`E[F_m(J′_1, …, J′_m)]` of the self-agnostic strategy `F` at Lean round `m` on a history whose
first `L` entries are i.i.d. Bernoulli(`q`) and whose remaining entries all equal `b`
(`b = 1` for the sequence `J′` of (3.3), `b = 0` for `J″` of (3.5)).

**Formalization Note** The expectation is written as the finite sum over `x ∈ {0,1}^m` of the
i.i.d. Bernoulli(`q`) weight of `x` times `F_m` at the history that keeps `x_i` for `i < L` and
replaces it by `b` for `i ≥ L`; the coordinates `i ≥ L` sum out with total weight `1`. If
`L ≥ m` no entry is replaced. -/
noncomputable def perturbedMean (F : (n : ℕ) → (Fin n → Fin 2) → ℝ) (q : ℝ) (m L : ℕ)
    (b : Fin 2) : ℝ :=
  ∑ x : Fin m → Fin 2, bernProd q x * F m (fun i => if (i : ℕ) < L then x i else b)

end NoRegretLastIterate


