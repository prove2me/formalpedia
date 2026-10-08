-- Prove2me | Definitions.Def_SongZipkinFluct_Monotone_Recursion
-- name    : SongZipkinFluct_Monotone_Recursion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:21.45332+00:00
-- url     : https://prove2.me/theorems/bba30e72-4887-4146-bc6b-ea1bbbd1f266
-- title:
--   §3, (10) and (13) — the value recursion W_n, G_n and the limits W_∞, G_∞
-- statement:
--   Fix a fixed order cost $K \ge 0$ and a terminal cost $W_0 : \mathbf I \times \mathbb Z \to \mathbb R$. For a function $W$ on $\mathbf I \times \mathbb Z$ define
--   $$(\mathcal G W)(i,y) = G^+(i,y) + \beta\lambda_i c + \beta\Big\{\lambda_i W(i,y-1) + \sum_{j\ne i} q_{ij} W(j,y) + (\mu - \lambda_i - q_i)\,W(i,y)\Big\}.$$
--   The $n$-stage optimal costs of the uniformized problem are given by the recursion (10): for $n \ge 1$,
--   $$G_n = \mathcal G W_{n-1}, \qquad W_n(i,x) = \min_{y \ge x}\{K\delta(y-x) + G_n(i,y)\}.$$
--   With $K = 0$ this is the recursion (13) of the linear order-cost model, and the paper takes $W_0 \equiv 0$ there. The infinite-horizon functions are the pointwise limits
--   $$W_\infty(i,x) = \lim_{n\to\infty} W_n(i,x), \qquad G_\infty(i,y) = \lim_{n\to\infty} G_n(i,y).$$
--   In §3.2 and §4.3 the function $G_\infty$ of the linear-cost model is called $G_0$.
--
--   The monotonicity results of §4 are statements about these functions and their minimizers.
--
--   **Formalization Note.** The minimum over $y \ge x$ is an infimum over integers $y \ge x$, and the limits are written as suprema over $n$. In the linear-cost model with $W_0 \equiv 0$, $W_n$ and $G_n$ are nondecreasing in $n$ and bounded (Lemma 4 and Theorem 1 of the paper), so the series, the infimum and the supremum are finite and the supremum is the limit. These are results of the paper, not hypotheses. `Gn K W₀ n` is defined for every $n$ but used only for $n \ge 1$.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 356, recursion (10); p. 357, (13) and Theorem 2(a)–(b); p. 358 (G₀)

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Model

namespace SongZipkinFluct.Monotone

namespace Model

variable {I : Type} (M : Model I)

/-- The right-hand side of `G` in the optimality equation (2) (p. 355) and of `G_n` in the
recursion (10) (p. 356), built from a continuation function `W`:
`G⁺(i, y) + βλ_i c + β{λ_i W(i, y − 1) + Σ_{j≠i} q_ij W(j, y) + (μ − λ_i − q_i) W(i, y)}`. -/
noncomputable def contG (W : I → ℤ → ℝ) (i : I) (y : ℤ) : ℝ :=
  M.Gplus i y + M.β * M.lam i * M.c
    + M.β * (M.lam i * W i (y - 1) + ∑' j : {j : I // j ≠ i}, M.Q i j * W j y
      + (M.μ - M.lam i - M.q i) * W i y)

/-- `W_n(i, x)`, the recursion (10) (p. 356) for a fixed cost `K` and a terminal cost `W₀`:
`W_0 = W₀` and `W_n(i, x) = min_{y ≥ x} {K δ(y − x) + G_n(i, y)}` for `n ≥ 1`.

**Formalization Note.** The minimum is the infimum over integers `y ≥ x`. It is a real `⨅`; that it
is finite and attained is a result of the paper (Lemma 4, p. 356; Theorem 1 (printed "Theorem 4"),
p. 357), not a hypothesis. -/
noncomputable def Wn (K : ℝ) (W₀ : I → ℤ → ℝ) : ℕ → I → ℤ → ℝ
  | 0 => W₀
  | n + 1 => fun i x => ⨅ y : {y : ℤ // x ≤ y}, K * δ ((y : ℤ) - x) + M.contG (Wn K W₀ n) i y

/-- `G_n(i, y) = contG W_{n−1} (i, y)` (recursion (10), p. 356; (13), p. 357 when `K = 0`).

**Formalization Note.** The paper defines `G_n` for `n ≥ 1` only; here `Gn K W₀ n` is
`contG (Wn K W₀ (n − 1))`, so `Gn K W₀ 0` is a value no statement uses. -/
noncomputable def Gn (K : ℝ) (W₀ : I → ℤ → ℝ) (n : ℕ) : I → ℤ → ℝ :=
  M.contG (M.Wn K W₀ (n - 1))

/-- `W_∞(i, x)`, the pointwise limit of `W_n(i, x)` (Theorem 2(a), p. 357), as `sup_n W_n(i, x)`.

**Formalization Note.** For `K = 0` and `W₀ ≡ 0`, `W_n` is nondecreasing in `n` and bounded
(Theorem 1(d) (printed "Theorem 4"), p. 357; Lemma 4, p. 356), so the supremum is the limit. -/
noncomputable def Winf (K : ℝ) (W₀ : I → ℤ → ℝ) (i : I) (x : ℤ) : ℝ :=
  ⨆ n : ℕ, M.Wn K W₀ n i x

/-- `G_∞(i, y)`, the pointwise limit of `G_n(i, y)`, `n ≥ 1` (Theorem 2(b), p. 357), as
`sup_{n ≥ 1} G_n(i, y)`.

**Formalization Note.** For `K = 0` and `W₀ ≡ 0`, `G_n` is nondecreasing in `n` and bounded
(Theorem 1(e) (printed "Theorem 4"), p. 357; Lemma 4, p. 356), so the supremum is the limit. In §3.2
and §4.3 this function (with `K = 0`, `W₀ ≡ 0`) is `G₀` (p. 358). -/
noncomputable def Ginf (K : ℝ) (W₀ : I → ℤ → ℝ) (i : I) (y : ℤ) : ℝ :=
  ⨆ n : ℕ, M.Gn K W₀ (n + 1) i y

end Model

end SongZipkinFluct.Monotone


