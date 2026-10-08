-- Prove2me | Definitions.Def_SongZipkinFluct_FixedCost_Recursion
-- name    : SongZipkinFluct_FixedCost_Recursion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:37.914985+00:00
-- url     : https://prove2.me/theorems/3232347a-2b16-416c-8845-0619811636fd
-- title:
--   (10) — the value iterates W_n, G_n; the linear-model limits W₀ = W_∞, G₀ = G_∞; the fixed-cost iterates and their limits
-- statement:
--   For a fixed order cost $K \ge 0$ and a terminal cost $W_0 : I \times \mathbb Z \to \mathbb R$, the $n$-stage problem of the uniformized model is solved by the recursion (10): for $n \ge 1$,
--   $$
--   W_n(i, x) = \min_{y \ge x}\{K\delta(y - x) + G_n(i, y)\},
--   $$
--   $$
--   G_n(i, y) = G^+(i, y) + \beta\lambda_i c + \beta\Big\{\lambda_i W_{n-1}(i, y-1) + \sum_{j \ne i} q_{ij} W_{n-1}(j, y) + (\mu - \lambda_i - q_i) W_{n-1}(i, y)\Big\}.
--   $$
--   The same right-hand side with $W_{n-1}$ replaced by $W$ is the $G$ of the optimality equation (2).
--
--   **The linear model** ($K = 0$, $W_0 \equiv 0$, §3.1) has limits
--   $$
--   W^{\mathrm{lin}}_\infty(i, x) = \sup_n W_n(i, x),\qquad G^{\mathrm{lin}}_\infty(i, y) = \sup_{n \ge 1} G_n(i, y).
--   $$
--   **The fixed-cost model** (§3.2) takes the model's discounted fixed cost $K = \bar K \tilde F_L(\alpha)$ and the terminal cost $W_0 = W^{\mathrm{lin}}_\infty$; correspondingly $G_0 = G^{\mathrm{lin}}_\infty$. Its iterates are written $W_n$, $G_n$ and their limits
--   $$
--   W_\infty(i, x) = \sup_n W_n(i, x),\qquad G_\infty(i, y) = \sup_{n\ge1} G_n(i, y).
--   $$
--
--   These are the objects about which every theorem of the mission is stated.
--
--   **Formalization Note** The minimum in (10) is written as an infimum over the integers $y \ge x$, and the series over $j \ne i$ as a `tsum`. Under the standing hypotheses and Assumption 1 ($\alpha\bar c < p$) the iterates are nonnegative and bounded by a nondecreasing function of $x$ (Lemma 4), so the series converge, the infimum is of a set of nonnegative reals, and the suprema over $n$ are finite; since the iterates are nondecreasing in $n$ (Theorem 1(d), (e) of the paper for the linear model, Theorem 3(d), (e) for the fixed-cost model), the suprema are the pointwise limits. The Lean index of $G_n$ is the paper's; $G_n$ is only used at $n \ge 1$.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 356, (10); p. 357, (13); p. 358, §3.2; p. 359, Theorem 5(a), (b)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Model

namespace SongZipkinFluct.FixedCost

open Model

variable {I : Type*} [DecidableEq I]

/-- The right-hand side of `G_n` in the recursion (10) (p. 356), built from a continuation
`Wc` (playing the role of `W_{n−1}`):
`G⁺(i, y) + βλ_i c + β{λ_i Wc(i, y − 1) + Σ_{j≠i} q_ij Wc(j, y) + (μ − λ_i − q_i) Wc(i, y)}`.
With `Wc = W` it is the `G` of the optimality equation (2) (p. 355).

Formalization Note: the series over `j ≠ i` is a `tsum`; it converges whenever `Wc` is bounded
in the world state at fixed `y`, which Lemma 4 (p. 356) guarantees for the iterates. -/
noncomputable def contG (M : Model I) (Wc : I → ℤ → ℝ) (i : I) (y : ℤ) : ℝ :=
  M.Gplus i y + M.β * M.lam i * M.c
    + M.β * (M.lam i * Wc i (y - 1) + (∑' j, if j = i then 0 else M.Q i j * Wc j y)
      + (M.μ - M.lam i - M.qrate i) * Wc i y)

/-- The value iterates `W_n` of the recursion (10) (p. 356), for a fixed order cost `K` and a
terminal cost `W₀`: `W_0 = W₀` and
`W_{n}(i, x) = inf_{y ≥ x} {Kδ(y − x) + G_{n}(i, y)}` with `G_n = contG W_{n−1}`.

Formalization Note: the paper writes `min`; the infimum is over the integers `y ≥ x`. Under the
standing hypotheses, Assumption 1 (`αc̄ < p`) and a terminal cost satisfying (11), it is the
infimum of a set of nonnegative reals (Lemma 4 and Theorem 3(e)), hence finite. -/
noncomputable def W (M : Model I) (K : ℝ) (W₀ : I → ℤ → ℝ) : ℕ → I → ℤ → ℝ
  | 0 => W₀
  | n + 1 => fun i x => ⨅ y : {y : ℤ // x ≤ y}, K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (W M K W₀ n) i y.1

/-- `G_n = contG W_{n−1}` of the recursion (10) (p. 356).

Formalization Note: the paper defines `G_n` for `n ≥ 1` only; the Lean index is that of the
paper, `G M K W₀ n = G_n`, and every statement uses it at `n ≥ 1` only (at `n = 0` the
truncated subtraction gives `contG W₀`). -/
noncomputable def G (M : Model I) (K : ℝ) (W₀ : I → ℤ → ℝ) (n : ℕ) : I → ℤ → ℝ :=
  contG M (W M K W₀ (n - 1))

/-- `W_∞` of the linear order-cost model (§3.1, p. 357: `K = 0`, `W₀ ≡ 0`):
`Wlin(i, x) = sup_n W_n(i, x)`.

Formalization Note: the iterates are nondecreasing in `n` (Theorem 1(d), printed "Theorem 4",
p. 357) and bounded (Lemma 4, p. 356), so the supremum is the pointwise limit of Theorem 2(a)
(p. 357). This is the terminal cost `W₀` of the fixed-cost model of §3.2 (p. 358). -/
noncomputable def Wlin (M : Model I) (i : I) (x : ℤ) : ℝ := ⨆ n : ℕ, W M 0 0 n i x

/-- `G_∞` of the linear order-cost model, `Glin(i, y) = sup_{n ≥ 1} G_n(i, y)` (`K = 0`, `W₀ ≡ 0`):
the `G₀` of §3.2 (p. 358). Nondecreasing in `n` by Theorem 1(e) (p. 357), bounded by Lemma 4. -/
noncomputable def Glin (M : Model I) (i : I) (y : ℤ) : ℝ := ⨆ n : ℕ, G M 0 0 (n + 1) i y

/-- The fixed-cost iterates of §3.2 (p. 358): `W_n` of (10) with the model's discounted fixed
cost `K = K̄ F̃_L(α)` and terminal cost `W₀ = Wlin`. -/
noncomputable def Wfix (M : Model I) (n : ℕ) : I → ℤ → ℝ := W M M.K (Wlin M) n

/-- The fixed-cost `G_n` of §3.2 (p. 358), `n ≥ 1`. -/
noncomputable def Gfix (M : Model I) (n : ℕ) : I → ℤ → ℝ := G M M.K (Wlin M) n

/-- `W_∞` of the fixed-cost model, `sup_n W_n(i, x)` (Theorem 5(a), p. 359): nondecreasing in
`n` by Theorem 3(d), bounded by Lemma 4. -/
noncomputable def WinfK (M : Model I) (i : I) (x : ℤ) : ℝ := ⨆ n : ℕ, Wfix M n i x

/-- `G_∞` of the fixed-cost model, `sup_{n ≥ 1} G_n(i, y)` (Theorem 5(b), p. 359): nondecreasing
in `n` by Theorem 3(e), bounded by Lemma 4. -/
noncomputable def GinfK (M : Model I) (i : I) (y : ℤ) : ℝ := ⨆ n : ℕ, Gfix M (n + 1) i y

end SongZipkinFluct.FixedCost


