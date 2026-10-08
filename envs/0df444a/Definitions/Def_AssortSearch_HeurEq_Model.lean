-- Prove2me | Definitions.Def_AssortSearch_HeurEq_Model
-- name    : AssortSearch_HeurEq_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:21.964261+00:00
-- url     : https://prove2.me/theorems/bce6754e-f8d9-4a1a-94f3-6e088bea07a2
-- title:
--   Iterative no-search assortment planning under independent-assortment search: observed demands $d_i(x)$, estimates $\hat v(x)$, profits and heuristic equilibrium
-- statement:
--   A retailer can carry product variants $1,\dots,n$, labelled from most to least popular. Variant $i$ has **preference** $v_i>0$ and the no-purchase option ("variant 0") has preference $v_0>0$. An assortment of **depth** $x\in\{0,1,\dots,n\}$ is the set $\{1,\dots,x\}$ of the $x$ most popular variants. Variant $i$ has margin $m_i$, and carrying it at demand $q$ costs $c(q)$.
--
--   **True demand.** Consumers behave according to the independent assortment search model. With $\lambda>0$ the constant of Theorem 1 ($\lambda=\exp[-(\bar U/\mu+\gamma)]$) and
--   $$H(x)=\exp\Big(-\lambda\Big(v_0+\sum_{j=1}^{x}v_j\Big)\Big),$$
--   the observed demand of variant $i\le x$ is
--   $$d_i(x)=q_i^m(x)\,(1-H(x)),\qquad q_i^m(x)=\frac{v_i}{v_0+\sum_{j=1}^{x}v_j},$$
--   and the observed no-purchase demand is fixed by the normalisation $\sum_{i=0}^{x}d_i(x)=1$ (14), i.e. $d_0(x)=1-\sum_{i=1}^{x}d_i(x)$. The no-purchase share of the no-search model for inputted preferences $w,w_0$ is $q_0^m(x\mid w)=w_0/(w_0+\sum_{j\le x}w_j)$.
--
--   **Estimates.** From the sales of assortment $x\ge1$ the retailer estimates preferences by solving (14) together with $d_i(x)=\hat v_i(x)/\sum_{j=0}^{x}\hat v_j(x)$, $i\in[0,x]$, normalised by $\hat v_1(x)=1$. The solution is
--   $$\hat v_i(x)=\frac{d_i(x)}{d_1(x)}\ (1\le i\le x),\qquad \hat v_0(x)=\frac{d_0(x)}{d_1(x)},$$
--   and variants outside the assortment carry the depth-test estimates: $\hat v(x)=\{\hat v_0(x),\dots,\hat v_x(x),\hat v_{x+1}(n),\dots,\hat v_n(n)\}$.
--
--   **Profits.** The no-search model fed with preferences $w,w_0$ predicts the profit
--   $$\pi(x\mid w)=\sum_{i=1}^{x}\big(m_i\,q_i^m(x\mid w)-c(q_i^m(x\mid w))\big),\qquad q_i^m(x\mid w)=\frac{w_i}{w_0+\sum_{j\le x}w_j},$$
--   while the true profit is $\pi(x)=\sum_{i=1}^{x}\big(m_i d_i(x)-c(d_i(x))\big)$, formula (1).
--
--   **Heuristic equilibrium.** A depth $x^*$ with $1\le x^*\le n$ is a heuristic equilibrium when $\pi(x\mid\hat v(x^*))\le\pi(x^*\mid\hat v(x^*))$ for every $0\le x\le n$: the assortment is optimal given the estimated preferences, and the estimated preferences are those observed given the assortment. A depth $x^o\le n$ is an **optimal depth** when $\pi(x)\le\pi(x^o)$ for every $0\le x\le n$.
--
--   These are the objects of §3, §3.1 and §5.1 of the paper; Theorems 7 and 8 and the steps of their proofs are stated in terms of them.
--
--   **Formalization Note** Variants are `Fin n`, 0-based: the paper's variant $i$ is index $i-1$, depth $x$ is `popularSet n x` (indices $<x$) from the published `RetailVariety.Structure.Model`, and $q_i^m$ is its `share`. The no-purchase option is not a variant: $v_0$, $\hat v_0$ are separate reals. $\lambda$ is a free parameter (every real $\bar U$ gives some $\lambda>0$). The estimates are defined by the closed-form solution rather than as the solution of the linear system; `demandFirst` is $d_1(x)$, set to $0$ when $n=0$. The estimates are meaningful only for $1\le x\le n$, and the equilibrium excludes $x^*=0$, where nothing is observed.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 6 (PDF 8), (1); p. 7 (PDF 9), (2); p. 8 (PDF 10), Theorem 1, (3); pp. 19–20 (PDF 21–22), §5.1, (14), estimates and heuristic equilibrium; p. 23 (PDF 25), proof of Theorem 8 (x^o)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- No-purchase share of the no-search (MNL) model (2), p. 7, for an arbitrary preference vector:
`q_0^m(x | w, w_0) = w_0 / (∑_{j ≤ x} w_j + w_0)`, where the assortment is the depth `x`
(the `x` most popular variants, indices `< x`). With `w = v`, `w_0 = v_0` it is the paper's
`q_0^m(x)`; with `w = v̂(x*)`, `w_0 = v̂_0(x*)` it is `q_0^m(x | v̂(x*))`. -/
noncomputable def shareNoPurchase {n : ℕ} (w : Fin n → ℝ) (w0 : ℝ) (x : ℕ) : ℝ :=
  w0 / (∑ j ∈ popularSet n x, w j + w0)

/-- `v_0 + ∑_{j=1}^{x} v_j`, the total preference of the no-purchase option and of the
assortment of depth `x`. -/
noncomputable def prefTotal {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) : ℝ :=
  v0 + ∑ j ∈ popularSet n x, v j

/-- `H(Ū, x) = exp(−λ (v_0 + ∑_{j=1}^{x} v_j))` (Theorem 1, p. 8, with `S = {1, …, x}`): the
probability that a consumer searches in the independent assortment model. `lam` is Theorem 1's
`λ = exp[−(Ū/μ + γ)]`, taken as a free positive parameter. -/
noncomputable def searchH {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) : ℝ :=
  Real.exp (-(lam * prefTotal v v0 x))

/-- Observed demand of variant `i` with assortment `x` (§5.1, pp. 19–20), equal by the paper's
assumption to the expected demand of the independent assortment model, Theorem 1's (3):
`d_i(x) = q_i^si(x) = q_i^m(x) (1 − H(Ū, x))`. Meaningful for `i` in the assortment
(`i.val < x`). -/
noncomputable def demand {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) (i : Fin n) : ℝ :=
  share v v0 (popularSet n x) i * (1 - searchH lam v v0 x)

/-- Observed no-purchase demand with assortment `x`, fixed by the normalisation (14), p. 19:
`d_0(x) = 1 − ∑_{i=1}^{x} d_i(x)`. -/
noncomputable def demandNoPurchase {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) : ℝ :=
  1 - ∑ i ∈ popularSet n x, demand lam v v0 x i

/-- Observed demand `d_1(x)` of the paper's variant 1 (index `0`). It is `0` when `n = 0`, where
there is no variant 1. -/
noncomputable def demandFirst {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) : ℝ :=
  if h : 0 < n then demand lam v v0 x ⟨0, h⟩ else 0

/-- Estimated preference `v̂_i(x)` of variant `i` from the sales data of assortment `x`
(pp. 19–20). For `i` in the assortment it is `d_i(x) / d_1(x)`: this is the unique solution of
the paper's system — (14) together with `d_i(x) = v̂_i(x) / ∑_{j=0}^{x} v̂_j(x)`, `i ∈ [0, x]` —
normalised by `v̂_1(x) = 1`. For a variant outside the assortment the depth-test estimate is used:
`v̂(x) = {v̂_0(x), …, v̂_x(x), v̂_{x+1}(n), …, v̂_n(n)}`, i.e. `v̂_i(x) := v̂_i(n) = d_i(n)/d_1(n)`.
Meaningful for `1 ≤ x ≤ n`. -/
noncomputable def estPref {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) (i : Fin n) : ℝ :=
  if i.val < x then demand lam v v0 x i / demandFirst lam v v0 x
  else demand lam v v0 n i / demandFirst lam v v0 n

/-- Estimated preference `v̂_0(x) = d_0(x) / d_1(x)` of the no-purchase variant from the sales
data of assortment `x` (pp. 19–20), the no-purchase component of the same normalised solution.
Meaningful for `1 ≤ x ≤ n`. -/
noncomputable def estPrefNoPurchase {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) : ℝ :=
  demandNoPurchase lam v v0 x / demandFirst lam v v0 x

/-- Profit of the assortment of depth `x` according to the no-search (MNL) model with inputted
preferences `w`, `w_0` ((1), p. 6, with (2), p. 7):
`π(x | w) = ∑_{i=1}^{x} (m_i q_i^m(x | w) − c(q_i^m(x | w)))`,
`q_i^m(x | w) = w_i / (∑_{j ≤ x} w_j + w_0)`. With `w = v̂(x*)` it is `π(x | v̂(x*))`. -/
noncomputable def estProfit {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (w : Fin n → ℝ) (w0 : ℝ)
    (x : ℕ) : ℝ :=
  ∑ i ∈ popularSet n x, (m i * share w w0 (popularSet n x) i - c (share w w0 (popularSet n x) i))

/-- True expected profit `π(x) = ∑_{i=1}^{x} (m_i d_i(x) − c(d_i(x)))` of the assortment of
depth `x` in the independent assortment model ((1), p. 6, with Theorem 1's (3)). -/
noncomputable def trueProfit {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ)
    (v0 : ℝ) (x : ℕ) : ℝ :=
  ∑ i ∈ popularSet n x, (m i * demand lam v v0 x i - c (demand lam v v0 x i))

/-- Heuristic equilibrium of the iterative no-search assortment planning process (p. 20):
an assortment `x*` with `1 ≤ x* ≤ n` that is optimal, among the depths `0, …, n`, for the
no-search model fed with the preferences `v̂(x*)` estimated from `x*` itself, i.e.
`x* = x(v̂*)` and `v̂* = v̂(x*)`. The depth `x* = 0` is excluded: with no variant offered nothing
is observed and `v̂(0)` is undefined. -/
def IsHeuristicEquilibrium {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ)
    (v0 : ℝ) (xstar : ℕ) : Prop :=
  1 ≤ xstar ∧ xstar ≤ n ∧
    ∀ x : ℕ, x ≤ n →
      estProfit m c (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar) x ≤
        estProfit m c (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar) xstar

/-- `x^o` is an optimal assortment of the independent assortment model among the depths
`0, …, n` (proof of Theorem 8, p. 23: `π(x^o) = max_{0 ≤ x ≤ n} π(x)`). -/
def IsOptimalDepth {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (xo : ℕ) : Prop :=
  xo ≤ n ∧ ∀ x : ℕ, x ≤ n → trueProfit lam m c v v0 x ≤ trueProfit lam m c v v0 xo

end AssortSearch.HeurEq


