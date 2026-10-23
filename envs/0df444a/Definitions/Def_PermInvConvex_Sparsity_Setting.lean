-- Prove2me | Definitions.Def_PermInvConvex_Sparsity_Setting
-- name    : PermInvConvex_Sparsity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:02.308993+00:00
-- url     : https://prove2.me/theorems/6f21aae1-2577-4fb7-94b3-5b891fdd4592
-- title:
--   §3, pp. 1, 6–7 — card, N^K (10), convex body, the induced norm ‖·‖c (14), problem (11), s(x), i_x, δ(x), u(x) (15)
-- statement:
--   Let $\|\cdot\|_s$ be a norm on $\mathbb R^n$ and $K$ a natural number. This file defines the objects of §3 of Kim, Tawarmalani and Richard.
--
--   1. $\operatorname{card}(x)$ is the number of nonzero components of $x$, and
--   $$N^K_{\|\cdot\|_s} = \{x \in \mathbb R^n \mid \|x\|_s \le 1,\ \operatorname{card}(x) \le K\}. \tag{10}$$
--   2. A **convex body** is a compact convex set with nonempty interior.
--   3. The induced norm $\|x\|_c = \inf\{t > 0 \mid x/t \in \operatorname{conv}(N^K_{\|\cdot\|_s})\}$, the gauge (14) of the convex hull of $N^K_{\|\cdot\|_s}$.
--   4. The feasible set of problem (11): vectors $u$ with $u_1 \ge \dots \ge u_K \ge 0$, $u_{K+1} = \dots = u_n = 0$ and $u \ge_{wm} |x|$.
--   5. For $i = 1, \dots, K$,
--   $$s(x)_i = \frac{\sum_{j=i}^{n} |x|_{[j]}}{K - i + 1};$$
--   $i_x$ is the smallest index in $\{1, \dots, K\}$ minimizing $s(x)_i$, and $\delta(x) = s(x)_{i_x}$.
--   6. The closed-form vector (15): $u(x)_i = |x|_{[i]}$ for $i < i_x$, $u(x)_i = \delta(x)$ for $i_x \le i \le K$, and $u(x)_i = 0$ for $i > K$.
--
--   The Sparsity Theorem says that $u(x)$ solves (11), and Theorem 3.1 that $\|x\|_c = \|u(x)\|_s$.
--
--   **Formalization Note** Lean index $i$ of a vector is the paper's $i+1$; $s(x)_i$ and $i_x$ keep the paper's 1-based index. The paper's conventions $s(x)_0 = s(x)_{K+1} = \infty$ only exclude $0$ and $K+1$ from the minimization, which the range $1 \le i \le K$ encodes; outside that range `sVal` is never used. $i_x$ is the infimum of the (nonempty, finite) set of minimizing indices. The paper writes $\min$ in (14); at $x = 0$ that minimum is not attained, so (14) is read as Mathlib's Minkowski `gauge`, an infimum. In (11), $u_K \ge 0$ is stated as $u_i \ge 0$ for all $i \le K$, which is equivalent given the chain.
-- source:
--   Kim, Tawarmalani, Richard, Convexification of Permutation-Invariant Sets and an Application to Sparse PCA, arXiv:1910.02573v2, p. 1 (card), p. 6 ((10), (11)), p. 7 (convex body, (14), s(x), i_x, δ(x), (15))

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization

namespace PermInvConvex.Sparsity

/-- `card(x)`, p. 1: the number of nonzero components of `x`. -/
noncomputable def card {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- The set (10), p. 6: `N^K_{‖·‖ₛ} = {x ∈ ℝⁿ | ‖x‖ₛ ≤ 1, card(x) ≤ K}`, for a norm given as the
function `ns`. -/
def NK {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (K : ℕ) : Set (Fin n → ℝ) :=
  {x | ns x ≤ 1 ∧ card x ≤ K}

/-- A convex body, p. 7: a compact convex set with nonempty interior. -/
def IsConvexBody {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ (interior C).Nonempty

/-- The norm `‖·‖_c` induced by `conv(N^K_{‖·‖ₛ})` through (14), p. 7:
`f_C(x) = inf {t > 0 | x / t ∈ C}` with `C = conv(N^K_{‖·‖ₛ})` (Mathlib's Minkowski `gauge`;
the paper writes `min`, which at `x = 0` is an infimum). -/
noncomputable def normC {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (K : ℕ) : (Fin n → ℝ) → ℝ :=
  gauge (convexHull ℝ (NK ns K))

/-- The feasible set of problem (11), p. 6:
`u₁ ≥ ⋯ ≥ u_K ≥ 0`, `u_{K+1} = ⋯ = uₙ = 0`, `u ≥_{wm} |x|`.
Index `i : Fin n` is the paper's `i + 1`; the chain is stated on the indices `< K`, and
`u_K ≥ 0` is stated as `uᵢ ≥ 0` for all of them (equivalent given the chain). -/
def Feas11 {n : ℕ} (K : ℕ) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {u | (∀ i j : Fin n, i ≤ j → (j : ℕ) < K → u j ≤ u i) ∧
    (∀ i : Fin n, (i : ℕ) < K → 0 ≤ u i) ∧
    (∀ i : Fin n, K ≤ (i : ℕ) → u i = 0) ∧
    WeakMajorizes u (absVec x)}

/-- `s(x)ᵢ = (∑_{j=i}^{n} |x|_{[j]}) / (K − i + 1)`, p. 7, with the paper's 1-based index
`i ∈ {1, …, K}` (used only there; the boundary values `s(x)₀ = s(x)_{K+1} = ∞` are encoded by
restricting every minimization to `1 ≤ i ≤ K`). -/
noncomputable def sVal {n : ℕ} (K : ℕ) (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ) + 1), decAbs x j) / ((K : ℝ) - i + 1)

/-- `iₓ`, p. 7: the smallest index among those `i ∈ {1, …, K}` minimizing `s(x)ᵢ`. -/
noncomputable def ix {n : ℕ} (K : ℕ) (x : Fin n → ℝ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ i ≤ K ∧ ∀ i' : ℕ, 1 ≤ i' → i' ≤ K → sVal K x i ≤ sVal K x i'}

/-- `δ(x) = s(x)_{iₓ}`, p. 7. -/
noncomputable def delta {n : ℕ} (K : ℕ) (x : Fin n → ℝ) : ℝ :=
  sVal K x (ix K x)

/-- The vector `u(x)` of (15), p. 7: `u(x)ᵢ = |x|_{[i]}` for `i ∈ {1, …, iₓ − 1}`,
`δ(x)` for `i ∈ {iₓ, …, K}`, `0` otherwise. Index `i : Fin n` is the paper's `i + 1`. -/
noncomputable def uVec {n : ℕ} (K : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) + 1 < ix K x then decAbs x i
    else if (i : ℕ) + 1 ≤ K then delta K x else 0

end PermInvConvex.Sparsity


