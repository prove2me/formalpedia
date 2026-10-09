-- Prove2me | Definitions.Def_SymPolyOpt_PowerSumLB_Setting
-- name    : SymPolyOpt_PowerSumLB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:30.514762+00:00
-- url     : https://prove2.me/theorems/2a71929b-88cd-4133-9969-98e67600ecf0
-- title:
--   (6.1), (6.4)–(6.5), pp. 24, 26 — power sums, the problem P_nmq, the Hankel matrix H_k(s), the SDP value L_nmq and the matrix J
-- statement:
--   Fix $n \in \mathbb N$ and a point $x = (x_1,\dots,x_n) \in \mathbb R^n$. The **power sum of order $j$** is
--   $$s_j(x) = \sum_{i=1}^{n} x_i^{\,j}, \qquad j \ge 0,$$
--   so that $s_0(x) = n$.
--
--   1. **The problem $\mathrm P_{nmq}$ (6.4).** Given $m, q \in \mathbb N$ and prescribed values $\gamma_1,\dots,\gamma_{m-1} \in \mathbb R$, the feasible set is $\{x \in \mathbb R^n : s_j(x) = \gamma_j,\ j = 1,\dots,m-1\}$, and the optimal value is
--   $$\min \mathrm P_{nmq} = \inf\Big\{ \sum_{i=1}^n x_i^{\,q} \;:\; s_j(x) = \gamma_j,\ j = 1,\dots,m-1 \Big\},$$
--   taken in the extended reals: $+\infty$ when the feasible set is empty, $-\infty$ when the objective is unbounded below on it.
--   2. **The Hankel matrix.** For a sequence $s = (s_0, s_1, \dots)$ of reals and $k \in \mathbb N$, $H_k(s) = (s_{i+j-2})_{1 \le i,j \le k}$ is the $k \times k$ matrix whose entries are constant along anti-diagonals.
--   3. **The SDP value $\mathrm L_{nmq}$ (6.5).**
--   $$\mathrm L_{nmq} = \inf_s \big\{ s_q \;:\; H_n(s) \succeq 0,\ s_0 = n,\ s_j = \gamma_j,\ j = 1,\dots,m-1 \big\},$$
--   again in the extended reals.
--   4. **$\gamma$ with $\gamma_0 = n$.** The sequence $\bar\gamma$ with $\bar\gamma_0 = n$ and $\bar\gamma_i = \gamma_i$ for $i \ge 1$, used in Theorem 6.6(b).
--   5. **The matrix $J$ (6.1) for the symmetric group.** With the fundamental invariants $\pi_j = \tfrac1j s_j$ ($1 \le j \le n$) viewed as polynomials in $X_1,\dots,X_n$, $J = \big(\sum_{k=1}^n \tfrac{\partial \pi_i}{\partial X_k}\tfrac{\partial \pi_j}{\partial X_k}\big)_{1 \le i,j \le n}$.
--
--   These objects are the data of Section 6.2: the paper bounds $\min \mathrm P_{nmq}$ from below by the SDP value $\mathrm L_{nmq}$, which only involves a Hankel matrix of size $n$.
--
--   **Formalization Note** Optimal values are infima in `EReal`, so they are $+\infty$ on an infeasible problem and may be $-\infty$ (e.g. $q$ odd). The prescribed vector $\gamma \in \mathbb R^{m-1}$ is a sequence $\gamma : \mathbb N \to \mathbb R$ of which only $\gamma_1,\dots,\gamma_{m-1}$ are read (the page's "$=\gamma_k$" in (6.4) is read as $\gamma_j$). The SDP variable is a sequence $s : \mathbb N \to \mathbb R$; its entries beyond $s_{2n-2}$ are unconstrained and do not change the value when $q \le 2n-2$. The Hankel matrix is 0-indexed, $H_k(s)_{ij} = s_{i+j}$ for $0 \le i,j < k$, which is the page's 1-indexed matrix. The pairing $\langle \partial p/\partial x_k, \partial q/\partial x_k\rangle$ of (6.1) is read, for the symmetric group, as the product of the partial derivatives (the standard Euclidean gradient pairing); $J$ is indexed $0,\dots,n-1$ for $\pi_1,\dots,\pi_n$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 24, (6.1); p. 26, (6.4), H_n(s), (6.5), Theorem 6.6(b) (γ_0 = n)

import Mathlib

namespace SymPolyOpt.PowerSumLB

variable {n : ℕ}

/-- The power sum `s_j(x) = ∑_{i=1}^n x_i^j` of order `j` of a point `x ∈ ℝⁿ`
(so `powerSum x 0 = n`). -/
def powerSum (x : Fin n → ℝ) (j : ℕ) : ℝ := ∑ i, x i ^ j

/-- The feasible set of (6.4): points `x ∈ ℝⁿ` with `s_j(x) = γ_j` for `j = 1, …, m − 1`. -/
def feasP (n m : ℕ) (γ : ℕ → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ j, 1 ≤ j → j ≤ m - 1 → powerSum x j = γ j}

/-- min P_nmq, as an infimum in EReal (+∞ if infeasible, −∞ if unbounded below). -/
noncomputable def minP (n m q : ℕ) (γ : ℕ → ℝ) : EReal :=
  ⨅ x ∈ feasP n m γ, ((powerSum x q : ℝ) : EReal)

/-- H_k(s) = (s_{i+j})_{0 ≤ i,j < k}, the page's (s_{i+j−2})_{1≤i,j≤k}. -/
def hankel (k : ℕ) (s : ℕ → ℝ) : Matrix (Fin k) (Fin k) ℝ := fun i j => s (i + j)

/-- The feasible set of (6.5): `H_n(s) ⪰ 0`, `s_0 = n`, `s_j = γ_j` for `j = 1, …, m − 1`. -/
def feasL (n m : ℕ) (γ : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {s | (hankel n s).PosSemidef ∧ s 0 = n ∧ ∀ j, 1 ≤ j → j ≤ m - 1 → s j = γ j}

/-- L_nmq, as an infimum in EReal. -/
noncomputable def valL (n m q : ℕ) (γ : ℕ → ℝ) : EReal :=
  ⨅ s ∈ feasL n m γ, ((s q : ℝ) : EReal)

/-- γ with γ₀ := n, as in "with γ_0 = n" of Theorem 6.6(b). -/
noncomputable def gammaExt (n : ℕ) (γ : ℕ → ℝ) : ℕ → ℝ := fun i => if i = 0 then (n : ℝ) else γ i

/-- The fundamental invariant `π_j = (1/j) s_j` of the symmetric group, as a polynomial. -/
noncomputable def piInv (n j : ℕ) : MvPolynomial (Fin n) ℝ :=
  (1 / (j : ℝ)) • MvPolynomial.psum (Fin n) ℝ j

/-- The matrix J of (6.1) for the invariants `π_1, …, π_n`, 0-based:
`J i j = ∑_k ∂π_{i+1}/∂x_k · ∂π_{j+1}/∂x_k`. -/
noncomputable def Jmat (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℝ) :=
  fun i j => ∑ k : Fin n,
    MvPolynomial.pderiv k (piInv n (i + 1)) * MvPolynomial.pderiv k (piInv n (j + 1))

end SymPolyOpt.PowerSumLB


