-- Prove2me | Definitions.Def_AdWordsMSVV_Tradeoff_LP
-- name    : AdWordsMSVV_Tradeoff_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:57.097982+00:00
-- url     : https://prove2.me/theorems/72c841e7-3647-4224-8030-ebc7749f3b63
-- title:
--   §4–§5, pp. 8–12 — the factor-revealing LP L, its dual D, l = Aa, the optimal pair x*, y* and the tradeoff function ψ_k(i) = Σ_{j≥i} y*_j
-- statement:
--   This file fixes the **factor-revealing linear program** $L$ of §4 and its dual $D$, for $k$ slabs and $N$ bidders. All indices $i,j$ range over $1,\dots,k-1$.
--
--   The primal $L$ is
--   $$\max\ \Phi=\sum_{i=1}^{k-1}\frac{k-i}{k}x_i\quad\text{s.t.}\quad \sum_{j=1}^{i}\Bigl(1+\frac{i-j}{k}\Bigr)x_j\le\frac ik N,\quad x_i\ge0,$$
--   written $\max c\cdot x$ s.t. $Ax\le b$, $x\ge0$, with $A_{ij}=1+(i-j)/k$ for $j\le i$ and $0$ otherwise, $b_i=(i/k)N$ and $c_i=(k-i)/k$. The dual $D$ is
--   $$\min\ \sum_{i=1}^{k-1}\frac ik N y_i\quad\text{s.t.}\quad \sum_{j=i}^{k-1}\Bigl(1+\frac{j-i}{k}\Bigr)y_j\ge\frac{k-i}{k},\quad y_i\ge0.$$
--
--   The file also defines:
--   1. the optimal values $\mathrm{val}(L)$ (supremum of $c\cdot x$ over feasible $x$) and $\mathrm{val}(D)$ (infimum of $b\cdot y$ over feasible $y$);
--   2. the vector $l=Aa$ of §5, $l_i=\sum_{j\le i}A_{ij}a_j$, the right-hand side of the LP $L(\pi,\psi)$;
--   3. the explicit solutions of the proof of Lemma 3, $x^*_i=\frac Nk(1-\frac1k)^{i-1}$ and $y^*_i=\frac1k(1-\frac1k)^{k-i-1}$;
--   4. Theorem 8's tradeoff function
--   $$\psi_k(i)=\sum_{j=i}^{k-1}y^*_j .$$
--
--   The tradeoff function $\psi_k$ is the one the algorithm of Theorem 8 runs with; the LPs are the analysis that derives it.
--
--   **Formalization Note** Vectors are functions $\mathbb N\to\mathbb R$ read only on $1\le i\le k-1$; values elsewhere are never used. $\psi_k$ is defined by its sum, the ":=" part of Theorem 8. The closed form printed beside it, $1-(1-1/k)^{k-i+1}$, is off by one in the exponent: the sum equals $1-(1-1/k)^{k-i}$, which vanishes at $i=k$.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 8 (LPs L and D, x*, y*), p. 9 (L(π, ψ), l = Aa), p. 12 (Theorem 8, ψ_k)

import Mathlib

namespace AdWordsMSVV.Tradeoff

open Finset

/-! The factor-revealing LP `L` and its dual `D` of §4 (p. 8), with `k` slabs and `N` bidders.
Coordinates are `ℕ → ℝ`, read only on the paper's 1-based range `i ∈ [1, k-1]`. -/

/-- The constraint matrix `A` of `L`: `A i j = 1 + (i - j)/k` for `j ≤ i`, `0` otherwise. -/
noncomputable def Aent (k i j : ℕ) : ℝ := if j ≤ i then 1 + ((i : ℝ) - j) / k else 0

/-- The right-hand side `b` of `L`: `b_i = (i/k) N`. -/
noncomputable def bVec (k N i : ℕ) : ℝ := (i : ℝ) / k * N

/-- The objective `c` of `L`: `c_i = (k - i)/k`. -/
noncomputable def cVec (k i : ℕ) : ℝ := ((k : ℝ) - i) / k

/-- `l = A a` for a vector `a` (p. 9): `l_i = Σ_{j=1}^{i} A i j a_j`. -/
noncomputable def lVec (k : ℕ) (a : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ Icc 1 i, Aent k i j * a j

/-- Feasibility for `L`: `x_i ≥ 0` and `Σ_{j=1}^{i} (1 + (i-j)/k) x_j ≤ (i/k) N` for `1 ≤ i ≤ k-1`. -/
def PrimalFeasible (k N : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ i ∈ Icc 1 (k - 1), 0 ≤ x i) ∧
  ∀ i ∈ Icc 1 (k - 1), ∑ j ∈ Icc 1 i, Aent k i j * x j ≤ bVec k N i

/-- Feasibility for `D`: `y_i ≥ 0` and `Σ_{j=i}^{k-1} (1 + (j-i)/k) y_j ≥ (k-i)/k` for
`1 ≤ i ≤ k-1`. -/
def DualFeasible (k : ℕ) (y : ℕ → ℝ) : Prop :=
  (∀ i ∈ Icc 1 (k - 1), 0 ≤ y i) ∧
  ∀ i ∈ Icc 1 (k - 1), cVec k i ≤ ∑ j ∈ Icc i (k - 1), Aent k j i * y j

/-- The objective `Φ = c · x = Σ_{i=1}^{k-1} ((k-i)/k) x_i` of `L`. -/
noncomputable def primalObj (k : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ Icc 1 (k - 1), cVec k i * x i

/-- The objective `b · y = Σ_{i=1}^{k-1} (i/k) N y_i` of `D`. -/
noncomputable def dualObj (k N : ℕ) (y : ℕ → ℝ) : ℝ := ∑ i ∈ Icc 1 (k - 1), bVec k N i * y i

/-- The optimal value of `L`: the supremum of `c · x` over primal-feasible `x`. -/
noncomputable def LValue (k N : ℕ) : ℝ := sSup (primalObj k '' {x | PrimalFeasible k N x})

/-- The optimal value of `D`: the infimum of `b · y` over dual-feasible `y`. -/
noncomputable def DValue (k N : ℕ) : ℝ := sInf (dualObj k N '' {y | DualFeasible k y})

/-- The primal solution of the proof of Lemma 3 (p. 8): `x*_i = (N/k)(1 - 1/k)^{i-1}`. -/
noncomputable def xStar (k N : ℕ) (i : ℕ) : ℝ := (N : ℝ) / k * (1 - 1 / (k : ℝ)) ^ (i - 1)

/-- The dual solution of the proof of Lemma 3 (p. 8): `y*_i = (1/k)(1 - 1/k)^{k-i-1}`. -/
noncomputable def yStar (k : ℕ) (i : ℕ) : ℝ := 1 / (k : ℝ) * (1 - 1 / (k : ℝ)) ^ (k - i - 1)

/-- Theorem 8's tradeoff function (p. 12), by its defining sum: `ψ_k(i) := Σ_{j=i}^{k-1} y*_j`. -/
noncomputable def psi (k : ℕ) (i : ℕ) : ℝ := ∑ j ∈ Icc i (k - 1), yStar k j

end AdWordsMSVV.Tradeoff


