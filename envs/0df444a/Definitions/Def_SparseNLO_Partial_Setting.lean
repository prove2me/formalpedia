-- Prove2me | Definitions.Def_SparseNLO_Partial_Setting
-- name    : SparseNLO_Partial_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:11:46.504992+00:00
-- url     : https://prove2.me/theorems/8506741f-a202-458d-a0c6-6ad71bee450d
-- title:
--   Problem (P): ‖x‖₀, I₁(x), I₀(x), C_s, M_s(x), the local Lipschitz condition (2.15), the projection P_{C_s} and L-stationarity (Def. 2.3)
-- statement:
--   These are the objects of the sparsity constrained problem
--   $$(\mathrm P)\qquad \min\ f(x)\quad\text{s.t.}\quad \|x\|_0\le s,$$
--   where $f:\mathbb R^n\to\mathbb R$ is continuously differentiable and $0<s<n$ is an integer.
--
--   1. The **$\ell_0$ norm** $\|x\|_0$ is the number of nonzero components of $x$. The **support** is $I_1(x)=\{i : x_i\neq 0\}$ and its complement is $I_0(x)=\{i : x_i=0\}$. The feasible set is $C_s=\{x : \|x\|_0\le s\}$.
--   2. $M_s(x)$ is the $s$-th largest of the absolute values $|x_1|,\dots,|x_n|$, counted with multiplicity, so that $M_1(x)\ge M_2(x)\ge\dots\ge M_n(x)$. In particular $M_s(x)=0$ exactly when $\|x\|_0<s$.
--   3. A constant $L_2$ satisfies the **local Lipschitz condition (2.15)** for $f$ if for all $i\neq j$, all $x$, and all $d$ whose nonzero components lie in $\{i,j\}$,
--   $$\big\|\nabla_{i,j}f(x)-\nabla_{i,j}f(x+d)\big\|\le L_2\,\|d\|,$$
--   where $\nabla_{i,j}f(x)=(\nabla_i f(x),\nabla_j f(x))\in\mathbb R^2$. The paper's local Lipschitz constant $L_2(f)=\max_{i\ne j}L_{i,j}(f)$ satisfies it.
--   4. The **orthogonal projection** onto $C_s$ is the set of all nearest points,
--   $$P_{C_s}(y)=\operatorname*{argmin}_{x\in C_s}\|x-y\|,$$
--   which is set-valued because $C_s$ is not convex.
--   5. (Definition 2.3) For $L>0$, a vector $x^*\in C_s$ is an **$L$-stationary point** of (P) if it satisfies the condition $[\mathrm{NC}_L]$:
--   $$x^*\in P_{C_s}\!\Big(x^*-\tfrac1L\nabla f(x^*)\Big).$$
--
--   $L$-stationarity is the optimality notion of the mission: the goal is that the limit points of the partial sparse-simplex method are $L_2(f)$-stationary.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)`, so indices are $0,\dots,n-1$ rather than $1,\dots,n$, and $\|\cdot\|$ is the Euclidean norm. $M_s(x)$ is the entry at position $s-1$ of the list of $|x_i|$ sorted in nonincreasing order (meaningful for $1\le s\le n$). The local Lipschitz condition is a predicate on a constant $L_2$ rather than the computed maximum; "at most two nonzero components" in (2.15) is read as "supported in $\{i,j\}$", the reading of Example 2.1. $P_{C_s}(y)$ is the set of minimizers of $\|x-y\|$ over $C_s$ (minimizing the norm or its square is the same).
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), pp. 2, 4, 7, 11, (P), §2.1, P_{C_s} and Definition 2.3 (2.4), (2.15)

import Mathlib

namespace SparseNLO.Partial

/-- The ℓ₀ "norm" `‖x‖₀`: the number of nonzero components of `x ∈ ℝⁿ` (p. 2). -/
noncomputable def l0 {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- The support set `I₁(x) = {i : xᵢ ≠ 0}` (§2.1, p. 4). -/
noncomputable def I1 {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

/-- The complement of the support, `I₀(x) = {i : xᵢ = 0}` (§2.1, p. 4). -/
noncomputable def I0 {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = 0)

/-- The feasible set `C_s = {x : ‖x‖₀ ≤ s}` of at most `s`-sparse vectors (§2.1, p. 4). -/
def Cs (n s : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | l0 x ≤ s}

/-- `M_s(x)`, the `s`-th largest absolute value component of `x`, counted with multiplicity
(§2.1, p. 4): the entry at position `s - 1` of the list `|x_1|, …, |x_n|` sorted in
nonincreasing order. Meaningful for `1 ≤ s ≤ n`; then `M_s(x) = 0` exactly when `‖x‖₀ < s`. -/
noncomputable def Ms {n : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((Finset.univ.val.map (fun i => |x i|)).sort (fun a b : ℝ => b ≤ a)).getD (s - 1) 0

/-- The local Lipschitz hypothesis (2.15) with constant `L2` (p. 11): for all `i ≠ j`, all `x`,
and all `d` supported in `{i, j}`,
`‖∇_{i,j} f(x) − ∇_{i,j} f(x + d)‖ ≤ L2 ‖d‖`, where `∇_{i,j} f(x) = (∇_i f(x), ∇_j f(x))`.
The paper's local Lipschitz constant `L₂(f) = max_{i ≠ j} L_{i,j}(f)` satisfies it. -/
def LocalLipschitz {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L2 : ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ x d : EuclideanSpace ℝ (Fin n),
    (∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) →
      Real.sqrt ((gradient f x i - gradient f (x + d) i) ^ 2
          + (gradient f x j - gradient f (x + d) j) ^ 2) ≤ L2 * ‖d‖

/-- The orthogonal projection onto `C_s` (p. 7), `P_{C_s}(y) = argmin_{x ∈ C_s} ‖x − y‖²`, as the
**set** of all minimizers: `C_s` is not convex, so the projection is set-valued. -/
def projCs (n s : ℕ) (y : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ Cs n s ∧ ∀ z ∈ Cs n s, ‖x - y‖ ≤ ‖z - y‖}

/-- Definition 2.3 (p. 7): `x ∈ C_s` is an `L`-stationary point of (P) if it satisfies
`[NC_L]`: `x ∈ P_{C_s}(x − (1/L) ∇f(x))` (2.4). -/
def IsLStationary {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : ℕ) (L : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ Cs n s ∧ x ∈ projCs n s (x - (1 / L) • gradient f x)

end SparseNLO.Partial


