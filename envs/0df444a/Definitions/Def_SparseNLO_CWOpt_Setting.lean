-- Prove2me | Definitions.Def_SparseNLO_CWOpt_Setting
-- name    : SparseNLO_CWOpt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:11:48.066593+00:00
-- url     : https://prove2.me/theorems/9e5608ee-9cb8-422e-bf59-ec54f56f1e32
-- title:
--   Problem (P): ‖x‖₀, I₁(x), I₀(x), C_s, M_s(x), the local Lipschitz condition (2.15), BF vectors (Def. 2.1) and CW-minima (Def. 2.4)
-- statement:
--   These are the objects of the sparsity constrained problem
--   $$(\mathrm P)\qquad \min\ f(x)\quad\text{s.t.}\quad \|x\|_0\le s,$$
--   where $f:\mathbb R^n\to\mathbb R$ is continuously differentiable and $0<s<n$ is an integer.
--
--   1. The **$\ell_0$ norm** $\|x\|_0$ is the number of nonzero components of $x$. The **support** is $I_1(x)=\{i : x_i\neq 0\}$ and its complement is $I_0(x)=\{i : x_i=0\}$. The feasible set is $C_s=\{x : \|x\|_0\le s\}$.
--   2. $M_s(x)$ is the $s$-th largest of the absolute values $|x_1|,\dots,|x_n|$, counted with multiplicity, so that $M_1(x)\ge M_2(x)\ge\dots\ge M_n(x)$. In particular $M_s(x)=0$ exactly when $\|x\|_0<s$.
--   3. A constant $L_2$ satisfies the **local Lipschitz condition (2.15)** for $f$ if for all $i\neq j$, all $x$, and all $d$ whose nonzero components lie in $\{i,j\}$,
--   $$\big\|\nabla_{i,j}f(x)-\nabla_{i,j}f(x+d)\big\|\le L_2\,\|d\|,$$
--   where $\nabla_{i,j}f(x)=(\nabla_i f(x),\nabla_j f(x))\in\mathbb R^2$. The paper's local Lipschitz constant $L_2(f)=\max_{i\ne j}L_{i,j}(f)$, which exists when $\nabla f$ is Lipschitz (Assumption 2), satisfies it; the predicate itself does not assume Assumption 2.
--   4. (Definition 2.1) A vector $x^*\in C_s$ is a **basic feasible (BF) vector** of (P) if $\nabla f(x^*)=0$ when $\|x^*\|_0<s$, and $\nabla_i f(x^*)=0$ for all $i\in I_1(x^*)$ when $\|x^*\|_0=s$.
--   5. (Definition 2.4) A vector $x^*\in C_s$ is a **coordinate-wise (CW) minimum** of (P) if either
--      - Case I: $\|x^*\|_0<s$ and $f(x^*)=\min_{t\in\mathbb R}f(x^*+te_i)$ for every $i$ (2.11), or
--      - Case II: $\|x^*\|_0=s$ and $f(x^*)\le\min_{t\in\mathbb R}f(x^*-x^*_ie_i+te_j)$ for every $i\in I_1(x^*)$ and every $j=1,\dots,n$ (2.12).
--
--   A CW-minimum is a point that no single-coordinate change (Case I), and no swap of one support coordinate for an arbitrary coordinate with an arbitrary value (Case II), can improve. It is the optimality notion whose relation to $L_2(f)$-stationarity is the subject of the mission.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)`, so indices are $0,\dots,n-1$ rather than $1,\dots,n$, and $\|\cdot\|$ is the Euclidean norm. $te_i$ is `EuclideanSpace.single i t`. $M_s(x)$ is the entry at position $s-1$ of the list of $|x_i|$ sorted in nonincreasing order (meaningful for $1\le s\le n$). Case I of Definition 2.4 is written $f(x^*)\le f(x^*+te_i)$ for all $t$, equivalent to (2.11) because $t=0$ attains the minimum; (2.12) is written as $f(x^*)\le f(x^*-x^*_ie_i+te_j)$ for all $t$. The local Lipschitz condition is a predicate on a constant $L_2$ rather than the computed maximum; "at most two nonzero components" in (2.15) is read as "supported in $\{i,j\}$", the reading of Example 2.1.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), pp. 2, 4, 5, 10, 11, (P), §2.1, Definition 2.1, Definition 2.4, (2.15)

import Mathlib

namespace SparseNLO.CWOpt

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
nonincreasing order. Meaningful for `1 ≤ s ≤ n`. -/
noncomputable def Ms {n : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((Finset.univ.val.map (fun i => |x i|)).sort (fun a b : ℝ => b ≤ a)).getD (s - 1) 0

/-- The local Lipschitz hypothesis (2.15) with constant `L2` (p. 11): for all `i ≠ j`, all `x`,
and all `d` supported in `{i, j}`,
`‖∇_{i,j} f(x) − ∇_{i,j} f(x + d)‖ ≤ L2 ‖d‖`, where `∇_{i,j} f(x) = (∇_i f(x), ∇_j f(x))`.
The paper's `L₂(f) = max_{i ≠ j} L_{i,j}(f)` satisfies it. -/
def LocalLipschitz {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L2 : ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ x d : EuclideanSpace ℝ (Fin n),
    (∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) →
      Real.sqrt ((gradient f x i - gradient f (x + d) i) ^ 2
          + (gradient f x j - gradient f (x + d) j) ^ 2) ≤ L2 * ‖d‖

/-- Definition 2.1 (p. 5): `x ∈ C_s` is a basic feasible (BF) vector of (P) if
`∇f(x) = 0` when `‖x‖₀ < s`, and `∇_i f(x) = 0` for all `i ∈ I₁(x)` when `‖x‖₀ = s`. -/
def IsBF {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ Cs n s ∧
    (l0 x < s → gradient f x = 0) ∧
    (l0 x = s → ∀ i ∈ I1 x, gradient f x i = 0)

/-- Definition 2.4 (p. 10): a feasible `x ∈ C_s` is a coordinate-wise (CW) minimum of (P) if
either (Case I) `‖x‖₀ < s` and `f(x) ≤ f(x + t eᵢ)` for every `i` and every `t ∈ ℝ` (2.11), or
(Case II) `‖x‖₀ = s` and `f(x) ≤ f(x − xᵢ eᵢ + t eⱼ)` for every `i ∈ I₁(x)`, every `j` and every
`t ∈ ℝ` (2.12). Here `t eᵢ = EuclideanSpace.single i t`. -/
def IsCWMin {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ Cs n s ∧
    ((l0 x < s ∧ ∀ (i : Fin n) (t : ℝ), f x ≤ f (x + EuclideanSpace.single i t)) ∨
     (l0 x = s ∧ ∀ i ∈ I1 x, ∀ (j : Fin n) (t : ℝ),
        f x ≤ f (x - EuclideanSpace.single i (x i) + EuclideanSpace.single j t)))

end SparseNLO.CWOpt


