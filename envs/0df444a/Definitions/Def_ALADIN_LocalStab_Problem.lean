-- Prove2me | Definitions.Def_ALADIN_LocalStab_Problem
-- name    : ALADIN_LocalStab_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:08.122607+00:00
-- url     : https://prove2.me/theorems/028f7a47-a1b7-4528-9759-31b751361b5b
-- title:
--   Problem (1.1): separable NLP with coupled affine constraints; KKT points, LICQ, strict complementarity, SOSC, regular KKT points
-- statement:
--   Fix integers $N, n, m, n_h \ge 0$. **Problem (1.1)** is the separable nonlinear program
--
--   $$
--   \min_{x}\ \sum_{i=1}^{N} f_i(x_i)\qquad\text{s.t.}\qquad \sum_{i=1}^{N} A_i x_i = b,\qquad h_i(x_i)\le 0,\quad i\in\{1,\dots,N\},
--   $$
--
--   over block vectors $x = (x_1,\dots,x_N)$ with $x_i\in\mathbb R^n$, where $f_i:\mathbb R^n\to\mathbb R$, $h_i:\mathbb R^n\to\mathbb R^{n_h}$ (the inequality is componentwise), $A_i\in\mathbb R^{m\times n}$ and $b\in\mathbb R^m$. Its **feasible set** consists of the $x$ with $\sum_i A_ix_i=b$ and $h_{ij}(x_i)\le 0$ for all $i,j$; a **local minimizer** is a feasible $x$ at which $\sum_i f_i$ is no larger than at every feasible point of some neighbourhood of $x$.
--
--   Following the paper's notation, $\lambda\in\mathbb R^m$ is the multiplier of the coupling constraint and $\kappa_i\in\mathbb R^{n_h}$ that of $h_i(x_i)\le 0$. A triple $(x,\lambda,\kappa)$ is a **KKT point** of (1.1) if
--
--   1. $x$ is feasible;
--   2. $\nabla f_i(x_i) + A_i^\top\lambda + \sum_{j} \kappa_{ij}\nabla h_{ij}(x_i) = 0$ for every block $i$;
--   3. $\kappa_{ij}\ge 0$ and $\kappa_{ij}\,h_{ij}(x_i) = 0$ for all $i,j$.
--
--   A constraint $(i,j)$ is **active** at $x$ if $h_{ij}(x_i)=0$. The KKT point is **regular** if in addition
--
--   1. **LICQ**: the gradients in $\mathbb R^{N n}$ of all constraints active at $x$ — the $m$ rows of $[A_1\ \cdots\ A_N]$, and for each active $(i,j)$ the block vector carrying $\nabla h_{ij}(x_i)$ in block $i$ and $0$ elsewhere — are linearly independent;
--   2. **strict complementarity**: $h_{ij}(x_i)=0$ implies $\kappa_{ij}>0$;
--   3. **SOSC**: for every nonzero $d=(d_1,\dots,d_N)\in\mathbb R^{Nn}$ with $\sum_i A_id_i=0$ and $\nabla h_{ij}(x_i)^\top d_i=0$ for every active $(i,j)$,
--   $$
--   \sum_{i=1}^N d_i^\top\,\nabla^2\big[f_i+\kappa_i^\top h_i\big](x_i)\,d_i \;>\;0 .
--   $$
--
--   The block-diagonal matrix with blocks $\nabla^2[f_i+\kappa_i^\top h_i](x_i)$ is the Hessian of the Lagrangian of (1.1) (the coupling term $\lambda^\top\sum_iA_ix_i$ is linear). Under strict complementarity the subspace in 3 is the critical cone, so this is the standard notion of a regular KKT point used in nonlinear programming, as the paper states with reference to Nocedal–Wright.
--
--   These objects are the setting of Lemma 3 of the paper: the local analysis of the ALADIN algorithm takes place around a local minimizer of (1.1) which is a regular KKT point.
--
--   **Formalization Note** Blocks are indexed by `Fin N`, vectors are `Fin n → ℝ` (with Mathlib's sup norm), matrices are Mathlib `Matrix`. Gradients and Hessians are expressed through Fréchet derivatives: $\nabla g(z)^\top d$ is `fderiv ℝ g z d` and $d^\top\nabla^2 g(z)d$ is `hessQuad g z d := fderiv ℝ (fderiv ℝ g) z d d`. LICQ is stated as: a linear combination of the active gradients (coefficients $\mu$ on the rows of $A$, $\nu_{ij}$ on the constraints, with $\nu_{ij}=0$ on inactive ones) that vanishes on every $d\in\mathbb R^{Nn}$ has $\mu=0,\ \nu=0$. Smoothness of $f_i,h_i$ is not part of the data; theorems assume it. The local-minimizer predicate states feasibility explicitly, since Mathlib's `IsLocalMinOn` alone holds vacuously outside the closure of the set.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1101, (1.1); p. 1104, Notation (regular KKT point, ref. [52] = Nocedal–Wright); p. 1107, (3.1)

import Mathlib

namespace ALADIN.LocalStab

open Matrix

/-- Problem (1.1) = (3.1) of Houska–Frasch–Diehl (2016), p. 1101 / p. 1107:
`min_x ∑ᵢ fᵢ(xᵢ)` s.t. `∑ᵢ Aᵢ xᵢ = b`, `hᵢ(xᵢ) ≤ 0` (componentwise), with
`N` blocks `xᵢ ∈ ℝⁿ`, `fᵢ : ℝⁿ → ℝ`, `hᵢ : ℝⁿ → ℝ^{nh}`, `Aᵢ ∈ ℝ^{m×n}`, `b ∈ ℝᵐ`.
Blocks are indexed by `Fin N`. Smoothness (`C²`, p. 1107) is not part of the data;
theorems assume it explicitly. -/
structure Problem (N n m nh : ℕ) where
  /-- the objectives `fᵢ : ℝⁿ → ℝ` -/
  f : Fin N → (Fin n → ℝ) → ℝ
  /-- the inequality constraint functions `hᵢ : ℝⁿ → ℝ^{nh}` -/
  h : Fin N → (Fin n → ℝ) → Fin nh → ℝ
  /-- the coupling matrices `Aᵢ ∈ ℝ^{m×n}` -/
  A : Fin N → Matrix (Fin m) (Fin n) ℝ
  /-- the right-hand side `b ∈ ℝᵐ` of the coupling constraint -/
  b : Fin m → ℝ

variable {N n m nh : ℕ}

/-- The separable objective `x ↦ ∑ᵢ fᵢ(xᵢ)` of (1.1). -/
def Problem.objective (P : Problem N n m nh) (x : Fin N → Fin n → ℝ) : ℝ :=
  ∑ i, P.f i (x i)

/-- The feasible set of (1.1): `∑ᵢ Aᵢ xᵢ = b` and `hᵢ(xᵢ) ≤ 0` for every block `i`. -/
def Problem.feasibleSet (P : Problem N n m nh) : Set (Fin N → Fin n → ℝ) :=
  {x | ∑ i, P.A i *ᵥ x i = P.b ∧ ∀ i j, P.h i (x i) j ≤ 0}

/-- `x` is a **local minimizer** of (1.1): `x` is feasible and `∑ᵢ fᵢ(xᵢ) ≤ ∑ᵢ fᵢ(x'ᵢ)` for every
feasible `x'` in a neighbourhood of `x`. (Feasibility is stated explicitly: Mathlib's `IsLocalMinOn`
alone holds vacuously at points outside the closure of the set.) -/
def Problem.IsLocalMinimizer (P : Problem N n m nh) (x : Fin N → Fin n → ℝ) : Prop :=
  x ∈ P.feasibleSet ∧ IsLocalMinOn P.objective P.feasibleSet x

/-- The block `i` of the Lagrangian without its linear coupling term:
`ξ ↦ fᵢ(ξ) + κᵢᵀ hᵢ(ξ)`. Its Hessian `∇²[fᵢ + κᵢᵀhᵢ]` is the `i`-th diagonal block of
the Hessian of the Lagrangian of (1.1) (the coupling term `λᵀ Aᵢ ξ` is linear). -/
def Problem.lagBlock (P : Problem N n m nh) (i : Fin N) (κi : Fin nh → ℝ)
    (ξ : Fin n → ℝ) : ℝ :=
  P.f i ξ + ∑ j, κi j * P.h i ξ j

/-- The quadratic form of the Hessian of `g : ℝⁿ → ℝ` at `z` in direction `d`:
`dᵀ ∇²g(z) d = D²g(z)[d, d]`, written as `fderiv (fderiv g) z d d`. -/
noncomputable def hessQuad {n : ℕ} (g : (Fin n → ℝ) → ℝ) (z d : Fin n → ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ g) z d d

/-- `(x, λ, κ)` is a **KKT point** of (1.1) (multiplier `λ ∈ ℝᵐ` of the coupling constraint,
`κᵢ ∈ ℝ^{nh}` of `hᵢ(xᵢ) ≤ 0`, Notation, p. 1104):
1. primal feasibility `∑ᵢ Aᵢxᵢ = b`, `hᵢ(xᵢ) ≤ 0`;
2. stationarity, block by block: `∇fᵢ(xᵢ) + Aᵢᵀλ + ∑ⱼ κᵢⱼ ∇hᵢⱼ(xᵢ) = 0`, written as the equality
   of the directional derivatives in every direction `d ∈ ℝⁿ`;
3. dual feasibility `κ ≥ 0`;
4. complementarity `κᵢⱼ hᵢⱼ(xᵢ) = 0`. -/
def Problem.IsKKTPoint (P : Problem N n m nh) (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ)
    (κ : Fin N → Fin nh → ℝ) : Prop :=
  x ∈ P.feasibleSet ∧
  (∀ i (d : Fin n → ℝ), fderiv ℝ (P.f i) (x i) d + lam ⬝ᵥ (P.A i *ᵥ d)
      + ∑ j, κ i j * fderiv ℝ (fun ξ => P.h i ξ j) (x i) d = 0) ∧
  (∀ i j, 0 ≤ κ i j) ∧
  (∀ i j, κ i j * P.h i (x i) j = 0)

/-- **LICQ** of (1.1) at `x`: the gradients in `ℝ^{N·n}` of all constraints active at `x` — the
`m` rows of `[A₁ ⋯ A_N]` and, for each active `(i, j)` (`hᵢⱼ(xᵢ) = 0`), the block vector with
`∇hᵢⱼ(xᵢ)` in block `i` and `0` elsewhere — are linearly independent. Stated as: every linear
combination with coefficients `μ ∈ ℝᵐ` on the rows and `ν` on the active constraints (`ν` vanishing on
inactive ones) that is the zero functional on `ℝ^{N·n}` has all coefficients zero. -/
def Problem.LICQ (P : Problem N n m nh) (x : Fin N → Fin n → ℝ) : Prop :=
  ∀ (μ : Fin m → ℝ) (ν : Fin N → Fin nh → ℝ),
    (∀ i j, P.h i (x i) j ≠ 0 → ν i j = 0) →
    (∀ d : Fin N → Fin n → ℝ, μ ⬝ᵥ (∑ i, P.A i *ᵥ d i)
        + ∑ i, ∑ j, ν i j * fderiv ℝ (fun ξ => P.h i ξ j) (x i) (d i) = 0) →
    μ = 0 ∧ ν = 0

/-- A **regular KKT point** (Notation, p. 1104, with reference [52] = Nocedal–Wright): a KKT point
`(x, λ, κ)` of (1.1) at which
1. LICQ holds;
2. strict complementarity holds: `hᵢⱼ(xᵢ) = 0 ⇒ κᵢⱼ > 0`;
3. SOSC holds: `∑ᵢ dᵢᵀ ∇²[fᵢ + κᵢᵀhᵢ](xᵢ) dᵢ > 0` for every `d ≠ 0` in `ℝ^{N·n}` with
   `∑ᵢ Aᵢdᵢ = 0` and `∇hᵢⱼ(xᵢ)ᵀdᵢ = 0` for every active `(i, j)` (under strict complementarity
   this subspace is the critical cone). -/
def Problem.IsRegularKKTPoint (P : Problem N n m nh) (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ)
    (κ : Fin N → Fin nh → ℝ) : Prop :=
  P.IsKKTPoint x lam κ ∧
  P.LICQ x ∧
  (∀ i j, P.h i (x i) j = 0 → 0 < κ i j) ∧
  (∀ d : Fin N → Fin n → ℝ, d ≠ 0 → ∑ i, P.A i *ᵥ d i = 0 →
      (∀ i j, P.h i (x i) j = 0 → fderiv ℝ (fun ξ => P.h i ξ j) (x i) (d i) = 0) →
      0 < ∑ i, hessQuad (P.lagBlock i (κ i)) (x i) (d i))

end ALADIN.LocalStab


