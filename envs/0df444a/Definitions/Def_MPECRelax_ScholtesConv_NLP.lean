-- Prove2me | Definitions.Def_MPECRelax_ScholtesConv_NLP
-- name    : MPECRelax_ScholtesConv_NLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:16.757303+00:00
-- url     : https://prove2.me/theorems/827f24bd-3a2a-47ff-b25f-630c9fb00098
-- title:
--   (2), Definition 2.1: the standard NLP, positive-linear dependence, MFCQ and KKT points
-- statement:
--   This file sets up the standard nonlinear program (2) of Hoheisel, Kanzow and Schwartz and the notions of §2.1 used later for the MPEC.
--
--   Throughout, $\mathbb R^n$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$, and $\nabla f(x)\in\mathbb R^n$ denotes the gradient of $f$ at $x$. A **nonlinear program** consists of an objective $f:\mathbb R^n\to\mathbb R$, finitely many inequality constraint functions $g_i$ ($i\in\iota$) and equality constraint functions $h_j$ ($j\in\kappa$):
--
--   $$\min f(x)\quad\text{s.t.}\quad g_i(x)\le 0\ (i\in\iota),\qquad h_j(x)=0\ (j\in\kappa).$$
--
--   1. A point $x$ is **feasible** if all constraints hold at $x$; the **active set** is $I_g(x)=\{i\mid g_i(x)=0\}$.
--   2. (**Definition 2.1**) For $I_1\subseteq\iota$, $I_2\subseteq\kappa$ the family $\{\nabla g_i(x)\mid i\in I_1\}\cup\{\nabla h_j(x)\mid j\in I_2\}$ is **positive-linearly dependent** if there are scalars $\alpha_i\ge 0$ ($i\in I_1$) and $\beta_j$ ($j\in I_2$), not all zero, with $\sum_{i\in I_1}\alpha_i\nabla g_i(x)+\sum_{j\in I_2}\beta_j\nabla h_j(x)=0$; otherwise it is positive-linearly independent.
--   3. $x$ satisfies the **Mangasarian–Fromovitz constraint qualification (MFCQ)** if the gradients $\nabla h_j(x)$, $j\in\kappa$, are linearly independent and there is $d\in\mathbb R^n$ with $\langle\nabla g_i(x),d\rangle<0$ for all $i\in I_g(x)$ and $\langle\nabla h_j(x),d\rangle=0$ for all $j$.
--   4. $x$ is a **stationary point** (the $x$-part of a KKT point) if $x$ is feasible and there are multipliers $\lambda\in\mathbb R^\iota$, $\mu\in\mathbb R^\kappa$ with $\lambda\ge0$, $\lambda_i g_i(x)=0$ for all $i$, and
--   $$\nabla f(x)+\sum_i\lambda_i\nabla g_i(x)+\sum_j\mu_j\nabla h_j(x)=0.$$
--
--   These objects are reused for the tightened program TNLP$(x^*)$ and for the relaxed programs of Scholtes and of Kadrani, Dussault and Benchakroun; the space $\mathbb R^n$ declared here is the one every mission of this paper works in.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla$ is Mathlib's `gradient`. The index sets are arbitrary types (finite where sums occur), so that subsets of constraints can be used as index types. Families of gradients are indexed families: a repeated vector counts as dependent. In positive-linear dependence the coefficients are extended by zero outside $I_1$, $I_2$, and "not all of them being zero" refers to all $\alpha_i$ and $\beta_j$ together. MFCQ is stated at any point (the paper states it at feasible points; the theorems add feasibility where the paper has it).
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 2–5, (2), MFCQ (p. 3), Definition 2.1 (p. 4), KKT points (p. 5)

import Mathlib

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesConv

/-- ℝⁿ with the Euclidean inner product; gradients are `gradient f x : E n`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A standard nonlinear program (2): minimize `f` subject to `g i x ≤ 0` (i : ι) and
`h j x = 0` (j : κ). -/
structure NLP (n : ℕ) (ι κ : Type) where
  f : E n → ℝ
  g : ι → E n → ℝ
  h : κ → E n → ℝ

namespace NLP

variable {n : ℕ} {ι κ : Type}

/-- `x` lies in the feasible set of (2). -/
def Feasible (P : NLP n ι κ) (x : E n) : Prop :=
  (∀ i, P.g i x ≤ 0) ∧ ∀ j, P.h j x = 0

/-- The active inequality constraints `I_g = {i | g_i(x) = 0}` (p. 3). -/
def activeSet (P : NLP n ι κ) (x : E n) : Set ι :=
  {i | P.g i x = 0}

/-- Definition 2.1: the family `{∇g_i(x) | i ∈ I₁} ∪ {∇h_j(x) | j ∈ I₂}` is positive-linearly
dependent: there are `α_i ≥ 0` (i ∈ I₁) and `β_j` (j ∈ I₂), not all zero, with
`∑_{i ∈ I₁} α_i ∇g_i(x) + ∑_{j ∈ I₂} β_j ∇h_j(x) = 0`. The coefficients are extended by zero
outside `I₁`, `I₂`. -/
def PosLinDep [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : E n) (I₁ : Set ι) (I₂ : Set κ) :
    Prop :=
  ∃ (α : ι → ℝ) (β : κ → ℝ), (∀ i ∈ I₁, 0 ≤ α i) ∧ (∀ i ∉ I₁, α i = 0) ∧
    (∀ j ∉ I₂, β j = 0) ∧ ((∃ i, α i ≠ 0) ∨ (∃ j, β j ≠ 0)) ∧
    ∑ i, α i • gradient (P.g i) x + ∑ j, β j • gradient (P.h j) x = 0

/-- The Mangasarian–Fromovitz constraint qualification (p. 3): the equality gradients
`∇h_j(x)` are linearly independent, and some `d` has `⟪∇g_i(x), d⟫ < 0` for every active `i`
and `⟪∇h_j(x), d⟫ = 0` for every `j`. -/
def IsMFCQ (P : NLP n ι κ) (x : E n) : Prop :=
  LinearIndependent ℝ (fun j : κ => gradient (P.h j) x) ∧
    ∃ d : E n, (∀ i ∈ P.activeSet x, ⟪gradient (P.g i) x, d⟫ < 0) ∧
      ∀ j, ⟪gradient (P.h j) x, d⟫ = 0

/-- `x` is a stationary point of (2) (p. 5): the `x`-part of a KKT point, i.e. `x` is feasible and
there are `λ ≥ 0`, `μ` with `λ_i g_i(x) = 0` and
`∇f(x) + ∑ λ_i ∇g_i(x) + ∑ μ_j ∇h_j(x) = 0`. -/
def IsKKTPoint [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : E n) : Prop :=
  P.Feasible x ∧ ∃ (lam : ι → ℝ) (mu : κ → ℝ), (∀ i, 0 ≤ lam i) ∧
    (∀ i, lam i * P.g i x = 0) ∧
    gradient P.f x + ∑ i, lam i • gradient (P.g i) x + ∑ j, mu j • gradient (P.h j) x = 0

end NLP

end MPECRelax.ScholtesConv


