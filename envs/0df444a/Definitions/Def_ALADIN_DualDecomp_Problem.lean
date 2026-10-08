-- Prove2me | Definitions.Def_ALADIN_DualDecomp_Problem
-- name    : ALADIN_DualDecomp_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:06.93397+00:00
-- url     : https://prove2.me/theorems/3a97426b-43a2-4d50-ad28-c60f40d0dd34
-- title:
--   Problem (1.1), the decoupled problem (3.2) and the output (yᵢ, κᵢ) of step 1 of Algorithm 2
-- statement:
--   Fix integers $N, n, m, n_h \ge 0$. The **distributed optimization problem** (1.1) (equivalently (3.1)) is
--   $$\min_{x}\ \sum_{i=1}^N f_i(x_i)\quad\text{s.t.}\quad \sum_{i=1}^N A_i x_i = b,\qquad h_i(x_i)\le 0,\ i\in\{1,\dots,N\},$$
--   with blocks $x_i\in\mathbb R^n$, objectives $f_i:\mathbb R^n\to\mathbb R$, inequality constraint functions $h_i:\mathbb R^n\to\mathbb R^{n_h}$ (the inequality is componentwise), coupling matrices $A_i\in\mathbb R^{m\times n}$ and a right-hand side $b\in\mathbb R^m$. The data $(f, h, A, b)$ form one problem instance.
--
--   For a differentiable $\varphi:\mathbb R^n\to\mathbb R$, $\nabla\varphi(z)\in\mathbb R^n$ denotes the gradient, the vector of partial derivatives $\partial\varphi/\partial z_k(z)$.
--
--   Step 1 of Algorithm 2 (ALADIN), given the current primal iterate $x$, the dual iterate $\lambda\in\mathbb R^m$, a penalty parameter $\rho$ and scaling matrices $\Sigma_i$, solves for every $i$ the **decoupled problem** (3.2)
--   $$\min_{y_i}\ f_i(y_i) + \lambda^\top A_i y_i + \frac{\rho}{2}\,\|y_i - x_i\|_{\Sigma_i}^2\quad\text{s.t.}\quad h_i(y_i)\le 0 \ \mid\ \kappa_i,$$
--   where $\|v\|_{\Sigma}^2 = v^\top\Sigma v$. A **step-1 output** for block $i$ is a pair $(y_i,\kappa_i)\in\mathbb R^n\times\mathbb R^{n_h}$ such that
--   1. $y_i$ is a local minimizer of (3.2) over its feasible set $\{z : h_i(z)\le 0\}$ (the page allows "local or global optimality");
--   2. $\kappa_i\ge 0$, $h_i(y_i)\le 0$ and $\kappa_{i,j}\,(h_i(y_i))_j = 0$ for every $j$;
--   3. $\nabla_y\big[f_i(y) + \lambda^\top A_i y + \tfrac{\rho}{2}\|y-x_i\|_{\Sigma_i}^2\big]_{y=y_i} + \sum_{j=1}^{n_h}\kappa_{i,j}\,\nabla (h_i)_j(y_i) = 0$,
--
--   i.e. $\kappa_i$ is a KKT multiplier of the inequality constraint of (3.2) at $y_i$. With $\rho = 0$, (3.2) is the dual-decomposition subproblem (A.2), $d_i(\lambda) = \min_{y_i} f_i(y_i) + \lambda^\top A_i y_i$ s.t. $h_i(y_i)\le 0$.
--
--   These objects are the input of every statement in the mission: Lemma 5 compares two dual updates computed from a step-1 output.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; the gradient is defined through `fderiv` applied to the standard basis vectors, which is the gradient whenever the function is differentiable (all statements assume $C^2$ data). The multiplier $\kappa_i$ is part of the step-1 output, as the page's notation "$\mid \kappa_i$" indicates; the paper assumes the linear independence constraint qualification for the lower-level constraints (p. 1108), so such multipliers exist.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1101, (1.1); p. 1107, (3.1) and standing assumptions; p. 1108, Algorithm 2 step 1, (3.2); p. 1122, (A.2)

import Mathlib

namespace ALADIN.DualDecomp

open Matrix

/-- Problem (1.1) = (3.1) of Houska–Frasch–Diehl (2016), p. 1101 / p. 1107:
`min_x ∑ᵢ fᵢ(xᵢ)` s.t. `∑ᵢ Aᵢ xᵢ = b`, `hᵢ(xᵢ) ≤ 0` (componentwise), with
`N` blocks `xᵢ ∈ ℝⁿ`, `fᵢ : ℝⁿ → ℝ`, `hᵢ : ℝⁿ → ℝ^{nh}`, `Aᵢ ∈ ℝ^{m×n}`, `b ∈ ℝᵐ`.
Blocks are indexed by `Fin N`. -/
structure Problem (N n m nh : ℕ) where
  /-- the objectives `fᵢ : ℝⁿ → ℝ` -/
  f : Fin N → (Fin n → ℝ) → ℝ
  /-- the inequality constraint functions `hᵢ : ℝⁿ → ℝ^{nh}` -/
  h : Fin N → (Fin n → ℝ) → Fin nh → ℝ
  /-- the coupling matrices `Aᵢ ∈ ℝ^{m×n}` -/
  A : Fin N → Matrix (Fin m) (Fin n) ℝ
  /-- the right-hand side `b ∈ ℝᵐ` of the coupling constraint -/
  b : Fin m → ℝ

/-- The gradient `∇φ(z) ∈ ℝⁿ` of `φ : ℝⁿ → ℝ` at `z`, in standard coordinates: its `k`-th entry is
the partial derivative `∂φ/∂z_k (z) = Dφ(z) e_k`. -/
noncomputable def grad {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun k => fderiv ℝ φ z (Pi.single k 1)

variable {N n m nh : ℕ}

/-- The objective of the decoupled problem (3.2) of Algorithm 2, step 1 (p. 1108), for block `i`:
`yᵢ ↦ fᵢ(yᵢ) + λᵀ Aᵢ yᵢ + (ρ/2) ‖yᵢ − xᵢ‖²_{Σᵢ}`, where `‖v‖²_Σ = vᵀ Σ v`. -/
noncomputable def decoupledObjective (P : Problem N n m nh) (ρ : ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (i : Fin N) (z : Fin n → ℝ) : ℝ :=
  P.f i z + lam ⬝ᵥ (P.A i *ᵥ z) + ρ / 2 * ((z - x) ⬝ᵥ (Sig *ᵥ (z - x)))

/-- The feasible set `{yᵢ | hᵢ(yᵢ) ≤ 0}` of the decoupled problem (3.2) for block `i`. -/
def feasibleSet (P : Problem N n m nh) (i : Fin N) : Set (Fin n → ℝ) :=
  {z | ∀ j, P.h i z j ≤ 0}

/-- Output of Algorithm 2, step 1 (p. 1108), for block `i`: `yᵢ` solves the decoupled problem (3.2)
(to local optimality, which the page allows: "to either local or global optimality"), and
`κᵢ ∈ ℝ^{nh}_+` is its multiplier ("`| κᵢ`"), i.e. `(yᵢ, κᵢ)` satisfies the KKT conditions of (3.2):
dual feasibility `κᵢ ≥ 0`, primal feasibility `hᵢ(yᵢ) ≤ 0`, complementarity `κᵢⱼ hᵢⱼ(yᵢ) = 0`, and
stationarity `∇_y[objective of (3.2)](yᵢ) + ∑ⱼ κᵢⱼ ∇hᵢⱼ(yᵢ) = 0`. -/
def Step1Solution (P : Problem N n m nh) (ρ : ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (i : Fin N) (y : Fin n → ℝ) (κ : Fin nh → ℝ) : Prop :=
  IsLocalMinOn (decoupledObjective P ρ Sig x lam i) (feasibleSet P i) y ∧
  (∀ j, 0 ≤ κ j) ∧
  (∀ j, P.h i y j ≤ 0) ∧
  (∀ j, κ j * P.h i y j = 0) ∧
  grad (decoupledObjective P ρ Sig x lam i) y + ∑ j, κ j • grad (fun z => P.h i z j) y = 0

end ALADIN.DualDecomp


