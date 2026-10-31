-- Prove2me | Definitions.Def_ScholtesStab_MPCC
-- name    : ScholtesStab_MPCC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:28.04499+00:00
-- url     : https://prove2.me/theorems/4b278f3c-ae1f-4124-826b-1e119c1b6070
-- title:
--   MPCC and its Scholtes regularization $\mathcal S$: data and feasible sets
-- statement:
--   A **mathematical program with complementarity constraints** (MPCC) is
--
--   $$
--   \min_x f(x)\quad\text{s.t.}\quad x\in M,\qquad M=\{x\in\mathbb R^n \mid F_{1,j}(x)\cdot F_{2,j}(x)=0,\ F_{1,j}(x)\ge 0,\ F_{2,j}(x)\ge 0,\ j=1,\dots,\kappa\},
--   $$
--
--   where the defining functions $f\in C^2(\mathbb R^n,\mathbb R)$ and $F_1,F_2\in C^2(\mathbb R^n,\mathbb R^\kappa)$ are twice continuously differentiable. Its **Scholtes regularization** with parameter $t>0$ is the nonlinear program
--
--   $$
--   \mathcal S:\quad \min_x f(x)\quad\text{s.t.}\quad x\in M^{\mathcal S},\qquad M^{\mathcal S}=\{x\in\mathbb R^n \mid F_{1,j}(x)\cdot F_{2,j}(x)\le t,\ F_{1,j}(x)\ge 0,\ F_{2,j}(x)\ge 0,\ j=1,\dots,\kappa\}.
--   $$
--
--   The structure `MPCC n κ` bundles $f$, the components $F_{1,j},F_{2,j}$ and their $C^2$ regularity; `M` is the feasible set of MPCC and `MS t` that of $\mathcal S$ with parameter $t$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, and the index $j$ ranges over `Fin κ` (0-based). As in the paper, there are no further equality or inequality constraints. `MS t` is defined for every real $t$; the theorems assume $t>0$.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.1 (MPCC) and p.2 (S)

import Mathlib

namespace ScholtesStab

/-- Euclidean space `ℝⁿ`, the space of the decision variable `x`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- **The data of MPCC and of its Scholtes regularization S.**
Lämmel–Shikhman, arXiv:2501.07383v2, p.1 (display MPCC) and p.2 (display S):
"MPCC : min_x f(x) s. t. x ∈ M … where the defining functions f ∈ C²(ℝⁿ, ℝ),
F₁, F₂ ∈ C²(ℝⁿ, ℝ^κ) are twice continuously differentiable."

An instance consists of an objective `f : ℝⁿ → ℝ` and the components `F₁,ⱼ, F₂,ⱼ : ℝⁿ → ℝ`,
`j = 1, …, κ`, of the two complementarity maps, all of class `C²`.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. The index `j` ranges over
`Fin κ`, i.e. it is 0-based (`j = 0, …, κ−1` stands for the paper's `j = 1, …, κ`). The
paper's standing assumption that `f, F₁, F₂` are `C²` is part of the structure. As on p.1,
no further equality or inequality constraints are present. -/
structure MPCC (n κ : ℕ) where
  /-- the objective function `f` -/
  f : E n → ℝ
  /-- the components `F₁,ⱼ` of `F₁` -/
  F₁ : Fin κ → E n → ℝ
  /-- the components `F₂,ⱼ` of `F₂` -/
  F₂ : Fin κ → E n → ℝ
  /-- `f ∈ C²(ℝⁿ, ℝ)` -/
  contDiff_f : ContDiff ℝ 2 f
  /-- `F₁ ∈ C²(ℝⁿ, ℝ^κ)` -/
  contDiff_F₁ : ∀ j, ContDiff ℝ 2 (F₁ j)
  /-- `F₂ ∈ C²(ℝⁿ, ℝ^κ)` -/
  contDiff_F₂ : ∀ j, ContDiff ℝ 2 (F₂ j)

namespace MPCC

variable {n κ : ℕ}

/-- The feasible set `M` of MPCC (p.1):
`M = {x ∈ ℝⁿ | F₁,ⱼ(x) · F₂,ⱼ(x) = 0, F₁,ⱼ(x) ≥ 0, F₂,ⱼ(x) ≥ 0, j = 1, …, κ}`. -/
def M (P : MPCC n κ) : Set (E n) :=
  {x | ∀ j, P.F₁ j x * P.F₂ j x = 0 ∧ 0 ≤ P.F₁ j x ∧ 0 ≤ P.F₂ j x}

/-- The feasible set `Mˢ` of the Scholtes regularization S with parameter `t` (p.2):
`Mˢ = {x ∈ ℝⁿ | F₁,ⱼ(x) · F₂,ⱼ(x) ≤ t, F₁,ⱼ(x) ≥ 0, F₂,ⱼ(x) ≥ 0, j = 1, …, κ}`.
The paper takes `t > 0`; theorems using `MS t` assume `0 < t` explicitly. -/
def MS (P : MPCC n κ) (t : ℝ) : Set (E n) :=
  {x | ∀ j, P.F₁ j x * P.F₂ j x ≤ t ∧ 0 ≤ P.F₁ j x ∧ 0 ≤ P.F₂ j x}

end MPCC

end ScholtesStab


