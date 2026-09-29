-- Prove2me | Definitions.Def_GPSAnalysis_Core_Problem
-- name    : GPSAnalysis_Core_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:14:14.345846+00:00
-- url     : https://prove2.me/theorems/d6c781c0-d1ed-4dbb-b686-ed1a3f46a4b9
-- title:
--   Linearly constrained problem (1.1): feasible region $\Omega=\{x:\ell\le Ax\le u\}$ and barrier $f_\Omega$
-- statement:
--   Audet and Dennis study the optimization problem
--
--   $$\min_{x\in\Omega} f(x), \qquad f:\mathbb R^n\to\mathbb R\cup\{+\infty\},$$
--
--   where the feasible region is a polyhedron given by two-sided linear constraints,
--
--   $$\Omega=\{x\in\mathbb R^n : \ell\le Ax\le u\},\qquad A\in\mathbb R^{m\times n},\quad \ell,u\in(\mathbb R\cup\{\pm\infty\})^m .$$
--
--   The inequalities are read componentwise in the extended reals, so an infinite bound imposes no constraint; with $m=0$ the region is all of $\mathbb R^n$.
--
--   The algorithm is applied not to $f$ but to the **barrier function**
--
--   $$f_\Omega(x)=\begin{cases} f(x) & \text{if } x\in\Omega,\\ +\infty & \text{otherwise,}\end{cases}$$
--
--   so $f$ is never evaluated at an infeasible point. The file also defines what it means for the constraint matrix $A$ to be **rational** (every entry is a rational number), which is the paper's assumption A2.
--
--   **Formalization Note** Points of $\mathbb R^n$ are `Fin n → ℝ`, the bounds are `EReal`-valued, and $f$ takes values in `WithTop ℝ` $=\mathbb R\cup\{+\infty\}$. The matrix $A$ is real and its rationality is a separate predicate, because several results of the paper are stated without A2.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), pp. 889-890, Section 1, Eq. (1.1) and the barrier f_Omega; p. 894, assumption A2

import Mathlib

open Matrix

namespace GPSAnalysis.Core

/-- The feasible region of problem (1.1) of Audet–Dennis (2003):
`Ω = {x ∈ ℝⁿ : ℓ ≤ A x ≤ u}` with `ℓ, u ∈ (ℝ ∪ {±∞})ᵐ`, compared componentwise in `EReal`.
When `m = 0`, `Ω = ℝⁿ`. -/
def feasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (lo up : Fin m → EReal) :
    Set (Fin n → ℝ) :=
  {x | ∀ i, lo i ≤ (((A *ᵥ x) i : ℝ) : EReal) ∧ (((A *ᵥ x) i : ℝ) : EReal) ≤ up i}

/-- The barrier function `f_Ω = f + ψ_Ω` (p. 890): `f_Ω(x) = f(x)` if `x ∈ Ω`, and `+∞` otherwise. -/
noncomputable def barrier {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) (Ω : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : WithTop ℝ := by
  classical
  exact if x ∈ Ω then f x else ⊤

/-- Assumption A2 (p. 894): every entry of the constraint matrix is rational. -/
def IsRationalMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, ∃ q : ℚ, A i j = (q : ℝ)

end GPSAnalysis.Core


