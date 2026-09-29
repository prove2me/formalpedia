-- Prove2me | Definitions.Def_BealeConvexMin_RandomLP_secondStageValue
-- name    : BealeConvexMin_RandomLP_secondStageValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:41:00.483751+00:00
-- url     : https://prove2.me/theorems/c6403efa-0c15-47eb-970a-1d35e6f54dfc
-- title:
--   Beale (1955), §5: the second-stage value min{f′y : y ≥ 0, Dy = b}
-- statement:
--   Beale's linear program with random coefficients has two stages. After the first-stage decision $x$ is fixed and the realised data are known, a non-negative second-stage vector $y\in\mathbb R^p$ is chosen to minimise $f'y$ subject to
--   $$Ax+Dy=\beta,\tag{5.4}$$
--   that is, $Dy=b$ with right-hand side $b=\beta-Ax$. Here $D$ is a constant $m\times p$ matrix and $f\in\mathbb R^p$ a constant cost vector.
--
--   This file defines three objects for a right-hand side $b\in\mathbb R^m$:
--
--   1. the **second-stage feasible set** $F(b)=\{y\in\mathbb R^p : y\ge 0,\ Dy=b\}$, with $y\ge0$ componentwise;
--   2. the predicate that the **second-stage minimum is attained**: there is $y^\ast\in F(b)$ with $f'y^\ast\le f'y$ for every $y\in F(b)$;
--   3. the **second-stage value**
--   $$Q(b)=\inf\{f'y : y\in F(b)\}.$$
--
--   When the minimum is attained, $Q(b)$ is that minimum, the quantity Beale writes as the minimum of $C$ over $y$. The paper takes the existence of "the value of $y$ that minimizes $C$" for granted.
--
--   **Formalization Note** $Q(b)$ is the real infimum `sInf` of the image of $F(b)$ under $y\mapsto f'y$. Lean returns the junk value $0$ when $F(b)$ is empty (infeasible second stage) or when $f'y$ is unbounded below on $F(b)$, so every theorem that uses $Q$ assumes the attainment predicate at the right-hand sides where it is evaluated.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, pp. 181–182 (PDF pp. 9–10), §5, eqs. (5.1)–(5.4)

import Mathlib

namespace BealeConvexMin.RandomLP

open Matrix

/-!
Beale (1955), §5, pp. 181–182, eqs. (5.1)–(5.4): the second stage of a linear program with random
coefficients. Once `x` is fixed and the realised values of `A` and `β` are known, the recourse
vector `y` is chosen non-negative to minimise `f′y` subject to `Ax + Dy = β` (eq. (5.4)), i.e.
`Dy = β − Ax`. Here `b` stands for that right-hand side `β − Ax`.
-/

/-- The second-stage feasible set `{y ∈ ℝ^p | y ≥ 0, D y = b}` (eqs. (5.2)/(5.4) with `b = β − Ax`).
Non-negativity is componentwise. -/
def feasY {m p : ℕ} (D : Matrix (Fin m) (Fin p) ℝ) (b : Fin m → ℝ) : Set (Fin p → ℝ) :=
  {y | 0 ≤ y ∧ D *ᵥ y = b}

/-- The second-stage minimum is attained: some feasible `y` has `f′y ≤ f′y'` for every feasible
`y'`. This is the paper's premise that "the value of y that minimizes C" exists (p. 182). -/
def SecondStageAttained {m p : ℕ} (D : Matrix (Fin m) (Fin p) ℝ) (f : Fin p → ℝ)
    (b : Fin m → ℝ) : Prop :=
  ∃ y ∈ feasY D b, ∀ y' ∈ feasY D b, f ⬝ᵥ y ≤ f ⬝ᵥ y'

/-- The second-stage value `min {f′y | y ≥ 0, D y = b}`, as the real infimum of `f′y` over
`feasY D b`. It is the minimum when `SecondStageAttained D f b` holds; on an empty or
unbounded-below feasible set the real `sInf` returns the junk value `0`, so every theorem
using it assumes attainment. -/
noncomputable def secondStageValue {m p : ℕ} (D : Matrix (Fin m) (Fin p) ℝ) (f : Fin p → ℝ)
    (b : Fin m → ℝ) : ℝ :=
  sInf ((fun y => f ⬝ᵥ y) '' feasY D b)

end BealeConvexMin.RandomLP


