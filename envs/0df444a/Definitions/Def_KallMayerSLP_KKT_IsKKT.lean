-- Prove2me | Definitions.Def_KallMayerSLP_KKT_IsKKT
-- name    : KallMayerSLP_KKT_IsKKT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:47.796506+00:00
-- url     : https://prove2.me/theorems/de7984b6-684b-4dd9-88a8-ce8b0a6e4681
-- title:
--   Karush–Kuhn–Tucker conditions (3.3)
-- statement:
--   A pair $(\hat x,\hat u)\in\mathbb R^n\times\mathbb R^m$ satisfies the **Karush–Kuhn–Tucker conditions** (3.3) for the program (3.1) if
--   1. $\nabla f(\hat x)+\sum_{i=1}^m\hat u_i\nabla g_i(\hat x)=0$,
--   2. $g_i(\hat x)\le 0$ for all $i$,
--   3. $\hat u_i\cdot g_i(\hat x)=0$ for all $i$,
--   4. $\hat u\ge 0$.
--
--   Proposition 3.4 shows that under the Slater condition these conditions characterize the optimal solutions of a convex program.
--
--   **Formalization Note** $\nabla$ is Mathlib's `gradient` (meaningful under continuous differentiability, which every theorem using the predicate assumes); $\hat u\ge0$ is componentwise.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, Proposition 3.4, eq. (3.3), p.64 (PDF 75)

import Mathlib

namespace KallMayerSLP.KKT

/-- **The Karush–Kuhn–Tucker conditions (3.3).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, Proposition 3.4, p.64
(PDF 75): for `x̂ ∈ ℝⁿ` and `û ∈ ℝᵐ`,
  i)   `∇f(x̂) + Σ_{i=1}^m ûᵢ ∇gᵢ(x̂) = 0`,
  ii)  `gᵢ(x̂) ≤ 0 ∀i`,
  iii) `ûᵢ · gᵢ(x̂) = 0 ∀i`,
  iv)  `û ≥ 0`.

**Formalization Note.** `∇` is Mathlib's `gradient` on `EuclideanSpace ℝ (Fin n)` (meaningful
under the book's standing continuous differentiability, which every theorem using this predicate
assumes); `û : Fin m → ℝ` and `û ≥ 0` is the componentwise order. -/
def IsKKT {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (u : Fin m → ℝ) : Prop :=
  gradient f x + ∑ i, u i • gradient (g i) x = 0 ∧
  (∀ i, g i x ≤ 0) ∧
  (∀ i, u i * g i x = 0) ∧
  0 ≤ u

end KallMayerSLP.KKT


