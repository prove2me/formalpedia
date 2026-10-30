-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_IsPiecewiseLinearOn
-- name    : StochasticProg_RecourseKKT_IsPiecewiseLinearOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:48:53.208026+00:00
-- url     : https://prove2.me/theorems/624f46b5-e66b-4710-a85b-cf68a5319572
-- title:
--   Piecewise linear function on a set
-- statement:
--   A function $f : E \to \mathbb R$ is **piecewise linear on** a set $D \subseteq E$ when there are finitely many convex polyhedra $C_1, \dots, C_k$ covering $D$ and affine functions $a_1, \dots, a_k$ with
--
--   $$
--   f(x) = a_i(x) \qquad \text{for all } x \in D \cap C_i,\ i = 1, \dots, k .
--   $$
--
--   This is "$f(x)$ is linear over regions defined by linear inequalities" (§2.11), the notion of Theorem 2.
--
--   **Formalization Note** "Linear" is read as affine on each region, as in the book's proof of Theorem 2, where $Q(x,\xi) = q_B^{\mathsf T} B^{-1}(h - Tx)$ on each region.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, §2.11, printed p. 99 (PDF p. 125); used in Chapter 3, Theorem 2, printed p. 107 (PDF p. 132)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_IsPolyhedralSet

namespace StochasticProg.RecourseKKT

/-- **Piecewise linear function on a set.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, §2.11, printed p. 99 (PDF p. 125): "f is piecewise linear, i.e., such that f(x) is linear
over regions defined by linear inequalities." Used in Chapter 3, Theorem 2, printed p. 107
(PDF p. 132).

`f` is piecewise linear on `D` when finitely many convex polyhedra `C₁, …, C_k` cover `D` and on each
`D ∩ Cᵢ` the function `f` coincides with an affine function `aᵢ`.

**Formalization Note.** "Linear over regions" is read as *affine* on each region: the book's own
pieces, `Q(x, ξ) = q_Bᵀ B⁻¹ (h − T x)` (proof of Theorem 2, p. 107), are affine in `x`. The regions
are polyhedra (`IsPolyhedralSet`), finitely many (`Fin k`). -/
def IsPiecewiseLinearOn {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) (D : Set E) :
    Prop :=
  ∃ (k : ℕ) (C : Fin k → Set E) (a : Fin k → E →ᵃ[ℝ] ℝ),
    (∀ i, IsPolyhedralSet (C i)) ∧ D ⊆ ⋃ i, C i ∧ ∀ i, ∀ x ∈ D ∩ C i, f x = a i x

end StochasticProg.RecourseKKT


