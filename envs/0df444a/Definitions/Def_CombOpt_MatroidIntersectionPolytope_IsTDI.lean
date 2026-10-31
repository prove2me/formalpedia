-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsTDI
-- name    : CombOpt_MatroidIntersectionPolytope_IsTDI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:51.273282+00:00
-- url     : https://prove2.me/theorems/2c95932a-1d28-4120-8915-3239eedf3389
-- title:
--   Totally dual integral system
-- statement:
--   For a rational system $Ax\le b$ and an objective $w$, linear-programming duality gives
--
--   $$
--   \max\{w^Tx : Ax\le b\}=\min\{y^Tb : y^TA=w^T,\ y\ge0\}.\qquad(6.13)
--   $$
--
--   The system $Ax\le b$ is **totally dual integral** (TDI) if, for every integral $w$ for which the optima in (6.13) exist, the minimum is achieved by an integral vector $y$: some $y\in\mathbb Z^m$ with $y\ge0$ and $y^TA=w^T$ has $y^Tb\le y'^Tb$ for every real $y'\ge0$ with $y'^TA=w^T$.
--
--   **Formalization Note** "The optima exist" is read as "both the maximum and the minimum of (6.13) are attained"; by linear-programming duality, either one being attained implies the other.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.6, (6.13), p. 225 (PDF p. 233)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_polyhedron

namespace CombOpt.MatroidIntersectionPolytope

/-- **Totally dual integral system.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.6, p. 225 (PDF p. 233): for the duality equation
`max {wᵀx : Ax ≤ b} = min {yᵀb : yᵀA = wᵀ, y ≥ 0}` (6.13), "we define a rational linear system
Ax ≤ b to be totally dual integral if the minimum in (6.13) can be achieved by an integral
vector y for each integral w for which the optima exist."

`IsTDI A b` holds when, for every integral `w` such that the maximum of `wᵀx` over
`{x : Ax ≤ b}` is attained and the minimum of `yᵀb` over `{y ≥ 0 : yᵀA = wᵀ}` is attained, some
integral `y ≥ 0` with `yᵀA = wᵀ` attains that minimum, i.e. `yᵀb ≤ y'ᵀb` for every real
`y' ≥ 0` with `y'ᵀA = wᵀ`.

**Formalization Note.** "The optima exist" is read as: both optima of (6.13) are attained. By
linear-programming duality either one being attained implies the other, so the hypothesis is not
stronger than the book's. Dual vectors range over `ℝ^m`; the integral one is the real cast of a
`y : m → ℤ`. -/
def IsTDI {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) (b : m → ℚ) : Prop :=
  ∀ w : n → ℤ,
    (∃ x ∈ polyhedron A b, ∀ x' ∈ polyhedron A b,
        ∑ j, (w j : ℝ) * x' j ≤ ∑ j, (w j : ℝ) * x j) →
    (∃ y : m → ℝ, 0 ≤ y ∧ (∀ j, ∑ i, y i * (A i j : ℝ) = w j) ∧
        ∀ y' : m → ℝ, 0 ≤ y' → (∀ j, ∑ i, y' i * (A i j : ℝ) = w j) →
          ∑ i, y i * (b i : ℝ) ≤ ∑ i, y' i * (b i : ℝ)) →
    ∃ y : m → ℤ, 0 ≤ y ∧ (∀ j, ∑ i, (y i : ℝ) * (A i j : ℝ) = w j) ∧
        ∀ y' : m → ℝ, 0 ≤ y' → (∀ j, ∑ i, y' i * (A i j : ℝ) = w j) →
          ∑ i, (y i : ℝ) * (b i : ℝ) ≤ ∑ i, y' i * (b i : ℝ)

end CombOpt.MatroidIntersectionPolytope


