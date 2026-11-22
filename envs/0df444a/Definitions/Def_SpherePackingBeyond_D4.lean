-- Prove2me | Definitions.Def_SpherePackingBeyond_D4
-- name    : SpherePackingBeyond_D4
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T22:37:58.531586+00:00
-- url     : https://prove2.me/theorems/2cadadf8-fd3d-4e4d-a364-6d7b40264539
-- title:
--   The $D_4$ root lattice and its unit-ball packing
-- statement:
--   The **$D_4$ root lattice** is the checkerboard lattice $\{x\in\mathbb{Z}^4 : x_1+x_2+x_3+x_4\equiv 0\pmod 2\}$, the even-sum sublattice of $\mathbb{Z}^4$. Its shortest nonzero vectors have length $\sqrt{2}$, so placing unit balls at the points of $\sqrt{2}\,D_4$ gives a packing whose distinct centers are at distance $2$. The file defines both $D_4$ and the scaled center set `D4centers` used in the density computation. These are the $d=4$ instances of the checkerboard lattices $D_n$ tabulated in Conway-Sloane.
--
--   **Formalization Note.** Points of `EuclideanSpace ℝ (Fin 4)` are indexed as functions; `D4centers` is written out explicitly as $\sqrt{2}$ times integer coordinates of even sum, rather than via a scalar action on sets.
-- source:
--   Conway & Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer 1999, Table I.1 (pp. xix-xx), https://doi.org/10.1007/978-1-4757-6568-7 (D4, Ch. 4 §7.1)

import Mathlib
import Definitions.Def_TenChallenges_SpherePacking

open scoped BigOperators

namespace SpherePackingBeyond

/-- The `D4` root lattice: integer vectors in `ℝ⁴` with even coordinate sum. -/
def D4 : Set (EuclideanSpace ℝ (Fin 4)) :=
  {x | ∃ z : Fin 4 → ℤ, (∀ i, x i = (z i : ℝ)) ∧ Even (∑ i, z i)}

/-- Centers of the unit-ball packing obtained from `D4`, scaled by `√2` so that
distinct centers are at distance at least `2`. -/
def D4centers : Set (EuclideanSpace ℝ (Fin 4)) :=
  {x | ∃ z : Fin 4 → ℤ, (∀ i, x i = Real.sqrt 2 * (z i : ℝ)) ∧ Even (∑ i, z i)}

end SpherePackingBeyond


