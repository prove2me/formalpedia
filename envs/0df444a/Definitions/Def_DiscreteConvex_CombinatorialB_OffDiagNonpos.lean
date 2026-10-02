-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
-- name    : DiscreteConvex_CombinatorialB_OffDiagNonpos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:07.018971+00:00
-- url     : https://prove2.me/theorems/a5fbc5d8-1abf-4af8-a5f3-6702b8f8ae59
-- title:
--   Off-diagonal nonpositivity (2.9)
-- statement:
--   A symmetric matrix $L=(\ell_{ij})$ has **off-diagonal nonpositivity**: $\ell_{ij}\le 0$ for all $i\ne j$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.62, Eq. (2.9).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.62, Eq. (2.9)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.62, Eq. (2.9): off-diagonal nonpositivity of a
symmetric matrix, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Off-diagonal nonpositivity** (2.9): `ℓ_ij ≤ 0` for `i ≠ j`. -/
def OffDiagNonpos {V : Type*} [Fintype V] [DecidableEq V] (L : Matrix V V ℝ) : Prop :=
  ∀ i j : V, i ≠ j → L i j ≤ 0

end DiscreteConvex.CombinatorialB


