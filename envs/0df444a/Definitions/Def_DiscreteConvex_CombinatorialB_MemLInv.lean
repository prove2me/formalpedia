-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_MemLInv
-- name    : DiscreteConvex_CombinatorialB_MemLInv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:31.877727+00:00
-- url     : https://prove2.me/theorems/fd3e24cd-b080-42c0-95b2-9efb958e398d
-- title:
--   Membership in L⁻¹
-- statement:
--   $M\in\mathcal L^{-1}$: $M$ is the inverse of some symmetric positive-definite $L$ satisfying off-diagonal nonpositivity (2.9) and diagonal dominance (2.10).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68, Eq. (2.18)-(2.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68, Eq. (2.18)-(2.19)

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
import Definitions.Def_DiscreteConvex_CombinatorialB_DiagDominance

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.68, Eq. (2.18)-(2.19): the class `L⁻¹` of
matrix inverses of `L = \{L pos. def. with (2.9),(2.10)\}`, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- `M ∈ L⁻¹` (Eq. (2.18)-(2.19)): `M` is the inverse of some symmetric positive-definite `L`
with off-diagonal nonpositivity (2.9) and diagonal dominance (2.10). -/
def MemLInv {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : Prop :=
  ∃ L : Matrix V V ℝ, L.IsSymm ∧ L.PosDef ∧ OffDiagNonpos L ∧ DiagDominance L ∧ M = L⁻¹

end DiscreteConvex.CombinatorialB


