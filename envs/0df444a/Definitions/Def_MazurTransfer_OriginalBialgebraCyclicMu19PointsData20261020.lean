-- Prove2me | Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
-- name    : MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T22:03:24.574977+00:00
-- url     : https://prove2.me/theorems/76049bfe-77a5-42cf-abda-b8d634b83da3
-- title:
--   Original literal nineteenth-root points from a given cyclic bialgebra equivalence
-- statement:
--   Retain the original point restriction equivalence and literal nineteenth-root multiplicative point equivalence induced by the same given cyclic bialgebra equivalence. Both complete original constructor types and whole values, all private proof helper types, and all original cyclic point and bialgebra restriction operations are independently checked. Named downstream consumer: normalization of the same selected integral pi quotient and norm torsor pushforward at nineteen.
-- source:
--   MazurTheorem BialgebraCyclicMu19Points by Vas and contributors; original cyclic bialgebra literal-root point equivalences, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalCyclicNineteenGroupAlgebraPointsData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraPointRestrictionData20261020
import Theorems.Thm_MazurTransfer_original_bialgebra_point_restriction_laws
import Theorems.Thm_MazurTransfer_original_cyclic_nineteen_group_algebra_point_laws
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a GIVEN cyclic bialgebra equivalence supplies literal mu19
points over EVERY coefficient algebra, naturally and multiplicatively.
Named downstream consumer: field-label normalization of the SAME selected
integral pi quotient and its norm torsor pushforward at nineteen.
-/

noncomputable section
namespace MazurTransfer.BialgebraCyclicMu19Points
open CyclicNineteenGroupAlgebraPoints
variable {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic)
variable (T : Type) [CommRing T] [Algebra R T]

def basisPointEquiv : WithConv (H →ₐ[R] T) ≃ WithConv (MonoidAlgebra R Cyclic →ₐ[R] T) where
  toFun f := BialgebraPointRestriction.restrictPoint (φ.symm : _ →ₐc[R] H) f
  invFun f := BialgebraPointRestriction.restrictPoint (φ : H →ₐc[R] _) f
  left_inv f := by
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    change f.ofConv (φ.symm (φ h)) = f.ofConv h
    rw [BialgEquiv.symm_apply_apply]
  right_inv f := by
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    change f.ofConv (φ (φ.symm h)) = f.ofConv h
    rw [BialgEquiv.apply_symm_apply]

def literalPointEquiv : WithConv (H →ₐ[R] T) ≃* rootsOfUnity 19 T where
  __ := (basisPointEquiv φ T).trans (CyclicNineteenGroupAlgebraPoints.pointEquiv R)
  map_mul' f g := by
    change rootOfPoint R (BialgebraPointRestriction.restrictPoint (φ.symm : _ →ₐc[R] H) (f * g)) = _
    rw [MazurTransfer.original_bialgebra_point_restriction_laws.1, MazurTransfer.original_cyclic_nineteen_group_algebra_point_laws.2.2.2.2.2.2.2.2.1]
    rfl





end MazurTransfer.BialgebraCyclicMu19Points
#print axioms MazurTransfer.BialgebraCyclicMu19Points.basisPointEquiv
#print axioms MazurTransfer.BialgebraCyclicMu19Points.literalPointEquiv


