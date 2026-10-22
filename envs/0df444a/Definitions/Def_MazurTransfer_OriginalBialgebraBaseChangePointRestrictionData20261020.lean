-- Prove2me | Definitions.Def_MazurTransfer_OriginalBialgebraBaseChangePointRestrictionData20261020
-- name    : MazurTransfer_OriginalBialgebraBaseChangePointRestrictionData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-22T02:19:21.212097+00:00
-- url     : https://prove2.me/theorems/b1939516-52fd-4d80-8972-80b0dc2a2e98
-- title:
--   Original canonical scalar change of a given genuine bialgebra map
-- statement:
--   Retain the exact original scalar change of the given genuine bialgebra map. Its complete original type and whole value and all generated helper types are independently checked. Named downstream consumer: normalized literal mu19 realization of the previously selected integral pi quotient after canonical scalar change at nineteen.
-- source:
--   MazurTheorem BialgebraBaseChangePointRestriction by Vas and contributors; same genuine bialgebra map and original point restriction square, Apache-2.0.

import Mathlib
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: base-change the GIVEN bialgebra map and prove its point
restriction square with the SAME original source and quotient labels.
Named downstream consumer: normalized mu19 realization of the PREVIOUSLY
SELECTED actual pi quotient after canonical scalar change at nineteen.
-/

noncomputable section
namespace MazurTransfer.BialgebraBaseChangePointRestriction
open scoped TensorProduct
variable {R S H G : Type} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing H] [HopfAlgebra R H] [CommRing G] [HopfAlgebra R G]

def baseChangeMap (j : H →ₐc[R] G) : S ⊗[R] H →ₐc[S] S ⊗[R] G :=
  Bialgebra.TensorProduct.map (BialgHom.id S S) j



variable {K : Type} [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]



end MazurTransfer.BialgebraBaseChangePointRestriction

#print axioms MazurTransfer.BialgebraBaseChangePointRestriction.baseChangeMap


