-- Prove2me | Definitions.Def_MazurTransfer_OriginalBialgebraMu19QuotientPointsData20261020
-- name    : MazurTransfer_OriginalBialgebraMu19QuotientPointsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-22T02:27:09.457842+00:00
-- url     : https://prove2.me/theorems/96b28a82-a35a-461c-9196-abec83e7bace
-- title:
--   Original literal mu19 quotient-point map from a given genuine bialgebra map
-- statement:
--   Retain the original literal nineteenth-root quotient-point map induced by the same given genuine bialgebra map and cyclic equivalence. Its complete original type and whole value, all generated helper types, and all original cyclic point and bialgebra restriction contexts are independently checked. Named downstream consumer: the same selected integral pi norm-kernel map and pushforward of its norm-preimage cocycles at nineteen.
-- source:
--   MazurTheorem BialgebraMu19QuotientPoints by Vas and contributors; same genuine bialgebra map and all-algebra literal-root quotient points, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal mu19 quotient points induced by the GIVEN
bialgebra inclusion and normalized cyclic equivalence over EVERY algebra.
Named downstream consumer: the SAME actual integral pi norm-kernel map
and pushforward of its norm-preimage cocycles at nineteen.
-/

noncomputable section
namespace MazurTransfer.BialgebraMu19QuotientPoints
open CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points BialgebraPointRestriction
variable {R H G : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable [CommRing G] [Bialgebra R G]
variable (j : H →ₐc[R] G) (ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic)
variable (T : Type) [CommRing T] [Algebra R T]

def quotientPoint (f : WithConv (G →ₐ[R] T)) : rootsOfUnity 19 T :=
  literalPointEquiv ψ T (restrictPoint j f)







end MazurTransfer.BialgebraMu19QuotientPoints

#print axioms MazurTransfer.BialgebraMu19QuotientPoints.quotientPoint


