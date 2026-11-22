-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:32.48359+00:00
-- url     : https://prove2.me/theorems/616652d8-e757-4b6d-b26f-ec09d5a892e6
-- title:
--   Qs Mn Transpose
-- statement:
--   Definitions and structural lemmas for Qs Mn Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
def qs_sg (A : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (A.filter (m < ·)).card
def qs_mn {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R) (J I : Finset (Fin n)) : R :=
  if h : J.card = I.card then
    Matrix.det (Matrix.of fun a b : Fin I.card => g (J.orderEmbOfFin h a) (I.orderEmbOfFin rfl b)) else 0
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)
end Formalism.InvariantFactorPaths.ColumnFamilies


