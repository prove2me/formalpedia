-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:47.953543+00:00
-- url     : https://prove2.me/theorems/9ad3af51-7a3c-4297-8bdf-14e0821d284e
-- title:
--   KStable Highest Weight Vector
-- statement:
--   Definitions and structural lemmas for KStable Highest Weight Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
section TM
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ} {R : Type} [CommRing R]
  {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}
def qr_mn (g1 : GL (Fin m) R) {k : ℕ} (x y : {S : Finset (Fin m) // S.card = k}) : R :=
  (g1.val.submatrix (x.1.orderEmbOfFin x.2) (y.1.orderEmbOfFin y.2)).det
def qr_G (g1 : GL (Fin m) R) (K' I' : TIdx nu) (c : ℤ) : R := qr_mn g1 (qr_base K' c) (qr_base I' c)
end TM
end Formalism.InvariantFactorPaths.ColumnFamilies


