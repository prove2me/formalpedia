-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:33:53.900176+00:00
-- url     : https://prove2.me/theorems/32cce262-214d-43cf-944a-eef0dc2c2f5c
-- title:
--   Highest Weight Space Finite
-- statement:
--   Definitions and structural lemmas for Highest Weight Space Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
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
def qr_ext {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  if e then insert (Fin.last m) (S.map Fin.castSuccEmb) else S.map Fin.castSuccEmb
section Ext
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))
end Ext
section Block
variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}
end Block
end Formalism.InvariantFactorPaths.ColumnFamilies


