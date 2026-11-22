-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:02.966809+00:00
-- url     : https://prove2.me/theorems/d44eb2e2-2df4-48c8-a5c2-5cc2144d30c1
-- title:
--   Qh Count All
-- statement:
--   Definitions and structural lemmas for Qh Count All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhCountAll.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
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
variable {n : ℕ} {R : Type} [CommRing R]
def qhM (R : Type) [CommRing R] {n : ℕ} (s : ℕ) (J : ℕ → Fin n) : GLCoord R n :=
  if hs : s ≤ n then qhN R s hs (fun q => J q.val) else 0
end Formalism.InvariantFactorPaths.ColumnFamilies


