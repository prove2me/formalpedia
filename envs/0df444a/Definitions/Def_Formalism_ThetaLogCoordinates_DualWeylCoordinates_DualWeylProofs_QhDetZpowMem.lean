-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:32.580427+00:00
-- url     : https://prove2.me/theorems/f168f202-fdee-46a3-bbda-716368e5ea06
-- title:
--   Qh Det Zpow Mem
-- statement:
--   Definitions and structural lemmas for Qh Det Zpow Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
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
def qhDet (R : Type) [CommRing R] (n : ℕ) : (GLCoord R n)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (genMat R n).det).unit
def qhN (R : Type) [CommRing R] {n : ℕ} (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) : GLCoord R n :=
  algebraMap _ (GLCoord R n)
    (Matrix.det (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q)))
end Formalism.InvariantFactorPaths.ColumnFamilies


