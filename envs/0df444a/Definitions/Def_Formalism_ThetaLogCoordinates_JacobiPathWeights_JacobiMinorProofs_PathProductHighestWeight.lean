-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:06.685308+00:00
-- url     : https://prove2.me/theorems/d528402f-2d34-4aad-9eeb-298be8d89074
-- title:
--   Path Product Highest Weight
-- statement:
--   Definitions and structural lemmas for Path Product Highest Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A1hw
def tv {A : Type*} [CommRing A] {n : ℕ} (a b : Fin n) (hab : a ≠ b) (t : A) :
    (Matrix (Fin n) (Fin n) A)ˣ where
  val := Matrix.transvection a b t
  inv := Matrix.transvection a b (-t)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hab]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hab]; simp
end A1hw
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


