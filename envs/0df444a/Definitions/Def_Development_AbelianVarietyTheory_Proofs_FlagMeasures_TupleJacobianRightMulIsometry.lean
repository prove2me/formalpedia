-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:17.419898+00:00
-- url     : https://prove2.me/theorems/f73b80bb-f604-4745-a7c2-b839bfc1d837
-- title:
--   Tuple Jacobian Right Mul Isometry
-- statement:
--   Definitions and structural lemmas for Tuple Jacobian Right Mul Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TupleJacobianRightMulIsometry.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.TupleJac
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
def rmulL {n m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (Fin m → Fin n → E) →ₗ[E] (Fin m → Fin n → E) where
  toFun x := rmul x A
  map_add' x y := by ext j k; simp [rmul, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext j k; simp [rmul, Finset.mul_sum, mul_left_comm]
def swapL (n m : ℕ) : (Fin n → Fin m → E) ≃ₗ[E] (Fin m → Fin n → E) where
  toFun x := fun j k => x k j
  invFun x := fun j k => x k j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
end GlobalTheory.HL.TupleJac


