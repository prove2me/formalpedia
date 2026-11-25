-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:27.484411+00:00
-- url     : https://prove2.me/theorems/82bfe1c7-7cdc-4943-9f84-97bd1a093202
-- title:
--   Dual Inter Self Dual Hermitian Lattice Subspace
-- statement:
--   Definitions and structural lemmas for Dual Inter Self Dual Hermitian Lattice Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
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
namespace GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
noncomputable def hfL (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]
noncomputable def hfR (x : Fin n → E) : (Fin n → E) →+ E where
  toFun y := hf L Hm x y
  map_add' a b := by simp [hf, mul_add, Finset.sum_add_distrib]
  map_zero' := by simp [hf]
variable {L Hm}
variable [IsNonarchimedeanLocalField F]
end GlobalTheory.HL.DualInter


