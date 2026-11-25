-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZero
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T17:08:12.656195+00:00
-- url     : https://prove2.me/theorems/e129cb0d-4133-4f99-9aa5-fd5dcd9d3e2f
-- title:
--   Exists Theta Division Point Ne Zero
-- statement:
--   Definitions and structural lemmas for Exists Theta Division Point Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsThetaDivisionPointNeZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ClassicalThetaLevelAndLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RiemannThetaLevelOneNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsApplySubSmulNeZeroAndApplyAddNeZero
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix
namespace GlobalTheory.ThetaDivisionPoints
noncomputable def intChar {g : ℕ} (N : ℕ) (c : Fin g → Fin N) : Multiplicative (Fin g → ℤ) →* ℂ where
  toFun m := eC (ofRealVec (fun i => ((c i : ℕ) : ℝ) / N) ⬝ᵥ ofIntVec m.toAdd)
  map_one' := by simp [ofIntVec_zero, eC_zero]
  map_mul' m m' := by rw [toAdd_mul, ofIntVec_add, dotProduct_add, eC_add]
end GlobalTheory.ThetaDivisionPoints


