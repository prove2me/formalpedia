-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
-- name    : GroundTheory_LocalFields_LocalFourierExistence
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:42.848939+00:00
-- url     : https://prove2.me/theorems/a9b51cc1-5a57-5d1e-99bb-5af8189b7aa6
-- title:
--   Local Fourier Existence
-- statement:
--   Definitions and structural lemmas for Local Fourier Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Topology Filter
open scoped WithZero Pointwise
section RatCircle
def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ : ℚ →+* ℝ).toAddMonoidHom
    (AddSubgroup.zmultiples_le_of_mem (by
      rw [AddSubgroup.mem_comap]
      simp))
def ratCircleChar : AddChar (AddCircle (1 : ℚ)) Circle :=
  (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom ratAddCircleToReal
end RatCircle
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Existence
end Existence
end GroundTheory.LocalField


