-- Prove2me | Definitions.Def_QEC_Coding_ChainComplex_Duality
-- name    : QEC_Coding_ChainComplex_Duality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:02:15.375434+00:00
-- url     : https://prove2.me/theorems/78a26cd6-03fc-487b-9266-50006e0d78da
-- title:
--   Duality
-- statement:
--   Definitions and structural lemmas for Duality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
theorem wordLinearMapTranspose_zero :
    wordLinearMapTranspose
      (0 : Word F i0 →ₗ[F] Word F i1) = 0 := by
  classical
  apply LinearMap.ext
  intro x
  ext i
  simp [wordLinearMapTranspose]
noncomputable def dualChainComplex
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    ChainComplexData F (Word F i2) (Word F i1) (Word F i0) where
  boundary1 := wordLinearMapTranspose K.boundary2
  boundary2 := wordLinearMapTranspose K.boundary1
  boundary_squared := by
    rw [← wordLinearMapTranspose_comp]
    rw [K.boundary_squared]
    exact wordLinearMapTranspose_zero
end QEC.Coding


