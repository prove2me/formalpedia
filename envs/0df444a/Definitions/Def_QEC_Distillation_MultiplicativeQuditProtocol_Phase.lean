-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_Phase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:22:08.426013+00:00
-- url     : https://prove2.me/theorems/4cb50c18-ef94-48b2-85d6-cb854378bc61
-- title:
--   Phase
-- statement:
--   Definitions and structural lemmas for Phase, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Mathlib.RingTheory.Trace.Basic
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation
open Semantics
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
def fieldTrace (x : F) : ZMod 2 := Algebra.trace (ZMod 2) F x
def additiveCharacter (x : F) : Complex :=
  Coding.PauliSymplectic.binaryPhaseScalar (fieldTrace x)
omit [Fintype F] in
/-- Every value of the trace-induced sign is its own multiplicative inverse. -/
theorem additiveCharacter_square (x : F) :
    additiveCharacter x * additiveCharacter x = 1 := by
  rw [additiveCharacter]
  by_cases hzero : fieldTrace x = 0
  · simp [Coding.PauliSymplectic.binaryPhaseScalar, hzero]
  · have hone : fieldTrace x = 1 :=
      Coding.PauliSymplectic.zmod_two_eq_one_of_ne_zero hzero
    simp [Coding.PauliSymplectic.binaryPhaseScalar, hone]
omit [Fintype F] in
/-- The trace-induced sign is fixed by complex conjugation. -/
theorem additiveCharacter_conj (x : F) :
    starRingEnd Complex (additiveCharacter x) = additiveCharacter x := by
  rw [additiveCharacter]
  by_cases hzero : fieldTrace x = 0
  · simp [Coding.PauliSymplectic.binaryPhaseScalar, hzero]
  · have hone : fieldTrace x = 1 :=
      Coding.PauliSymplectic.zmod_two_eq_one_of_ne_zero hzero
    simp [Coding.PauliSymplectic.binaryPhaseScalar, hone]
def cczAmplitude (x y z : F) : Complex :=
  additiveCharacter (x * y * z)
omit [Fintype F] in
/-- The local degree-three amplitude is a sign. -/
theorem cczAmplitude_square (x y z : F) :
    cczAmplitude x y z * cczAmplitude x y z = 1 :=
  additiveCharacter_square (x * y * z)
omit [Fintype F] in
/-- The local degree-three amplitude has unit complex norm. -/
theorem cczAmplitude_mul_conj (x y z : F) :
    cczAmplitude x y z * starRingEnd Complex (cczAmplitude x y z) = 1 := by
  rw [cczAmplitude, additiveCharacter_conj]
  exact additiveCharacter_square (x * y * z)
def cczDiagonalOperator :
    Operator (EuclideanSpace Complex (F × F × F)) where
  toFun psi := WithLp.toLp 2 fun label =>
    cczAmplitude label.1 label.2.1 label.2.2 * psi label
  map_add' := by
    intro psi chi
    ext label
    change cczAmplitude label.1 label.2.1 label.2.2 * (psi label + chi label) =
      cczAmplitude label.1 label.2.1 label.2.2 * psi label +
        cczAmplitude label.1 label.2.1 label.2.2 * chi label
    ring
  map_smul' := by
    intro scalar psi
    ext label
    change cczAmplitude label.1 label.2.1 label.2.2 * (scalar * psi label) =
      scalar * (cczAmplitude label.1 label.2.1 label.2.2 * psi label)
    ring
@[simp]
theorem cczDiagonalOperator_apply (psi : EuclideanSpace Complex (F × F × F))
    (label : F × F × F) :
    cczDiagonalOperator psi label =
      cczAmplitude label.1 label.2.1 label.2.2 * psi label :=
  rfl
theorem cczDiagonalOperator_square :
    cczDiagonalOperator (F := F) * cczDiagonalOperator =
      (1 : Operator (EuclideanSpace Complex (F × F × F))) := by
  ext psi label
  simp only [Module.End.mul_apply, cczDiagonalOperator_apply]
  rw [← mul_assoc, cczAmplitude_square]
  simp
theorem cczDiagonalOperator_map_inner
    (psi chi : EuclideanSpace Complex (F × F × F)) :
    inner Complex (cczDiagonalOperator psi) (cczDiagonalOperator chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [cczDiagonalOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (cczAmplitude label.1 label.2.1 label.2.2 * chi label) *
        (starRingEnd Complex (cczAmplitude label.1 label.2.1 label.2.2) *
          starRingEnd Complex (psi label)) =
        (cczAmplitude label.1 label.2.1 label.2.2 *
          starRingEnd Complex (cczAmplitude label.1 label.2.1 label.2.2)) *
          (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      rw [cczAmplitude_mul_conj]
      ring
noncomputable def cczLinearEquiv :
    EuclideanSpace Complex (F × F × F) ≃ₗ[Complex]
      EuclideanSpace Complex (F × F × F) where
  toFun psi := cczDiagonalOperator psi
  invFun psi := cczDiagonalOperator psi
  left_inv := by
    intro psi
    have h := LinearMap.congr_fun (cczDiagonalOperator_square (F := F)) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  right_inv := by
    intro psi
    have h := LinearMap.congr_fun (cczDiagonalOperator_square (F := F)) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  map_add' := cczDiagonalOperator.map_add
  map_smul' := cczDiagonalOperator.map_smul
@[simp]
theorem cczLinearEquiv_apply (psi : EuclideanSpace Complex (F × F × F))
    (label : F × F × F) :
    cczLinearEquiv psi label = cczAmplitude label.1 label.2.1 label.2.2 * psi label :=
  rfl
@[simp]
theorem cczLinearEquiv_symm_apply (psi : EuclideanSpace Complex (F × F × F))
    (label : F × F × F) :
    (cczLinearEquiv (F := F)).symm psi label =
      cczAmplitude label.1 label.2.1 label.2.2 * psi label :=
  rfl
noncomputable def cczTransport :
    UnitaryTransport (EuclideanSpace Complex (F × F × F))
      (EuclideanSpace Complex (F × F × F)) where
  toLinearEquiv := cczLinearEquiv
  map_inner := cczDiagonalOperator_map_inner
@[simp]
theorem cczTransport_apply (psi : EuclideanSpace Complex (F × F × F))
    (label : F × F × F) :
    cczTransport psi label = cczAmplitude label.1 label.2.1 label.2.2 * psi label :=
  rfl
def taggedCczAmplitude [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) : Complex :=
  cczAmplitude (label (ThreeCopyTag.first, site))
    (label (ThreeCopyTag.second, site))
    (label (ThreeCopyTag.third, site))
omit [Fintype F] in
/-- The selected tagged phase is a sign. -/
theorem taggedCczAmplitude_square [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczAmplitude site label * taggedCczAmplitude site label = 1 :=
  cczAmplitude_square _ _ _
omit [Fintype F] in
/-- The selected tagged phase has unit complex norm. -/
theorem taggedCczAmplitude_mul_conj [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczAmplitude site label * starRingEnd Complex (taggedCczAmplitude site label) = 1 := by
  exact cczAmplitude_mul_conj _ _ _
def taggedCczDiagonalOperator [Fintype ι] [DecidableEq ι] (site : ι) :
    Operator (TaggedThreeCopyRegister F ι) where
  toFun psi := WithLp.toLp 2 fun label =>
    taggedCczAmplitude site label * psi label
  map_add' := by
    intro psi chi
    ext label
    change taggedCczAmplitude site label * (psi label + chi label) =
      taggedCczAmplitude site label * psi label + taggedCczAmplitude site label * chi label
    ring
  map_smul' := by
    intro scalar psi
    ext label
    change taggedCczAmplitude site label * (scalar * psi label) =
      scalar * (taggedCczAmplitude site label * psi label)
    ring
@[simp]
theorem taggedCczDiagonalOperator_apply [Fintype ι] [DecidableEq ι]
    (site : ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczDiagonalOperator site psi label = taggedCczAmplitude site label * psi label :=
  rfl
theorem taggedCczDiagonalOperator_square [Fintype ι] [DecidableEq ι] (site : ι) :
    taggedCczDiagonalOperator (F := F) site * taggedCczDiagonalOperator site =
      (1 : Operator (TaggedThreeCopyRegister F ι)) := by
  ext psi label
  simp only [Module.End.mul_apply]
  change taggedCczAmplitude site label * (taggedCczAmplitude site label * psi label) = psi label
  rw [← mul_assoc, taggedCczAmplitude_square]
  simp
theorem taggedCczDiagonalOperator_map_inner [Fintype ι] [DecidableEq ι]
    (site : ι) (psi chi : TaggedThreeCopyRegister F ι) :
    inner Complex (taggedCczDiagonalOperator site psi) (taggedCczDiagonalOperator site chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [taggedCczDiagonalOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (taggedCczAmplitude site label * chi label) *
        (starRingEnd Complex (taggedCczAmplitude site label) * starRingEnd Complex (psi label)) =
        (taggedCczAmplitude site label * starRingEnd Complex (taggedCczAmplitude site label)) *
          (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      rw [taggedCczAmplitude_mul_conj]
      ring
noncomputable def taggedCczLinearEquiv [Fintype ι] [DecidableEq ι] (site : ι) :
    TaggedThreeCopyRegister F ι ≃ₗ[Complex] TaggedThreeCopyRegister F ι where
  toFun psi := taggedCczDiagonalOperator site psi
  invFun psi := taggedCczDiagonalOperator site psi
  left_inv := by
    intro psi
    have h := LinearMap.congr_fun (taggedCczDiagonalOperator_square (F := F) site) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  right_inv := by
    intro psi
    have h := LinearMap.congr_fun (taggedCczDiagonalOperator_square (F := F) site) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  map_add' := (taggedCczDiagonalOperator site).map_add
  map_smul' := (taggedCczDiagonalOperator site).map_smul
noncomputable def taggedCczTransport [Fintype ι] [DecidableEq ι] (site : ι) :
    UnitaryTransport (TaggedThreeCopyRegister F ι) (TaggedThreeCopyRegister F ι) where
  toLinearEquiv := taggedCczLinearEquiv site
  map_inner := taggedCczDiagonalOperator_map_inner site
end QEC.Distillation


