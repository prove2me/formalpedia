-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Parameters
-- name    : QEC_Coding_Stabilizer_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:46:07.928664+00:00
-- url     : https://prove2.me/theorems/31f42413-5bed-4b28-9c4d-b47d19672628
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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
namespace QEC
namespace Coding
open PauliSymplectic
universe u v
namespace StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
structure BinaryStabilizerPresentation where
  code : SourceValidBinary ι
  generators : κ → Binary ι
  generated_eq : generatedStabilizerSet generators = code.1.generatedGroup
  independent : LinearIndependent (ZMod 2) (fun j => (generators j).vector)
namespace BinaryStabilizerPresentation
def blockLength (_P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Nat :=
  Fintype.card ι
def semanticCode (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι) :=
  P.code.1.code
def generatorSupport (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (j : κ) : Finset ι :=
  support (P.generators j)
def generatorRank (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Nat :=
  Module.finrank (ZMod 2) P.code.1.generatedVectorSubspace
def stabilizerInNormalizer (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Submodule (ZMod 2)
      (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace) :=
  P.code.1.generatedVectorSubspace.comap
    (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace).subtype
abbrev logicalPauliSpace (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :=
  (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace) ⧸
    P.stabilizerInNormalizer
def logicalPauliDimension (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Nat :=
  Module.finrank (ZMod 2) P.logicalPauliSpace
def encodedQubits (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Nat :=
  P.logicalPauliDimension / 2
omit [DecidableEq ι] in
theorem binaryOne_vector_eq_zero :
    (binaryOne (ι := ι)).vector = (0 : SymplecticVector (ZMod 2) ι) := by
  apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
  simp [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv, binaryOne]
omit [DecidableEq ι] in
theorem binarySign_vector_eq_zero (p : ZMod 2) :
    (binarySign (ι := ι) p).vector = (0 : SymplecticVector (ZMod 2) ι) := by
  apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
  simp [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv, binarySign]
theorem generatedGroupElement_eq_one_of_vector_eq_zero
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (G : P.code.1.GeneratedGroupElement)
    (hvector : G.1.vector = 0) : G = 1 := by
  by_cases hphase : G.1.phase = 0
  · apply Subtype.ext
    rw [PauliSymplectic.mk.injEq]
    exact ⟨hphase, hvector.trans binaryOne_vector_eq_zero.symm⟩
  · have hphaseOne : G.1.phase = 1 := zmod_two_eq_one_of_ne_zero hphase
    have hsign : G.1 = binarySign (ι := ι) 1 := by
      rw [PauliSymplectic.mk.injEq]
      exact ⟨hphaseOne, hvector.trans (binarySign_vector_eq_zero 1).symm⟩
    exact False.elim (P.code.2.1 (hsign ▸ G.2))
theorem generatedGroupElement_vector_injective
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Function.Injective (fun G : P.code.1.GeneratedGroupElement => G.1.vector) := by
  intro G H hGH
  have hzero : (G * H⁻¹).1.vector = 0 := by
    change (binaryMul G.1 (binaryDagger H.1)).vector = 0
    have hvector : G.1.vector = H.1.vector := hGH
    have hdouble_zero (a : ZMod 2) : a + a = 0 := by
      by_cases ha : a = 0
      · simp [ha]
      · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
        subst a
        decide
    apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
    ext i
    · simpa [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv,
        binaryMul, binaryDagger, hvector] using hdouble_zero (H.1.vector.xPart i)
    · simpa [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv,
        binaryMul, binaryDagger, hvector] using hdouble_zero (H.1.vector.zPart i)
  have hone := generatedGroupElement_eq_one_of_vector_eq_zero P (G * H⁻¹) hzero
  have hEq := congrArg (fun X : P.code.1.GeneratedGroupElement => X * H) hone
  simpa [mul_assoc] using hEq
noncomputable def generatedGroupElementVectorEquiv
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.code.1.GeneratedGroupElement ≃ P.code.1.generatedVectorSubspace :=
  Equiv.ofBijective
    (fun G => ⟨G.1.vector, ⟨G.1, G.2, rfl⟩⟩)
    ⟨fun G H hGH => generatedGroupElement_vector_injective P (congrArg Subtype.val hGH), by
      rintro ⟨v, G, hG, hvector⟩
      exact ⟨⟨G, hG⟩, Subtype.ext hvector⟩⟩
noncomputable def semanticCodeProjector
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  (Fintype.card P.code.1.GeneratedGroupElement : Complex)⁻¹ •
    P.code.1.stabilizerAverage
end BinaryStabilizerPresentation
structure StabilizerParameterData where
  presentation : BinaryStabilizerPresentation (ι := ι) (κ := κ)
  distance : Nat
  semanticDistance : SemanticStabilizerDistance presentation.code distance
namespace StabilizerParameterData
def blockLength (D : StabilizerParameterData (ι := ι) (κ := κ)) : Nat :=
  D.presentation.blockLength
def logicalPauliDimension (D : StabilizerParameterData (ι := ι) (κ := κ)) : Nat :=
  D.presentation.logicalPauliDimension
def encodedQubits (D : StabilizerParameterData (ι := ι) (κ := κ)) : Nat :=
  D.presentation.encodedQubits
def semanticCodeDimension (D : StabilizerParameterData (ι := ι) (κ := κ)) : Nat :=
  Module.finrank Complex D.presentation.semanticCode.carrier
end StabilizerParameterData
end StabilizerCode
end Coding
end QEC


