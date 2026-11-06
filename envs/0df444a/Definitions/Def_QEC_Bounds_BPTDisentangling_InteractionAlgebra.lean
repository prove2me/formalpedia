-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
-- name    : QEC_Bounds_BPTDisentangling_InteractionAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:47:38.863668+00:00
-- url     : https://prove2.me/theorems/6139fc42-47e8-4d49-9fbe-58a5dbab7c3e
-- title:
--   Interaction Algebra
-- statement:
--   Definitions and structural lemmas for Interaction Algebra, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_adjoint_eq_self
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_idempotent
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def RegionErasureRecoverable (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Prop :=
  (M.regionSubsystem region).ErasureRecoverableFromRegister M.codeSpace
theorem codeSpace_projector_isProj (M : BPTCommutingProjectorModel L kappa) :
    LinearMap.IsProj M.codeSpace.carrier M.fullCodeProjector := by
  constructor
  · intro vector
    exact M.codeSpace.projector_mem_carrier vector
  · intro vector hvector
    exact M.codeSpace.projector_eq_self_of_mem hvector
theorem trace_fullCodeProjector_eq_finrank_codeSpace
    (M : BPTCommutingProjectorModel L kappa) :
    LinearMap.trace Complex L.Register M.fullCodeProjector =
      (Module.finrank Complex M.codeSpace.carrier : Complex) := by
  exact M.codeSpace_projector_isProj.trace
noncomputable def normalizedCodeProjectorDensity
    (M : BPTCommutingProjectorModel L kappa) (hcode : M.codeSpace.carrier ≠ ⊥) :
    Semantics.DensityOperator L.Register where
  toOperator :=
    ((Module.finrank Complex M.codeSpace.carrier : Complex)⁻¹) • M.fullCodeProjector
  positive := by
    have hprojector : M.fullCodeProjector.IsSymmetricProjection := by
      constructor
      · change M.fullCodeProjector.comp M.fullCodeProjector = M.fullCodeProjector
        exact M.fullCodeProjector_idempotent
      · exact (LinearMap.isSymmetric_iff_isSelfAdjoint M.fullCodeProjector).mpr
          M.fullCodeProjector_adjoint_eq_self
    have hdim_nonneg : 0 ≤ (Module.finrank Complex M.codeSpace.carrier : Complex) := by
      exact_mod_cast Nat.zero_le (Module.finrank Complex M.codeSpace.carrier)
    exact hprojector.isPositive.smul_of_nonneg ((inv_nonneg).2 hdim_nonneg)
  trace_one := by
    have hdimNat : Module.finrank Complex M.codeSpace.carrier ≠ 0 := by
      intro hzero
      apply hcode
      exact Submodule.finrank_eq_zero.mp hzero
    have hdim : (Module.finrank Complex M.codeSpace.carrier : Complex) ≠ 0 := by
      exact_mod_cast hdimNat
    rw [map_smul, M.trace_fullCodeProjector_eq_finrank_codeSpace]
    exact inv_mul_cancel₀ hdim
def UnitarySupportedOn (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) (U : Semantics.UnitaryTransport L.Register L.Register) : Prop :=
  (M.regionSubsystem region).OperatorSupportedOnRegister U.toLinearEquiv.toLinearMap
noncomputable def thenUnitary
    (U V : Semantics.UnitaryTransport L.Register L.Register) :
    Semantics.UnitaryTransport L.Register L.Register where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (V (U x)) (V (U y)) = inner Complex x y
    rw [V.map_inner, U.map_inner]
noncomputable def composeUnitaryTransport
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (U : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K J) :
    Semantics.UnitaryTransport H J where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (V (U x)) (V (U y)) = inner Complex x y
    rw [V.map_inner, U.map_inner]
@[simp]
theorem composeUnitaryTransport_apply
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (U : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K J) (vector : H) :
    composeUnitaryTransport U V vector = V (U vector) :=
  rfl
@[simp]
theorem composeUnitaryTransport_toLinearEquiv_apply
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (U : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K J) (vector : H) :
    (composeUnitaryTransport U V).toLinearEquiv vector = V.toLinearEquiv (U.toLinearEquiv vector) :=
  rfl
noncomputable def unitaryRTensor
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J] :
    Semantics.UnitaryTransport (Semantics.CompositeSystem H J) (Semantics.CompositeSystem K J) := by
  let e := U.toLinearIsometryEquiv.rTensor J
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }
noncomputable def unitaryLTensor
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K) :
    Semantics.UnitaryTransport (Semantics.CompositeSystem I H) (Semantics.CompositeSystem I K) := by
  let e := U.toLinearIsometryEquiv.lTensor I
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }
@[simp]
theorem unitaryRTensor_apply_tmul
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (j : J) :
    unitaryRTensor U J (h ⊗ₜ[Complex] j) = U h ⊗ₜ[Complex] j :=
  rfl
@[simp]
theorem unitaryRTensor_toLinearEquiv_apply_tmul
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (j : J) :
    (unitaryRTensor U J).toLinearEquiv (h ⊗ₜ[Complex] j) =
      U.toLinearEquiv h ⊗ₜ[Complex] j :=
  rfl
@[simp]
theorem unitaryLTensor_apply_tmul
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (i : I) (h : H) :
    unitaryLTensor I U (i ⊗ₜ[Complex] h) = i ⊗ₜ[Complex] U h :=
  rfl
@[simp]
theorem unitaryLTensor_toLinearEquiv_apply_tmul
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (i : I) (h : H) :
    (unitaryLTensor I U).toLinearEquiv (i ⊗ₜ[Complex] h) =
      i ⊗ₜ[Complex] U.toLinearEquiv h :=
  rfl
noncomputable def extendLocalUnitaryToRegister
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q)
    (U : Semantics.UnitaryTransport S.selectedSystem S.selectedSystem) :
    Semantics.UnitaryTransport (Semantics.Qudit.QuditRegister q)
      (Semantics.Qudit.QuditRegister q) :=
  composeUnitaryTransport
    (composeUnitaryTransport S.registerFactorization
      (unitaryRTensor U S.complementSystem))
    S.registerFactorization.symm
noncomputable def extendSubmoduleUnitary
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (S : Submodule Complex H)
    (U : Semantics.UnitaryTransport S S) :
    Semantics.UnitaryTransport H H := by
  let L : S →ₗᵢ[Complex] H := S.subtypeₗᵢ.comp U.toLinearIsometryEquiv.toLinearIsometry
  let T : H →ₗᵢ[Complex] H := L.extend
  have hTsurj : Function.Surjective T := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := Complex)
      (V := H) (V₂ := H) rfl).mp T.injective
  let E : H ≃ₗᵢ[Complex] H := LinearIsometryEquiv.ofSurjective T hTsurj
  exact
    { toLinearEquiv := E.toLinearEquiv
      map_inner := fun x y => E.inner_map_map x y }
noncomputable def unitaryTransportOfLinearIsometryEquiv
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] (E : H ≃ₗᵢ[Complex] K) :
    Semantics.UnitaryTransport H K :=
  { toLinearEquiv := E.toLinearEquiv
    map_inner := fun x y => E.inner_map_map x y }
noncomputable def extendAlongLinearIsometryUnitary
    {A H : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : A →ₗᵢ[Complex] H)
    (U : Semantics.UnitaryTransport A A) :
    Semantics.UnitaryTransport H H := by
  let E : A ≃ₗᵢ[Complex] J.range := J.equivRange
  let EJ : Semantics.UnitaryTransport A J.range := unitaryTransportOfLinearIsometryEquiv E
  let Urange : Semantics.UnitaryTransport J.range J.range :=
    composeUnitaryTransport (composeUnitaryTransport EJ.symm U) EJ
  exact extendSubmoduleUnitary J.range Urange
noncomputable def conjugateUnitaryTransport
    {A B : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] (T : Semantics.UnitaryTransport A B)
    (U : Semantics.UnitaryTransport B B) :
    Semantics.UnitaryTransport A A :=
  composeUnitaryTransport (composeUnitaryTransport T U) T.symm
noncomputable def tensorAssociatorUnitary
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J] :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem H K) J)
      (Semantics.CompositeSystem H (Semantics.CompositeSystem K J)) := by
  let e := TensorProduct.assocIsometry Complex H K J
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }
noncomputable def submoduleTensorEmbedding
    {B C : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] (SB : Submodule Complex B) (SC : Submodule Complex C) :
    Semantics.CompositeSystem SB SC →ₗᵢ[Complex] Semantics.CompositeSystem B C :=
  TensorProduct.mapIsometry SB.subtypeₗᵢ SC.subtypeₗᵢ
noncomputable def activeSectorCoordinateTransport
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC)) :
    Semantics.UnitaryTransport (Semantics.CompositeSystem SB SC)
      (Semantics.CompositeSystem WB
        (Semantics.CompositeSystem (Semantics.CompositeSystem NB WC) NC)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (unitaryRTensor UB SC)
      (unitaryLTensor (Semantics.CompositeSystem WB NB) UC))
    (composeUnitaryTransport
      (tensorAssociatorUnitary WB NB (Semantics.CompositeSystem WC NC))
      (unitaryLTensor WB (tensorAssociatorUnitary NB WC NC).symm))
noncomputable def activeSectorPhysicalUnitary
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C) := by
  let T := activeSectorCoordinateTransport SB SC UB UC
  let V := unitaryLTensor WB (unitaryRTensor U NC)
  exact extendAlongLinearIsometryUnitary (submoduleTensorEmbedding SB SC)
    (conjugateUnitaryTransport T V)
@[simp]
theorem tensorAssociatorUnitary_apply_tmul
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (k : K) (j : J) :
    tensorAssociatorUnitary H K J ((h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j) =
      h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j) := by
  rfl
@[simp]
theorem tensorAssociatorUnitary_symm_apply_tmul
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (k : K) (j : J) :
    (tensorAssociatorUnitary H K J).symm (h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j)) =
      (h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j := by
  rfl
@[simp]
theorem tensorAssociatorUnitary_toLinearEquiv_apply_tmul
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (k : K) (j : J) :
    (tensorAssociatorUnitary H K J).toLinearEquiv ((h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j) =
      h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j) :=
  rfl
@[simp]
theorem tensorAssociatorUnitary_symm_toLinearEquiv_apply_tmul
    (H K J : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (h : H) (k : K) (j : J) :
    (tensorAssociatorUnitary H K J).symm.toLinearEquiv
        (h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j)) =
      (h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j :=
  rfl
noncomputable def tensorSwapUnitary
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K] :
    Semantics.UnitaryTransport (Semantics.CompositeSystem H K)
      (Semantics.CompositeSystem K H) := by
  let e := TensorProduct.commIsometry Complex H K
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }
@[simp]
theorem tensorSwapUnitary_apply_tmul
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (h : H) (k : K) :
    tensorSwapUnitary H K (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h :=
  rfl
@[simp]
theorem tensorSwapUnitary_toLinearEquiv_apply_tmul
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (h : H) (k : K) :
    (tensorSwapUnitary H K).toLinearEquiv (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h :=
  rfl
noncomputable def overlapLeftEmbedding
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a : A) : B →ₗ[Complex] Semantics.CompositeSystem A B :=
  TensorProduct.mk Complex A B a
@[simp]
theorem overlapLeftEmbedding_apply
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a : A) (b : B) :
    overlapLeftEmbedding A B a b = a ⊗ₜ[Complex] b :=
  rfl
noncomputable def overlapRightEmbedding
    (B C : Type u)
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) : B →ₗ[Complex] Semantics.CompositeSystem B C :=
  (TensorProduct.mk Complex B C).flip c
@[simp]
theorem overlapRightEmbedding_apply
    (B C : Type u)
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) (b : B) :
    overlapRightEmbedding B C c b = b ⊗ₜ[Complex] c :=
  rfl
theorem adjoint_overlapLeftEmbedding_apply_tmul
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a a' : A) (b : B) :
    LinearMap.adjoint (overlapLeftEmbedding A B a) (a' ⊗ₜ[Complex] b) =
      (inner Complex a a') • b := by
  apply (ext_iff_inner_left Complex).mpr
  intro test
  rw [LinearMap.adjoint_inner_right]
  simp [overlapLeftEmbedding, TensorProduct.inner_tmul, inner_smul_right, mul_comm]
theorem adjoint_overlapRightEmbedding_apply_tmul
    (B C : Type u)
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c c' : C) (b : B) :
    LinearMap.adjoint (overlapRightEmbedding B C c) (b ⊗ₜ[Complex] c') =
      (inner Complex c c') • b := by
  apply (ext_iff_inner_left Complex).mpr
  intro test
  rw [LinearMap.adjoint_inner_right]
  simp [overlapRightEmbedding, TensorProduct.inner_tmul, inner_smul_right, mul_comm]
noncomputable def rightTensorCompression
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (eta : B) (T : Semantics.Operator (Semantics.CompositeSystem A B)) :
    Semantics.Operator A :=
  (LinearMap.adjoint (overlapRightEmbedding A B eta)).comp
    (T.comp (overlapRightEmbedding A B eta))
noncomputable def rightTensorExtensionAfterLeft
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (T : Semantics.Operator (Semantics.CompositeSystem A W)) :
    Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem W N)) :=
  (tensorAssociatorUnitary A W N).conjOperator
    (TensorProduct.map T (1 : Semantics.Operator N))
noncomputable def leftInteractionCoefficient
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (a a' : A) :
    Semantics.Operator B :=
  (LinearMap.adjoint (overlapLeftEmbedding A B a)).comp
    (P.comp (overlapLeftEmbedding A B a'))
noncomputable def rightInteractionCoefficient
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (c c' : C) :
    Semantics.Operator B :=
  (LinearMap.adjoint (overlapRightEmbedding B C c)).comp
    (Q.comp (overlapRightEmbedding B C c'))
noncomputable def overlapRightCompression
    {H B C : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (inclusion : H →ₗ[Complex] B) :
    Semantics.Operator (Semantics.CompositeSystem H C) :=
  (TensorProduct.map (LinearMap.adjoint inclusion) (1 : Semantics.Operator C)).comp
    (Q.comp (TensorProduct.map inclusion (1 : Semantics.Operator C)))
noncomputable def leftTensorCompression
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (eta : A) (T : Semantics.Operator (Semantics.CompositeSystem A B)) :
    Semantics.Operator B :=
  (LinearMap.adjoint (overlapLeftEmbedding A B eta)).comp
    (T.comp (overlapLeftEmbedding A B eta))
noncomputable def leftTensorExtensionBeforeRight
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem N C)) :
    Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem W N) C) :=
  (tensorAssociatorUnitary W N C).symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator W) T)
noncomputable def overlapLiftLeft
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) :
    Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) :=
  TensorProduct.map P (1 : Semantics.Operator C)
noncomputable def overlapLiftRight
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) :
    Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) :=
  (tensorAssociatorUnitary A B C).symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator A) Q)
noncomputable def overlapTripleEmbedding
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a : A) (c : C) : B →ₗ[Complex]
      Semantics.CompositeSystem (Semantics.CompositeSystem A B) C :=
  (overlapRightEmbedding (Semantics.CompositeSystem A B) C c).comp
    (overlapLeftEmbedding A B a)
@[simp]
theorem overlapTripleEmbedding_apply
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a : A) (c : C) (b : B) :
    overlapTripleEmbedding A B C a c b = (a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c := by
  rfl
@[simp]
theorem overlapLiftLeft_apply_tmul
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (a : A) (b : B) (c : C) :
    overlapLiftLeft (C := C) P ((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c) =
      P (a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c := by
  rfl
@[simp]
theorem overlapLiftRight_apply_tmul
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a : A) (b : B) (c : C) :
    overlapLiftRight (A := A) Q ((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c) =
      (tensorAssociatorUnitary A B C).symm (a ⊗ₜ[Complex] Q (b ⊗ₜ[Complex] c)) := by
  simp [overlapLiftRight, Semantics.UnitaryTransport.conjOperator]
@[simp]
theorem overlapLiftRight_apply_tripleEmbedding
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a : A) (b : B) (c : C) :
    overlapLiftRight (A := A) Q (overlapTripleEmbedding A B C a c b) =
      (tensorAssociatorUnitary A B C).symm (a ⊗ₜ[Complex] Q (b ⊗ₜ[Complex] c)) := by
  simpa using overlapLiftRight_apply_tmul (A := A) Q a b c
@[simp]
theorem overlapLiftLeft_apply_associator_symm_tmul
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (a : A) (b : B) (c : C) :
    overlapLiftLeft (C := C) P
        ((tensorAssociatorUnitary A B C).symm (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] c))) =
      P (a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c := by
  rw [tensorAssociatorUnitary_symm_apply_tmul]
  rfl
theorem leftOverlapCompression_through_reassociation
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (a a' : A) (c : C) (middle : Semantics.CompositeSystem B C) :
    LinearMap.adjoint (overlapTripleEmbedding A B C a c)
        (overlapLiftLeft (C := C) P
          ((tensorAssociatorUnitary A B C).symm (a' ⊗ₜ[Complex] middle))) =
      leftInteractionCoefficient P a a'
        (LinearMap.adjoint (overlapRightEmbedding B C c) middle) := by
  induction middle using TensorProduct.induction_on with
  | zero =>
      simp [leftInteractionCoefficient, overlapTripleEmbedding,
        LinearMap.adjoint_comp, LinearMap.comp_apply]
  | tmul middleB middleC =>
      rw [overlapLiftLeft_apply_associator_symm_tmul]
      simp [leftInteractionCoefficient, overlapTripleEmbedding,
        LinearMap.adjoint_comp, LinearMap.comp_apply,
        adjoint_overlapLeftEmbedding_apply_tmul,
        adjoint_overlapRightEmbedding_apply_tmul]
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
theorem overlapTripleCompression_left_then_right_apply
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) (b : B) :
    (LinearMap.adjoint (overlapTripleEmbedding A B C a c)).comp
      ((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
        (overlapTripleEmbedding A B C a' c')) b =
      (leftInteractionCoefficient P a a' * rightInteractionCoefficient Q c c') b := by
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [overlapLiftRight_apply_tripleEmbedding]
  simpa [leftInteractionCoefficient, rightInteractionCoefficient, LinearMap.comp_apply] using
    leftOverlapCompression_through_reassociation P a a' c
      (Q (b ⊗ₜ[Complex] c'))
theorem overlapTripleCompression_left_then_right
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) :
    (LinearMap.adjoint (overlapTripleEmbedding A B C a c)).comp
      ((overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q).comp
        (overlapTripleEmbedding A B C a' c')) =
      leftInteractionCoefficient P a a' * rightInteractionCoefficient Q c c' := by
  apply LinearMap.ext
  intro b
  exact overlapTripleCompression_left_then_right_apply P Q a a' c c' b
theorem adjoint_overlapTripleEmbedding_apply_associator_symm
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (a a' : A) (c : C) (middle : Semantics.CompositeSystem B C) :
    LinearMap.adjoint (overlapTripleEmbedding A B C a c)
        ((tensorAssociatorUnitary A B C).symm (a' ⊗ₜ[Complex] middle)) =
      (inner Complex a a') • LinearMap.adjoint (overlapRightEmbedding B C c) middle := by
  induction middle using TensorProduct.induction_on with
  | zero =>
      simp [overlapTripleEmbedding, LinearMap.adjoint_comp, LinearMap.comp_apply]
  | tmul middleB middleC =>
      rw [tensorAssociatorUnitary_symm_apply_tmul]
      simp [overlapTripleEmbedding, LinearMap.adjoint_comp, LinearMap.comp_apply,
        adjoint_overlapLeftEmbedding_apply_tmul,
        adjoint_overlapRightEmbedding_apply_tmul, smul_smul, mul_comm]
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add, smul_add] using congrArg₂ (· + ·) hx hy
theorem rightOverlapCompression_through_left
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a : A) (c c' : C) (middle : Semantics.CompositeSystem A B) :
    LinearMap.adjoint (overlapTripleEmbedding A B C a c)
        (overlapLiftRight (A := A) Q (middle ⊗ₜ[Complex] c')) =
      rightInteractionCoefficient Q c c'
        (LinearMap.adjoint (overlapLeftEmbedding A B a) middle) := by
  induction middle using TensorProduct.induction_on with
  | zero =>
      simp [rightInteractionCoefficient, overlapTripleEmbedding,
        LinearMap.adjoint_comp, LinearMap.comp_apply]
  | tmul middleA middleB =>
      rw [overlapLiftRight_apply_tmul]
      rw [adjoint_overlapTripleEmbedding_apply_associator_symm]
      simp [rightInteractionCoefficient, LinearMap.adjoint_comp, LinearMap.comp_apply,
        adjoint_overlapLeftEmbedding_apply_tmul]
  | add x y hx hy =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy
theorem overlapTripleCompression_right_then_left_apply
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) (b : B) :
    (LinearMap.adjoint (overlapTripleEmbedding A B C a c)).comp
      ((overlapLiftRight (A := A) Q * overlapLiftLeft (C := C) P).comp
        (overlapTripleEmbedding A B C a' c')) b =
      (rightInteractionCoefficient Q c c' * leftInteractionCoefficient P a a') b := by
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  change LinearMap.adjoint (overlapTripleEmbedding A B C a c)
      (overlapLiftRight (A := A) Q
        (overlapLiftLeft (C := C) P ((a' ⊗ₜ[Complex] b) ⊗ₜ[Complex] c'))) =
    rightInteractionCoefficient Q c c' (leftInteractionCoefficient P a a' b)
  rw [overlapLiftLeft_apply_tmul]
  simpa [leftInteractionCoefficient, rightInteractionCoefficient, LinearMap.comp_apply] using
    rightOverlapCompression_through_left Q a c c' (P (a' ⊗ₜ[Complex] b))
theorem overlapTripleCompression_right_then_left
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (a a' : A) (c c' : C) :
    (LinearMap.adjoint (overlapTripleEmbedding A B C a c)).comp
      ((overlapLiftRight (A := A) Q * overlapLiftLeft (C := C) P).comp
        (overlapTripleEmbedding A B C a' c')) =
      rightInteractionCoefficient Q c c' * leftInteractionCoefficient P a a' := by
  apply LinearMap.ext
  intro b
  exact overlapTripleCompression_right_then_left_apply P Q a a' c c' b
theorem leftInteractionCoefficient_commute_rightInteractionCoefficient
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (a a' : A) (c c' : C) :
    Commute (leftInteractionCoefficient P a a') (rightInteractionCoefficient Q c c') := by
  change leftInteractionCoefficient P a a' * rightInteractionCoefficient Q c c' =
    rightInteractionCoefficient Q c c' * leftInteractionCoefficient P a a'
  rw [← overlapTripleCompression_left_then_right P Q a a' c c', hcommute.eq,
    overlapTripleCompression_right_then_left P Q a a' c c']
noncomputable def leftInteractionAlgebra
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) :
    StarSubalgebra Complex (Semantics.Operator B) :=
  StarAlgebra.adjoin Complex
    {coefficient | ∃ a a' : A, coefficient = leftInteractionCoefficient P a a'}
noncomputable def rightInteractionAlgebra
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) :
    StarSubalgebra Complex (Semantics.Operator B) :=
  StarAlgebra.adjoin Complex
    {coefficient | ∃ c c' : C, coefficient = rightInteractionCoefficient Q c c'}
theorem adjoint_leftInteractionCoefficient_of_selfAdjoint
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (hselfAdjoint : LinearMap.adjoint P = P) (a a' : A) :
    LinearMap.adjoint (leftInteractionCoefficient P a a') =
      leftInteractionCoefficient P a' a := by
  simp [leftInteractionCoefficient, LinearMap.adjoint_comp, hselfAdjoint,
    LinearMap.comp_assoc]
theorem rightInteractionAlgebra_le_leftCoefficientCentralizer
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q)) :
    rightInteractionAlgebra Q ≤ StarSubalgebra.centralizer Complex
      ({coefficient | ∃ a a' : A, coefficient = leftInteractionCoefficient P a a'} :
        Set (Semantics.Operator B)) := by
  rw [rightInteractionAlgebra]
  apply StarAlgebra.adjoin_le
  rintro coefficient ⟨c, c', rfl⟩
  refine (StarSubalgebra.mem_centralizer_iff Complex).mpr ?_
  intro leftCoefficient hleftCoefficient
  rcases hleftCoefficient with ⟨a, a', rfl⟩
  constructor
  · exact (leftInteractionCoefficient_commute_rightInteractionCoefficient
      P Q hcommute a a' c c').eq
  · rw [LinearMap.star_eq_adjoint,
      adjoint_leftInteractionCoefficient_of_selfAdjoint P hselfAdjoint]
    exact (leftInteractionCoefficient_commute_rightInteractionCoefficient
      P Q hcommute a' a c c').eq
theorem interactionAlgebras_commute
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    {left right : Semantics.Operator B}
    (hleft : left ∈ leftInteractionAlgebra P)
    (hright : right ∈ rightInteractionAlgebra Q) :
    Commute left right := by
  have hrightCentral := rightInteractionAlgebra_le_leftCoefficientCentralizer
    P Q hselfAdjoint hcommute
  have hleftCentral : leftInteractionAlgebra P ≤ StarSubalgebra.centralizer Complex
      (rightInteractionAlgebra Q : Set (Semantics.Operator B)) := by
    rw [leftInteractionAlgebra]
    apply StarAlgebra.adjoin_le
    rintro coefficient ⟨a, a', rfl⟩
    refine (StarSubalgebra.mem_centralizer_iff Complex).mpr ?_
    intro rightCoefficient hrightCoefficient
    constructor
    · have hcentral := ((StarSubalgebra.mem_centralizer_iff Complex).mp
        (hrightCentral hrightCoefficient))
        (leftInteractionCoefficient P a a') ⟨a, a', rfl⟩
      exact hcentral.1.symm
    · have hcentral := ((StarSubalgebra.mem_centralizer_iff Complex).mp
        (hrightCentral (StarMemClass.star_mem hrightCoefficient)))
        (leftInteractionCoefficient P a a') ⟨a, a', rfl⟩
      exact hcentral.1.symm
  exact ((StarSubalgebra.mem_centralizer_iff Complex).mp
    (hleftCentral hleft) right hright).1.symm
def commutingOperatorAsModuleEnd
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (T : Semantics.Operator B)
    (hcommute : ∀ operator : S, Commute (operator : Semantics.Operator B) T) :
    Module.End S B where
  toFun := T
  map_add' := T.map_add
  map_smul' := by
    intro operator vector
    change T ((operator : Semantics.Operator B) vector) =
      (operator : Semantics.Operator B) (T vector)
    exact congrArg (fun map => map vector) (hcommute operator).eq.symm
theorem leftInteractionCoefficient_mem_leftInteractionAlgebra
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (a a' : A) :
    leftInteractionCoefficient P a a' ∈ leftInteractionAlgebra P := by
  apply StarAlgebra.subset_adjoin
  exact ⟨a, a', rfl⟩
theorem rightInteractionCoefficient_mem_rightInteractionAlgebra
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (c c' : C) :
    rightInteractionCoefficient Q c c' ∈ rightInteractionAlgebra Q := by
  apply StarAlgebra.subset_adjoin
  exact ⟨c, c', rfl⟩
theorem orthogonalComplement_invariant_of_adjoint_closed
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (operators : Set (Semantics.Operator B))
    (hadjoint : ∀ ⦃operator : Semantics.Operator B⦄,
      operator ∈ operators → LinearMap.adjoint operator ∈ operators)
    {W : Submodule Complex B}
    (hinvariant : ∀ ⦃operator : Semantics.Operator B⦄,
      operator ∈ operators → ∀ ⦃vector : B⦄, vector ∈ W → operator vector ∈ W) :
    ∀ ⦃operator : Semantics.Operator B⦄,
      operator ∈ operators → ∀ ⦃vector : B⦄, vector ∈ Wᗮ → operator vector ∈ Wᗮ := by
  intro operator hoperator vector hvector
  rw [Submodule.mem_orthogonal]
  intro witness hwitness
  rw [← LinearMap.adjoint_inner_left]
  have hadjointWitness : LinearMap.adjoint operator witness ∈ W :=
    hinvariant (operator := LinearMap.adjoint operator) (hadjoint hoperator) hwitness
  exact (Submodule.mem_orthogonal W vector).mp hvector
    (LinearMap.adjoint operator witness) hadjointWitness
instance starSubalgebraComplexScalarTower
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    IsScalarTower Complex S B where
  smul_assoc scalar operator vector := by
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
instance starSubalgebraComplexSMulCommClass
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    SMulCommClass S Complex B where
  smul_comm operator scalar vector := by
    change (operator : Semantics.Operator B) (scalar • vector) =
      scalar • (operator : Semantics.Operator B) vector
    exact (operator : Semantics.Operator B).map_smul scalar vector
instance starSubalgebraSubmoduleComplexModule
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B) :
    Module Complex W :=
  Module.compHom W (algebraMap Complex S)
def starSubalgebraSubmoduleComplexInclusion
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B) :
    W →ₗ[Complex] B where
  toFun := Subtype.val
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro scalar vector
    change ((algebraMap Complex S scalar : S) • (vector : W) : B) = scalar • (vector : B)
    change ((algebraMap Complex (Semantics.Operator B) scalar : Semantics.Operator B) : B →ₗ[Complex] B)
      vector = scalar • (vector : B)
    simp
noncomputable def starSubalgebraOrthogonalComplement
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) : Submodule S B := by
  letI : IsScalarTower Complex S B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  let W0 : Submodule Complex B := W.restrictScalars Complex
  refine
    { carrier := W0ᗮ
      zero_mem' := (W0ᗮ).zero_mem
      add_mem' := fun left right => (W0ᗮ).add_mem left right
      smul_mem' := ?_ }
  intro operator vector hvector
  change (operator : Semantics.Operator B) vector ∈ W0ᗮ
  refine orthogonalComplement_invariant_of_adjoint_closed (B := B)
    (operators := (S : Set (Semantics.Operator B))) ?_ ?_ operator.property hvector
  · intro member hmember
    change LinearMap.adjoint member ∈ S
    rw [← LinearMap.star_eq_adjoint]
    exact StarMemClass.star_mem hmember
  · intro member hmember witness hwitness
    exact W.smul_mem ⟨member, hmember⟩ hwitness
noncomputable def isotypicLeftAction
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (component : isotypicComponents S B) (operator : S) :
    Semantics.Operator (component.1.restrictScalars Complex) where
  toFun := fun vector => operator • vector
  map_add' := by
    intro left right
    exact smul_add operator left right
  map_smul' := by
    intro scalar vector
    exact smul_comm operator scalar vector
noncomputable def overlapProjectorOnIsotypicComponent
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Semantics.Operator
      (Semantics.CompositeSystem A (component.1.restrictScalars Complex)) :=
  let inclusion := (component.1.restrictScalars Complex).subtype
  (TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint inclusion)).comp
    (P.comp (TensorProduct.map (1 : Semantics.Operator A) inclusion))
noncomputable def isotypicLeftActionOnCopies
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    Semantics.Operator (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) where
  toFun := fun vector => operator • vector
  map_add' := by
    intro left right
    exact smul_add operator left right
  map_smul' := by
    intro scalar vector
    exact smul_comm operator scalar vector
noncomputable def isotypicLeftActionOnSimple
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (operator : S) :
    Semantics.Operator (W.restrictScalars Complex) where
  toFun := fun vector => operator • vector
  map_add' := by
    intro left right
    exact smul_add operator left right
  map_smul' := by
    intro scalar vector
    exact smul_comm operator scalar vector
noncomputable def isotypicTensorLeftAction
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    Semantics.Operator
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) :=
  TensorProduct.map (isotypicLeftActionOnSimple S W operator)
    (1 : Semantics.Operator (EuclideanSpace Complex (Fin n)))
noncomputable def isotypicCopyTensorCoordinates
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) :
    (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) ≃ₗ[Complex]
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) :=
  let W0 := W.restrictScalars Complex
  let coordinates : (PiLp 2 (fun _ : Fin n => W0)) ≃ₗ[Complex]
      (Fin n → W0) :=
    (PiLp.continuousLinearEquiv 2 Complex (fun _ : Fin n => W0)).toLinearEquiv
  let euclideanCoordinates : (EuclideanSpace Complex (Fin n)) ≃ₗ[Complex]
      (Fin n → Complex) :=
    (EuclideanSpace.equiv (Fin n) Complex).toLinearEquiv
  coordinates.trans
    ((TensorProduct.piScalarRight Complex Complex W0 (Fin n)).symm.trans
      (TensorProduct.congr (LinearEquiv.refl Complex W0) euclideanCoordinates.symm))
theorem isotypicCopyTensorCoordinates_single
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (i : Fin n) (w : W.restrictScalars Complex) :
    isotypicCopyTensorCoordinates S W n (PiLp.single 2 i w) =
      w ⊗ₜ[Complex] EuclideanSpace.single i 1 := by
  change (TensorProduct.congr (LinearEquiv.refl Complex (W.restrictScalars Complex))
      ((EuclideanSpace.equiv (Fin n) Complex).toLinearEquiv.symm))
      ((TensorProduct.piScalarRight Complex Complex (W.restrictScalars Complex) (Fin n)).symm
        (Pi.single i w)) = _
  rw [TensorProduct.piScalarRight_symm_single]
  rw [TensorProduct.congr_tmul]
  rfl
noncomputable def isotypicMultiplicityMatrixOperator (n : Nat)
    (matrix : Matrix (Fin n) (Fin n) Complex) :
    Semantics.Operator (EuclideanSpace Complex (Fin n)) :=
  let coordinates : (EuclideanSpace Complex (Fin n)) ≃ₗ[Complex]
      (Fin n → Complex) :=
    (EuclideanSpace.equiv (Fin n) Complex).toLinearEquiv
  coordinates.symm.toLinearMap.comp
    ((Matrix.toLin' matrix).comp coordinates.toLinearMap)
noncomputable def isotypicMultiplicityMatrixActionOnCopies
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex) :
    Semantics.Operator (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) :=
  let W0 := W.restrictScalars Complex
  let coordinates : (PiLp 2 (fun _ : Fin n => W0)) ≃ₗ[Complex]
      (Fin n → W0) :=
    (PiLp.continuousLinearEquiv 2 Complex (fun _ : Fin n => W0)).toLinearEquiv
  let action : (Fin n → W0) →ₗ[Complex] (Fin n → W0) :=
    (endVecRingEquivMatrixEnd (Fin n) Complex W0).symm
      (fun row column => matrix row column • (1 : Module.End Complex W0))
  coordinates.symm.toLinearMap.comp (action.comp coordinates.toLinearMap)
noncomputable def isotypicSimpleFactorCoordinate
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B) :
    W ≃ₗ[Complex] W.restrictScalars Complex where
  toFun := fun vector => ⟨vector, vector.property⟩
  invFun := fun vector => ⟨vector, vector.property⟩
  left_inv := by
    intro vector
    rfl
  right_inv := by
    intro vector
    rfl
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar vector
    rfl
theorem isotypicSimpleFactorCoordinate_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (operator : S) (vector : W) :
    isotypicSimpleFactorCoordinate S W (operator • vector) =
      isotypicLeftActionOnSimple S W operator (isotypicSimpleFactorCoordinate S W vector) := by
  rfl
noncomputable def isotypicLeftActionOnFunctionCopies
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    Module.End Complex (Fin n → W) where
  toFun := fun vector => operator • vector
  map_add' := by
    intro left right
    exact smul_add operator left right
  map_smul' := by
    intro scalar vector
    ext index
    change (operator : Semantics.Operator B) (scalar • (vector index : B)) =
      scalar • (operator : Semantics.Operator B) (vector index : B)
    exact (operator : Semantics.Operator B).map_smul scalar (vector index : B)
noncomputable def isotypicSimpleCopyTensorCoordinates
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) :
    (Fin n → W) ≃ₗ[Complex]
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) :=
  let piFactorTransport : (Fin n → W) ≃ₗ[Complex]
      (Fin n → W.restrictScalars Complex) :=
    LinearEquiv.piCongrRight (fun _ => isotypicSimpleFactorCoordinate S W)
  let rawEquiv : (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) ≃ₗ[Complex]
      (Fin n → W.restrictScalars Complex) :=
    (PiLp.continuousLinearEquiv 2 Complex
      (fun _ : Fin n => W.restrictScalars Complex)).toLinearEquiv
  piFactorTransport.trans
    (rawEquiv.symm.trans (isotypicCopyTensorCoordinates S W n))
theorem isotypicSimpleCopyTensorCoordinates_single
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (i : Fin n) (w : W) :
    isotypicSimpleCopyTensorCoordinates S W n (Pi.single i w) =
      isotypicSimpleFactorCoordinate S W w ⊗ₜ[Complex] EuclideanSpace.single i 1 := by
  change isotypicCopyTensorCoordinates S W n
      (PiLp.single 2 i (isotypicSimpleFactorCoordinate S W w)) = _
  rw [isotypicCopyTensorCoordinates_single]
theorem isotypicSimpleCopyTensorCoordinates_apply
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (vector : Fin n → W) :
    isotypicSimpleCopyTensorCoordinates S W n vector =
      ∑ i, isotypicSimpleFactorCoordinate S W (vector i) ⊗ₜ[Complex]
        EuclideanSpace.single i 1 := by
  have hvector : (∑ i, Pi.single i (vector i)) = vector := Finset.univ_sum_single vector
  conv_lhs => rw [← hvector]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact isotypicSimpleCopyTensorCoordinates_single S W n i (vector i)
theorem isotypicSimpleCopyTensorCoordinates_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    (isotypicSimpleCopyTensorCoordinates S W n).toLinearMap.comp
        (isotypicLeftActionOnFunctionCopies S W n operator) =
      (isotypicTensorLeftAction S W n operator).comp
        (isotypicSimpleCopyTensorCoordinates S W n).toLinearMap := by
  apply LinearMap.ext
  intro vector
  change isotypicSimpleCopyTensorCoordinates S W n (operator • vector) =
    isotypicTensorLeftAction S W n operator
      (isotypicSimpleCopyTensorCoordinates S W n vector)
  rw [isotypicSimpleCopyTensorCoordinates_apply,
    isotypicSimpleCopyTensorCoordinates_apply]
  simp only [map_sum, TensorProduct.map_tmul, Module.End.one_apply]
  apply Finset.sum_congr rfl
  intro i _
  change isotypicSimpleFactorCoordinate S W (operator • vector i) ⊗ₜ[Complex]
      EuclideanSpace.single i 1 =
    isotypicTensorLeftAction S W n operator
      (isotypicSimpleFactorCoordinate S W (vector i) ⊗ₜ[Complex]
        EuclideanSpace.single i 1)
  rw [isotypicSimpleFactorCoordinate_intertwines]
  simp [isotypicTensorLeftAction]
noncomputable def isotypicTensorCommutantPullback
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat)
    (T : Semantics.Operator
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)))
    (hcommute : ∀ operator : S, Commute T (isotypicTensorLeftAction S W n operator)) :
    Module.End S (Fin n → W) := by
  let E := isotypicSimpleCopyTensorCoordinates S W n
  exact
    { toFun := fun vector => E.symm (T (E vector))
      map_add' := by
        intro left right
        simp
      map_smul' := by
        intro operator vector
        apply E.injective
        change E (E.symm (T (E (operator • vector)))) =
          E ((RingHom.id S) operator • E.symm (T (E vector)))
        have hE : E (operator • vector) =
            isotypicTensorLeftAction S W n operator (E vector) := by
          simpa [isotypicLeftActionOnFunctionCopies, LinearMap.comp_apply] using
            congrArg (fun map : (Fin n → W) →ₗ[Complex]
                (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) =>
              map vector)
              (isotypicSimpleCopyTensorCoordinates_intertwines S W n operator)
        have hE' : E (operator • E.symm (T (E vector))) =
            isotypicTensorLeftAction S W n operator
              (T (E vector)) := by
          have hraw := congrArg (fun map : (Fin n → W) →ₗ[Complex]
                (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) =>
              map (E.symm (T (E vector))))
              (isotypicSimpleCopyTensorCoordinates_intertwines S W n operator)
          change E (operator • E.symm (T (E vector))) =
            isotypicTensorLeftAction S W n operator
              (E (E.symm (T (E vector)))) at hraw
          rw [E.apply_symm_apply] at hraw
          exact hraw
        have htransport : T (E (operator • vector)) =
            E (operator • E.symm (T (E vector))) := by
          calc
          T (E (operator • vector)) =
              T (isotypicTensorLeftAction S W n operator (E vector)) := by rw [hE]
          _ = isotypicTensorLeftAction S W n operator (T (E vector)) := by
              exact congrArg
                (fun map : Semantics.Operator
                    (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)) =>
                  map (E vector))
                (hcommute operator).eq
          _ = E (operator • E.symm (T (E vector))) := hE'.symm
        simpa only [E.apply_symm_apply, RingHom.id_apply] using htransport }
noncomputable def isotypicMultiplicityMatrixActionOnFunctionCopies
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex) :
    Module.End Complex (Fin n → W) :=
  (endVecRingEquivMatrixEnd (Fin n) Complex W).symm
    (fun row column => matrix row column • (1 : Module.End Complex W))
abbrev isotypicLiftedMultiplicity (n : Nat) : Type u :=
  EuclideanSpace Complex (ULift.{u} (Fin n))
noncomputable def isotypicMultiplicityLiftIsometry (n : Nat) :
    EuclideanSpace Complex (Fin n) ≃ₗᵢ[Complex]
      isotypicLiftedMultiplicity.{u} n :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex (Equiv.ulift).symm
noncomputable def isotypicMultiplicityLiftTensorUnitary
    (W : Type u) [NormedAddCommGroup W] [InnerProductSpace Complex W]
    [Semantics.FiniteQuantumSystem W] (n : Nat) :
    Semantics.UnitaryTransport
      (W ⊗[Complex] EuclideanSpace Complex (Fin n))
      (W ⊗[Complex] isotypicLiftedMultiplicity.{u} n) := by
  let e := (isotypicMultiplicityLiftIsometry.{u} n).lTensor W
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }
noncomputable def isotypicMultiplicityLiftConjOperator
    (n : Nat) (R : Semantics.Operator (EuclideanSpace Complex (Fin n))) :
    Semantics.Operator (isotypicLiftedMultiplicity.{u} n) :=
  (isotypicMultiplicityLiftIsometry.{u} n).toLinearEquiv.toLinearMap.comp
    (R.comp (isotypicMultiplicityLiftIsometry.{u} n).toLinearEquiv.symm.toLinearMap)
noncomputable def isotypicLiftedMultiplicityUnitVector (n : Nat) [NeZero n] :
    isotypicLiftedMultiplicity.{u} n :=
  EuclideanSpace.basisFun (ULift.{u} (Fin n)) Complex
    (ULift.up ⟨0, Nat.pos_of_neZero n⟩)
noncomputable def rightInteractionCoefficientOnIsotypicComponent
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C) :
    Module.End (leftInteractionAlgebra P) component.1 := by
  let coefficient := rightInteractionCoefficient Q c c'
  let coefficientEnd : Module.End (leftInteractionAlgebra P) B :=
    commutingOperatorAsModuleEnd (leftInteractionAlgebra P) coefficient (by
      intro operator
      exact interactionAlgebras_commute P Q hselfAdjoint hcommute operator.property
        (rightInteractionCoefficient_mem_rightInteractionAlgebra Q c c'))
  exact
    { toFun := fun vector =>
        ⟨coefficientEnd vector,
          (Submodule.IsFullyInvariant.of_mem_isotypicComponents component.2)
            coefficientEnd vector.property⟩
      map_add' := by
        intro left right
        apply Subtype.ext
        exact coefficientEnd.map_add left right
      map_smul' := by
        intro scalar vector
        apply Subtype.ext
        exact coefficientEnd.map_smul scalar vector }
noncomputable def rightInteractionCoefficientOnIsotypicComponentOperator
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C) :
    Semantics.Operator (component.1.restrictScalars Complex) := by
  let right := rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
    component c c'
  exact
    { toFun := fun vector => right vector
      map_add' := right.map_add
      map_smul' := by
        intro scalar vector
        apply Subtype.ext
        change rightInteractionCoefficient Q c c' (scalar • (vector : B)) =
          scalar • rightInteractionCoefficient Q c c' (vector : B)
        exact (rightInteractionCoefficient Q c c').map_smul scalar (vector : B) }
noncomputable def overlapRightProjectorOnIsotypicComponent
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Semantics.Operator
      (Semantics.CompositeSystem (component.1.restrictScalars Complex) C) :=
  overlapRightCompression Q (component.1.restrictScalars Complex).subtype
def OverlapProjectorTensorBlockFactorization
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (component : isotypicComponents (leftInteractionAlgebra P) B) : Prop :=
  ∃ (n : Nat) (hn : NeZero n) (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)),
    letI : NeZero n := hn
    ∃ (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
        (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A (W.restrictScalars Complex)))
      (Qright : Semantics.Operator
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{u} n) C)),
      (unitaryLTensor A U).conjOperator
        (overlapProjectorOnIsotypicComponent P component) =
        rightTensorExtensionAfterLeft A (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) Pleft ∧
      (unitaryRTensor U C).conjOperator
        (overlapRightProjectorOnIsotypicComponent P Q component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) C Qright
noncomputable def leftIsotypicSectorProjector
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Semantics.Operator B := by
  letI : IsScalarTower Complex (leftInteractionAlgebra P) B := by
    constructor
    intro scalar operator vector
    change ((scalar • (operator : Semantics.Operator B)) : Semantics.Operator B) vector =
      scalar • (operator : Semantics.Operator B) vector
    simp
  exact (component.1.restrictScalars Complex).starProjection.toLinearMap
def quditLabelRelabel
    {I J : Type u} [Fintype I] [Fintype J]
    {q : I → Nat} {r : J → Nat} (e : I ≃ J)
    (hdim : ∀ i, q i = r (e i)) :
    Semantics.Qudit.Label q ≃ Semantics.Qudit.Label r where
  toFun := fun labels j =>
    Fin.cast ((hdim (e.symm j)).trans (congrArg r (e.apply_symm_apply j)))
      (labels (e.symm j))
  invFun := fun labels i => Fin.cast (hdim i).symm (labels (e i))
  left_inv := by
    intro labels
    funext i
    apply Fin.ext
    change (labels (e.symm (e i))).val = (labels i).val
    rw [e.symm_apply_apply]
  right_inv := by
    intro labels
    funext j
    apply Fin.ext
    change (labels (e (e.symm j))).val = (labels j).val
    rw [e.apply_symm_apply]
noncomputable def quditCoordinateRelabel
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {q : I → Nat} {r : J → Nat} (e : I ≃ J)
    (hdim : ∀ i, q i = r (e i)) :
    Semantics.UnitaryTransport (Semantics.Qudit.QuditRegister q)
      (Semantics.Qudit.QuditRegister r) := by
  let sourceBasis := EuclideanSpace.basisFun (Semantics.Qudit.Label q) Complex
  let targetBasis := EuclideanSpace.basisFun (Semantics.Qudit.Label r) Complex
  let U := sourceBasis.equiv targetBasis (quditLabelRelabel e hdim)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def pureFactorTensorComplementProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (phi : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Semantics.Operator (M.regionSubsystem region).complementSystem) :
    Semantics.Operator L.Register :=
  (M.regionSubsystem region).registerFactorization.symm.conjOperator
    (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap complementProjector)
end BPTCommutingProjectorModel
end Bounds
end QEC


