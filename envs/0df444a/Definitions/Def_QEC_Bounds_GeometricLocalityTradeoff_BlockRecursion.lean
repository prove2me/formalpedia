-- Prove2me | Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
-- name    : QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:18:48.786952+00:00
-- url     : https://prove2.me/theorems/3f82aceb-3965-468f-988a-634a8756e7c1
-- title:
--   Block Recursion
-- statement:
--   Definitions and structural lemmas for Block Recursion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
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
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul_tmul
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
namespace BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
noncomputable def prepareLeftBranch (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : H) : K →ₗ[Complex] CompositeSystem H K :=
  TensorProduct.mk Complex H K v
@[simp] theorem prepareLeftBranch_apply (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : H) (k : K) :
    prepareLeftBranch H K v k = v ⊗ₜ[Complex] k := rfl
theorem adjoint_prepareLeftBranch_comp (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : H) :
    (LinearMap.adjoint (prepareLeftBranch H K v)).comp (prepareLeftBranch H K v) =
      (inner Complex v v) • (1 : Operator K) := by
  apply LinearMap.ext
  intro k
  apply (ext_iff_inner_left Complex).mpr
  intro l
  change inner Complex l (LinearMap.adjoint (prepareLeftBranch H K v)
    (prepareLeftBranch H K v k)) =
      inner Complex l (((inner Complex v v) • (1 : Operator K)) k)
  rw [LinearMap.adjoint_inner_right]
  simp [prepareLeftBranch, TensorProduct.inner_tmul]
noncomputable def prepareLeftKraus (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {m : Nat} (vectors : Fin m -> H) :
    FiniteKrausFamily (Fin m) K (CompositeSystem H K) where
  operator i := prepareLeftBranch H K (vectors i)
theorem prepareLeftKraus_complete (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {m : Nat} (vectors : Fin m -> H)
    (htrace : ∑ i, inner Complex (vectors i) (vectors i) = 1) :
    (prepareLeftKraus H K vectors).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [prepareLeftKraus, adjoint_prepareLeftBranch_comp]
  apply LinearMap.ext
  intro k
  calc
    (∑ i, (inner Complex (vectors i) (vectors i) • (1 : Operator K))) k =
        (∑ i, inner Complex (vectors i) (vectors i)) • k := by
          simp [Finset.sum_smul]
    _ = k := by rw [htrace]; simp
theorem density_exists_rankOne_ensemble {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) :
    ∃ (m : Nat) (vectors : Fin m -> H),
      rho.toOperator = ∑ i,
        (InnerProductSpace.rankOne Complex (vectors i) (vectors i)).toLinearMap := by
  have hpositive : (LinearMap.toContinuousLinearMap rho.toOperator).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff rho.toOperator).2 rho.positive
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).1 hpositive with
    ⟨m, vectors, hvectors⟩
  refine ⟨m, vectors, ?_⟩
  simpa using congrArg ContinuousLinearMap.toLinearMap hvectors
noncomputable def densityEnsembleSize (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) : Nat :=
  Classical.choose (density_exists_rankOne_ensemble rho)
noncomputable def densityEnsembleVectors (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) : Fin (densityEnsembleSize H rho) -> H :=
  Classical.choose (Classical.choose_spec (density_exists_rankOne_ensemble rho))
theorem densityEnsemble_specification (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) :
    rho.toOperator = ∑ i,
      (InnerProductSpace.rankOne Complex (densityEnsembleVectors H rho i)
        (densityEnsembleVectors H rho i)).toLinearMap :=
  Classical.choose_spec (Classical.choose_spec (density_exists_rankOne_ensemble rho))
theorem densityEnsemble_trace_one (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (rho : DensityOperator H) :
    ∑ i, inner Complex (densityEnsembleVectors H rho i)
      (densityEnsembleVectors H rho i) = 1 := by
  have htrace := rho.trace_one
  rw [densityEnsemble_specification] at htrace
  simpa [map_sum, InnerProductSpace.trace_rankOne] using htrace
noncomputable def prepareLeft (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) : QuantumChannel K (CompositeSystem H K) :=
  (prepareLeftKraus H K (densityEnsembleVectors H rho)).toQuantumChannel
    (prepareLeftKraus_complete H K (densityEnsembleVectors H rho)
      (densityEnsemble_trace_one H rho))
noncomputable def complementExtension {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι -> Nat} (S : QuditSubsystem q) (A : Operator S.complementSystem) :
    Operator (Qudit.QuditRegister q) :=
  S.registerFactorization.symm.conjOperator
    (TensorProduct.map (1 : Operator S.selectedSystem) A)
noncomputable def abcdToBcad
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [FiniteQuantumSystem D] :
    UnitaryTransport
      (CompositeSystem A (CompositeSystem B (CompositeSystem C D)))
      (CompositeSystem B (CompositeSystem C (CompositeSystem A D))) :=
  composeUnitaryTransport
    (BPTEntropy.abcToBac A B (CompositeSystem C D))
    (unitaryLTensor B (BPTEntropy.abcToBac A C D))
@[simp] theorem abcdToBcad_apply_tmul
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [FiniteQuantumSystem D]
    (a : A) (b : B) (c : C) (d : D) :
    abcdToBcad A B C D (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d))) =
      b ⊗ₜ[Complex] (c ⊗ₜ[Complex] (a ⊗ₜ[Complex] d)) := by
  simp [abcdToBcad, composeUnitaryTransport_apply]
noncomputable def traceBCToAD
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [FiniteQuantumSystem D] :
    Operator (CompositeSystem A (CompositeSystem B (CompositeSystem C D))) →ₗ[Complex]
      Operator (CompositeSystem A D) :=
  (FiniteMatrixEntropy.partialTraceLeftRaw C (CompositeSystem A D)).comp
    ((FiniteMatrixEntropy.partialTraceLeftRaw B (CompositeSystem C (CompositeSystem A D))).comp
      (abcdToBcad A B C D).conjOperatorLinearMap)
abbrev recursionA (M : BPTCommutingProjectorModel L kappa)
    (region inside : Finset L.Site) : QuditSubsystem L.localDimension :=
  M.regionSubsystem (region \ inside)
abbrev recursionAB (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : QuditSubsystem L.localDimension :=
  M.regionSubsystem region
abbrev recursionABC (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site) : QuditSubsystem L.localDimension :=
  BPTEntropy.QuditSubsystem.unionSubsystem
    (M.regionSubsystem (region \ inside)) (M.regionSubsystem (inside ∪ outside))
theorem recursionA_subset_region
    (M : BPTCommutingProjectorModel L kappa) (region inside : Finset L.Site) :
    (recursionA M region inside).selected ⊆ (recursionAB M region).selected := by
  simpa [recursionA, recursionAB] using
    fun site hsite => (Finset.mem_sdiff.mp hsite).1
theorem recursionAB_subset_ABC
    (M : BPTCommutingProjectorModel L kappa) (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) :
    (recursionAB M region).selected ⊆ (recursionABC M region inside outside).selected := by
  change region ⊆ (region \ inside) ∪ (inside ∪ outside)
  intro site hsite
  by_cases hsiteInside : site ∈ inside
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hsiteInside)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hsite, hsiteInside⟩)
noncomputable def recursionFourFactorTransport
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) :
    UnitaryTransport L.Register
      (CompositeSystem
        (M.regionSubsystem (region \ inside)).selectedSystem
        (CompositeSystem
          ((M.regionSubsystem (region \ inside)).additionalRetainedSystem
            (M.regionSubsystem region))
          (CompositeSystem
            ((M.regionSubsystem region).additionalRetainedSystem
              (recursionABC M region inside outside))
            (recursionABC M region inside outside).complementSystem))) := by
  let A := M.regionSubsystem (region \ inside)
  let AB := M.regionSubsystem region
  let ABC := recursionABC M region inside outside
  have hAAB : A.selected ⊆ AB.selected := by
    simpa [A, AB] using fun site hsite => (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    simpa [AB, ABC] using recursionAB_subset_ABC M region inside outside hinside
  let splitAB := A.selectedFactorization AB hAAB
  let splitCD := AB.complementFactorization ABC hABABC
  exact composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport AB.registerFactorization
        (unitaryRTensor splitAB AB.complementSystem))
      (unitaryLTensor (CompositeSystem A.selectedSystem
        (A.additionalRetainedSystem AB)) splitCD))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))
noncomputable def recursionABState
    (M : BPTCommutingProjectorModel L kappa)
    (region inside : Finset L.Site)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (hregionalState : ‖regionalState‖ = 1) :
    DensityOperator (CompositeSystem
      (recursionA M region inside).selectedSystem
      ((recursionA M region inside).additionalRetainedSystem (recursionAB M region))) :=
  ((recursionA M region inside).selectedFactorization (recursionAB M region)
    (recursionA_subset_region M region inside)).conjDensity
      (pureDensity regionalState (by simpa [hregionalState]))
noncomputable def recursionCDOperator
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site) (hinside : inside ⊆ region)
    (A : Operator (M.regionSubsystem region).complementSystem) :
    Operator (CompositeSystem
      ((recursionAB M region).additionalRetainedSystem (recursionABC M region inside outside))
      (recursionABC M region inside outside).complementSystem) :=
  ((recursionAB M region).complementFactorization (recursionABC M region inside outside)
    (recursionAB_subset_ABC M region inside outside hinside)).conjOperator A
noncomputable def recursionLeftState
    (M : BPTCommutingProjectorModel L kappa)
    (region inside : Finset L.Site) (hinside : inside ⊆ region)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (hregionalState : ‖regionalState‖ = 1) :
    DensityOperator (M.regionSubsystem (region \ inside)).selectedSystem := by
  let A := M.regionSubsystem (region \ inside)
  let AB := M.regionSubsystem region
  have hAAB : A.selected ⊆ AB.selected := by
    simpa [A, AB] using fun site hsite => (Finset.mem_sdiff.mp hsite).1
  exact DensityOperator.rightMarginal
    ((A.selectedFactorization AB hAAB).conjDensity
      (pureDensity regionalState (by simpa [hregionalState])))
noncomputable def recursionPreparation
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) (houtside : outside ⊆ regionᶜ)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (hregionalState : ‖regionalState‖ = 1) :
    QuantumChannel
      (BPTEntropy.QuditSubsystem.unionSubsystem
        (M.regionSubsystem (region \ inside))
        (M.regionSubsystem (inside ∪ outside))).complementSystem
      (M.regionSubsystem (inside ∪ outside)).complementSystem := by
  let A := M.regionSubsystem (region \ inside)
  let BC := M.regionSubsystem (inside ∪ outside)
  have hdisjoint : Disjoint A.selected BC.selected := by
    rw [Finset.disjoint_left]
    intro site hA hBC
    rcases Finset.mem_union.mp hBC with hinsideSite | houtsideSite
    · exact (Finset.mem_sdiff.mp hA).2 hinsideSite
    · exact (Finset.mem_compl.mp (houtside houtsideSite)) (Finset.mem_sdiff.mp hA).1
  exact QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (BPTEntropy.QuditSubsystem.complementBACFactorization A BC hdisjoint).symm)
    (prepareLeft _ _ (recursionLeftState M region inside hinside regionalState hregionalState))
end BPTCommutingProjectorModel
end Bounds
end QEC


