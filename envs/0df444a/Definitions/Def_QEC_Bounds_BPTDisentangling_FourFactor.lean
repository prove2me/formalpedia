-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
-- name    : QEC_Bounds_BPTDisentangling_FourFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:13:36.871713+00:00
-- url     : https://prove2.me/theorems/ee5d266a-9308-4ee2-a11e-658a39abafc6
-- title:
--   Four Factor
-- statement:
--   Definitions and structural lemmas for Four Factor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_eq_internal_union_external
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_disjoint_region
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_externalBoundary_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_supported_on
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_support_subset_boundary_of_couples
import Theorems.Thm_QEC_Bounds_localExtension_comp
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_complementFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_splitComplementLabel_splitLabel_second
import Theorems.Thm_QEC_Semantics_QuditSubsystem_splitSelectedLabel_splitLabel
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
inductive Disentangled (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Prop where
  | intro
      (unitary : Semantics.UnitaryTransport L.Register L.Register)
      (regionalState : (M.regionSubsystem region).selectedSystem)
      (complementProjector : Semantics.Operator (M.regionSubsystem region).complementSystem)
      (unitary_supported : M.UnitarySupportedOn (M.boundary region) unitary)
      (regionalState_normalized : ‖regionalState‖ = 1)
      (complementProjector_isSymmetricProjection : complementProjector.IsSymmetricProjection)
      (projector_factorization :
        unitary.conjOperator M.fullCodeProjector =
          M.pureFactorTensorComplementProjector region regionalState complementProjector)
noncomputable def identityUnitary (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H] :
    Semantics.UnitaryTransport H H where
  toLinearEquiv := LinearEquiv.refl Complex H
  map_inner := by simp
noncomputable def regionZeroVector (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.regionSubsystem region).selectedSystem :=
  EuclideanSpace.basisFun
    (Semantics.Qudit.Label (M.regionSubsystem region).selectedDimensions) Complex
    (Semantics.Qudit.zeroLabel (M.regionSubsystem region).selectedDimensions (by
      intro site
      exact L.localDimension_positive site))
noncomputable def nestedFactorizationLeft
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem S.selectedSystem
        (Semantics.CompositeSystem (S.additionalRetainedSystem T) T.complementSystem)) := by
  let e := S.registerFactorization.toLinearIsometryEquiv.trans
    ((S.complementFactorization T hST).toLinearIsometryEquiv.lTensor S.selectedSystem)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }
noncomputable def nestedFactorizationRight
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem S.selectedSystem
        (Semantics.CompositeSystem (S.additionalRetainedSystem T) T.complementSystem)) := by
  let splitSelected :=
    (S.selectedFactorization T hST).toLinearIsometryEquiv.rTensor T.complementSystem
  let reassociate := TensorProduct.assocIsometry Complex S.selectedSystem
    (S.additionalRetainedSystem T) T.complementSystem
  let e := T.registerFactorization.toLinearIsometryEquiv.trans
    (splitSelected.trans reassociate)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }
theorem nestedFactorizationLeft_apply_basis
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (labels : Semantics.Qudit.Label L.localDimension) :
    nestedFactorizationLeft S T hST
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun (Semantics.Qudit.Label S.selectedDimensions) Complex
        (S.splitLabel labels).1) ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Semantics.Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitComplementLabel T hST (S.splitLabel labels).2).1) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Semantics.Qudit.Label T.complementDimensions) Complex
          (S.splitComplementLabel T hST (S.splitLabel labels).2).2)) := by
  dsimp [nestedFactorizationLeft]
  rw [S.registerFactorization_apply_basis]
  simp only [LinearEquiv.lTensor_tmul]
  rw [S.complementFactorization_apply_basis T hST]
theorem nestedFactorizationRight_apply_basis
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (labels : Semantics.Qudit.Label L.localDimension) :
    nestedFactorizationRight S T hST
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun (Semantics.Qudit.Label S.selectedDimensions) Complex
        (S.splitSelectedLabel T hST (T.splitLabel labels).1).1) ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Semantics.Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitSelectedLabel T hST (T.splitLabel labels).1).2) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Semantics.Qudit.Label T.complementDimensions) Complex
          (T.splitLabel labels).2)) := by
  dsimp [nestedFactorizationRight]
  rw [T.registerFactorization_apply_basis]
  simp only [LinearEquiv.rTensor_tmul]
  rw [S.selectedFactorization_apply_basis T hST]
  rw [TensorProduct.assoc_tmul]
theorem nestedFactorization_toLinearEquiv_eq
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected) :
    (nestedFactorizationLeft S T hST).toLinearEquiv =
      (nestedFactorizationRight S T hST).toLinearEquiv := by
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  change nestedFactorizationLeft S T hST
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
    nestedFactorizationRight S T hST
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
  rw [nestedFactorizationLeft_apply_basis, nestedFactorizationRight_apply_basis]
  simp only [S.splitSelectedLabel_splitLabel T hST,
    S.splitComplementLabel_splitLabel_second T hST]
noncomputable def liftLocalToLarger
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (A : Semantics.Operator S.selectedSystem) : Semantics.Operator T.selectedSystem :=
  (S.selectedFactorization T hST).symm.conjOperator
    (TensorProduct.map A (1 : Semantics.Operator (S.additionalRetainedSystem T)))
theorem extendLocalToRegister_liftLocalToLarger
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (A : Semantics.Operator S.selectedSystem) :
    T.extendLocalToRegister (liftLocalToLarger S T hST A) = S.extendLocalToRegister A := by
  let basis := EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex
  apply basis.toBasis.ext
  intro labels
  apply (nestedFactorizationLeft S T hST).toLinearEquiv.injective
  have hNested := nestedFactorization_toLinearEquiv_eq S T hST
  conv_lhs => rw [hNested]
  dsimp [nestedFactorizationLeft, nestedFactorizationRight,
    Semantics.QuditSubsystem.extendLocalToRegister,
    Semantics.QuditSubsystem.extendLocal, liftLocalToLarger]
  simp only [LinearEquiv.apply_symm_apply]
  rw [T.registerFactorization_apply_basis, S.registerFactorization_apply_basis]
  simp only [TensorProduct.map_tmul, LinearEquiv.rTensor_tmul, LinearEquiv.lTensor_tmul,
    Semantics.UnitaryTransport.conjOperator_apply]
  simp only [Semantics.UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm, LinearMap.id_apply]
  rw [S.selectedFactorization_apply_basis T hST,
    S.complementFactorization_apply_basis T hST]
  simp only [TensorProduct.map_tmul, Module.End.one_apply]
  rw [TensorProduct.assoc_tmul]
  simp only [S.splitSelectedLabel_splitLabel T hST,
    S.splitComplementLabel_splitLabel_second T hST]
theorem operatorSupportedOnRegister_of_subset
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    {A : Semantics.Operator L.Register}
    (hA : S.OperatorSupportedOnRegister A) : T.OperatorSupportedOnRegister A := by
  rcases hA with ⟨localA, hlocalA⟩
  refine ⟨liftLocalToLarger S T hST localA, ?_⟩
  rw [extendLocalToRegister_liftLocalToLarger]
  exact hlocalA
theorem projector_supportedOnRegister_of_support_subset
    (M : BPTCommutingProjectorModel L kappa) (check : kappa) (region : Finset L.Site)
    (hsupport : M.support check ⊆ region) :
    (M.regionSubsystem region).OperatorSupportedOnRegister (M.projector check) := by
  apply operatorSupportedOnRegister_of_subset (L.subsystem (M.support check))
    (M.regionSubsystem region)
  · simpa [BPTCommutingProjectorModel.regionSubsystem] using hsupport
  · exact M.projector_supported_on check
noncomputable def interior (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset L.Site :=
  region \ M.internalBoundary region
noncomputable def exterior (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset L.Site :=
  regionᶜ \ M.externalBoundary region
theorem interior_eq_region_sdiff_boundary (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    M.interior region = region \ M.boundary region := by
  ext site
  simp [interior, internalBoundary]
theorem region_eq_interior_union_internalBoundary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    region = M.interior region ∪ M.internalBoundary region := by
  ext site
  constructor
  · intro hregion
    by_cases hboundary : site ∈ M.internalBoundary region
    · exact Finset.mem_union_right _ hboundary
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hregion, hboundary⟩)
  · intro h
    rcases Finset.mem_union.mp h with hinterior | hboundary
    · exact (Finset.mem_sdiff.mp hinterior).1
    · exact (Finset.mem_inter.mp hboundary).2
theorem complement_eq_externalBoundary_union_exterior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    regionᶜ = M.externalBoundary region ∪ M.exterior region := by
  ext site
  constructor
  · intro hcomplement
    by_cases hboundary : site ∈ M.externalBoundary region
    · exact Finset.mem_union_left _ hboundary
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hcomplement, hboundary⟩)
  · intro h
    rcases Finset.mem_union.mp h with hboundary | hexterior
    · exact Finset.mem_compl.mpr ((M.mem_externalBoundary_iff region site).mp hboundary |>.1)
    · exact (Finset.mem_sdiff.mp hexterior).1
noncomputable def fourFactorTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (M.regionSubsystem (M.interior region)).selectedSystem
        (Semantics.CompositeSystem
          ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
            (M.regionSubsystem region))
          (Semantics.CompositeSystem
            ((M.regionSubsystem region).additionalRetainedSystem
              (M.regionSubsystem (region ∪ M.externalBoundary region)))
            (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem))) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  exact composeUnitaryTransport
    (composeUnitaryTransport (nestedFactorizationLeft AB ABC hABABC)
      (unitaryRTensor splitAB
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))
noncomputable def fourFactorTransportFromRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (M.regionSubsystem (M.interior region)).selectedSystem
        (Semantics.CompositeSystem
          ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
            (M.regionSubsystem region))
          (Semantics.CompositeSystem
            ((M.regionSubsystem region).additionalRetainedSystem
              (M.regionSubsystem (region ∪ M.externalBoundary region)))
            (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem))) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  let splitCD := AB.complementFactorization ABC hABABC
  exact composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport AB.registerFactorization
        (unitaryRTensor splitAB AB.complementSystem))
      (unitaryLTensor (Semantics.CompositeSystem A.selectedSystem
        (A.additionalRetainedSystem AB)) splitCD))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))
abbrev fourFactorA (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem (M.interior region)).selectedSystem
abbrev fourFactorB (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem (M.interior region)).additionalRetainedSystem (M.regionSubsystem region)
abbrev fourFactorC (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem region).additionalRetainedSystem
    (M.regionSubsystem (region ∪ M.externalBoundary region))
abbrev fourFactorD (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) : Type :=
  (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem
abbrev fourFactorSystem (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Type :=
  Semantics.CompositeSystem (M.fourFactorA region)
    (Semantics.CompositeSystem (M.fourFactorB region)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
noncomputable def fourFactorBasisVector (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) (labels : Semantics.Qudit.Label L.localDimension) :
    M.fourFactorSystem region :=
  (EuclideanSpace.basisFun
      (Semantics.Qudit.Label
        (M.regionSubsystem (M.interior region)).selectedDimensions) Complex
      ((M.regionSubsystem (M.interior region)).splitSelectedLabel
        (M.regionSubsystem region)
        (by
          intro site hsite
          exact (Finset.mem_sdiff.mp hsite).1)
        ((M.regionSubsystem region).splitLabel labels).1).1)
    ⊗ₜ[Complex]
  ((EuclideanSpace.basisFun
      (Semantics.Qudit.Label
        ((M.regionSubsystem (M.interior region)).additionalRetainedDimensions
          (M.regionSubsystem region))) Complex
      ((M.regionSubsystem (M.interior region)).splitSelectedLabel
        (M.regionSubsystem region)
        (by
          intro site hsite
          exact (Finset.mem_sdiff.mp hsite).1)
        ((M.regionSubsystem region).splitLabel labels).1).2)
    ⊗ₜ[Complex]
    ((EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          ((M.regionSubsystem region).additionalRetainedDimensions
            (M.regionSubsystem (region ∪ M.externalBoundary region)))) Complex
        ((M.regionSubsystem region).splitComplementLabel
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            exact Finset.mem_union_left _ hsite)
          ((M.regionSubsystem region).splitLabel labels).2).1)
      ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
        ((M.regionSubsystem region).splitComplementLabel
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            exact Finset.mem_union_left _ hsite)
          ((M.regionSubsystem region).splitLabel labels).2).2)))
def fourFactorBCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    {site : L.Site // site ∈ M.internalBoundary region} ≃
      (M.regionSubsystem (M.interior region)).AdditionalRetainedCoordinates
        (M.regionSubsystem region) where
  toFun := fun site => ⟨site, by
    constructor
    · intro hinterior
      exact (Finset.mem_sdiff.mp hinterior).2 site.property
    · exact (Finset.mem_inter.mp site.property).2⟩
  invFun := fun site => ⟨site, by
    by_contra hnotinternal
    exact site.property.1 (Finset.mem_sdiff.mpr ⟨site.property.2, hnotinternal⟩)⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl
def fourFactorCCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    {site : L.Site // site ∈ M.externalBoundary region} ≃
      (M.regionSubsystem region).AdditionalRetainedCoordinates
        (M.regionSubsystem (region ∪ M.externalBoundary region)) where
  toFun := fun site => ⟨site, by
    constructor
    · intro hregion
      exact (Finset.disjoint_left.mp (M.externalBoundary_disjoint_region region))
        site.property hregion
    · exact Finset.mem_union_right _ site.property⟩
  invFun := fun site => ⟨site, by
    rcases Finset.mem_union.mp site.property.2 with hregion | hexternal
    · exact False.elim (site.property.1 hregion)
    · exact hexternal⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl
def fourFactorDCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    {site : L.Site // site ∈ M.exterior region} ≃
      (M.regionSubsystem (region ∪ M.externalBoundary region)).ComplementCoordinates where
  toFun := fun site => ⟨site, by
    intro hunion
    rcases Finset.mem_union.mp hunion with hregion | hexternal
    · exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp site.property).1) hregion
    · exact (Finset.mem_sdiff.mp site.property).2 hexternal⟩
  invFun := fun site => ⟨site, by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr ?_, ?_⟩
    · intro hregion
      exact site.property (Finset.mem_union_left _ hregion)
    · intro hexternal
      exact site.property (Finset.mem_union_right _ hexternal)⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl
set_option maxHeartbeats 800000 in
/-- The concrete internal-boundary register relabeled as the virtual `B` factor. -/
noncomputable def fourFactorBCoordinateRelabel (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.internalBoundary region)).selectedSystem
      ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
        (M.regionSubsystem region)) :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem (M.internalBoundary region)).selectedDimensions)
    (r := (M.regionSubsystem (M.interior region)).additionalRetainedDimensions
      (M.regionSubsystem region))
    (M.fourFactorBCoordinateEquiv region) (by
    intro site
    rfl)
set_option maxHeartbeats 800000 in
/-- The concrete external-boundary register relabeled as the virtual `C` factor. -/
noncomputable def fourFactorCCoordinateRelabel (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.externalBoundary region)).selectedSystem
      ((M.regionSubsystem region).additionalRetainedSystem
        (M.regionSubsystem (region ∪ M.externalBoundary region))) :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem (M.externalBoundary region)).selectedDimensions)
    (r := (M.regionSubsystem region).additionalRetainedDimensions
      (M.regionSubsystem (region ∪ M.externalBoundary region)))
    (M.fourFactorCCoordinateEquiv region) (by
    intro site
    rfl)
set_option maxHeartbeats 800000 in
/-- The source exterior register relabeled as the virtual `D` factor. -/
noncomputable def fourFactorDCoordinateRelabel (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.exterior region)).selectedSystem
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem (M.exterior region)).selectedDimensions)
    (r := (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions)
    (M.fourFactorDCoordinateEquiv region) (by
    intro site
    rfl)
def regionComplementCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).SelectedCoordinates ≃
      (M.regionSubsystem region).ComplementCoordinates where
  toFun := fun site => ⟨site, Finset.mem_compl.mp site.property⟩
  invFun := fun site => ⟨site, Finset.mem_compl.mpr site.property⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl
def regionDoubleComplementCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).ComplementCoordinates ≃
      (M.regionSubsystem region).SelectedCoordinates where
  toFun := fun site => ⟨site, by
    by_contra hnotregion
    exact site.property (Finset.mem_compl.mpr hnotregion)⟩
  invFun := fun site => ⟨site, by
    intro hcomplement
    exact (Finset.mem_compl.mp hcomplement) site.property⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl
set_option maxHeartbeats 800000 in
/-- Relabel the selected register of `regionᶜ` as the complement register of `region`. -/
noncomputable def regionComplementCoordinateRelabel (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem regionᶜ).selectedSystem
      (M.regionSubsystem region).complementSystem :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem regionᶜ).selectedDimensions)
    (r := (M.regionSubsystem region).complementDimensions)
    (M.regionComplementCoordinateEquiv region) (by
    intro site
    rfl)
set_option maxHeartbeats 800000 in
/-- Relabel the complement register of `regionᶜ` as the selected register of `region`. -/
noncomputable def regionDoubleComplementCoordinateRelabel
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem regionᶜ).complementSystem
      (M.regionSubsystem region).selectedSystem :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem regionᶜ).complementDimensions)
    (r := (M.regionSubsystem region).selectedDimensions)
    (M.regionDoubleComplementCoordinateEquiv region) (by
    intro site
    rfl)
noncomputable def extendComplementToRegister
    (S : Semantics.QuditSubsystem L.localDimension)
    (P : Semantics.Operator S.complementSystem) : Semantics.Operator L.Register :=
  S.registerFactorization.symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) P)
noncomputable def complementPartitionPostTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (M.regionSubsystem regionᶜ).selectedSystem
        (M.regionSubsystem regionᶜ).complementSystem)
      (Semantics.CompositeSystem
        (M.regionSubsystem region).selectedSystem
        (M.regionSubsystem region).complementSystem) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (unitaryRTensor (M.regionComplementCoordinateRelabel region)
        (M.regionSubsystem regionᶜ).complementSystem)
      (unitaryLTensor (M.regionSubsystem region).complementSystem
        (M.regionDoubleComplementCoordinateRelabel region)))
    (tensorSwapUnitary (M.regionSubsystem region).complementSystem
      (M.regionSubsystem region).selectedSystem)
noncomputable def complementPartitionTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (M.regionSubsystem region).selectedSystem
        (M.regionSubsystem region).complementSystem) :=
  composeUnitaryTransport (M.regionSubsystem regionᶜ).registerFactorization
    (M.complementPartitionPostTransport region)
noncomputable def fourFactorExtendAB
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem
      (M.fourFactorA region) (M.fourFactorB region))) :
    Semantics.Operator (M.fourFactorSystem region) := by
  let reassociate := TensorProduct.assocIsometry Complex (M.fourFactorA region)
    (M.fourFactorB region)
    (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
  let U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
      (M.fourFactorSystem region) :=
    { toLinearEquiv := reassociate.toLinearEquiv
      map_inner := reassociate.inner_map_map }
  exact U.conjOperator (TensorProduct.map P
    (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
noncomputable def fourFactorMiddleReassociate
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport (M.fourFactorSystem region)
      (Semantics.CompositeSystem (M.fourFactorA region)
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
          (M.fourFactorD region))) := by
  let reassociate := (TensorProduct.assocIsometry Complex (M.fourFactorB region)
    (M.fourFactorC region) (M.fourFactorD region)).symm
  let e := reassociate.lTensor (M.fourFactorA region)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := e.inner_map_map }
@[simp]
theorem fourFactorMiddleReassociate_symm_toLinearEquiv_apply_tmul
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (b : M.fourFactorB region)
    (c : M.fourFactorC region) (d : M.fourFactorD region) :
    (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        (a ⊗ₜ[Complex] ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] d)) =
      a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) := by
  rfl
noncomputable def fourFactorExtendBC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem
      (M.fourFactorB region) (M.fourFactorC region))) :
    Semantics.Operator (M.fourFactorSystem region) :=
  (M.fourFactorMiddleReassociate region).symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
      (TensorProduct.map P (1 : Semantics.Operator (M.fourFactorD region))))
noncomputable def fourFactorExtendCD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem
      ((M.regionSubsystem region).additionalRetainedSystem
        (M.regionSubsystem (region ∪ M.externalBoundary region)))
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem)) :
    Semantics.Operator (Semantics.CompositeSystem
      (M.regionSubsystem (M.interior region)).selectedSystem
      (Semantics.CompositeSystem
        ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
          (M.regionSubsystem region))
        (Semantics.CompositeSystem
          ((M.regionSubsystem region).additionalRetainedSystem
            (M.regionSubsystem (region ∪ M.externalBoundary region)))
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem))) :=
  TensorProduct.map (1 : Semantics.Operator
    (M.regionSubsystem (M.interior region)).selectedSystem)
    (TensorProduct.map (1 : Semantics.Operator
      ((M.regionSubsystem (M.interior region)).additionalRetainedSystem
        (M.regionSubsystem region))) P)
noncomputable def fourFactorCDCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem regionᶜ).selectedSystem
      (Semantics.CompositeSystem
        ((M.regionSubsystem region).additionalRetainedSystem
          (M.regionSubsystem (region ∪ M.externalBoundary region)))
        (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem) := by
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  exact composeUnitaryTransport (M.regionComplementCoordinateRelabel region)
    (AB.complementFactorization ABC hABABC)
def boundaryAdditionalCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.regionSubsystem (M.internalBoundary region)).AdditionalRetainedCoordinates
      (M.regionSubsystem (M.boundary region)) ≃
      (M.regionSubsystem region).AdditionalRetainedCoordinates
        (M.regionSubsystem (region ∪ M.externalBoundary region)) where
  toFun := fun site => ⟨site, by
    have hboundary : (site : L.Site) ∈
        M.internalBoundary region ∪ M.externalBoundary region := by
      rw [← M.boundary_eq_internal_union_external region]
      exact site.property.2
    rcases Finset.mem_union.mp hboundary with hinternal | hexternal
    · exact False.elim (site.property.1 hinternal)
    · constructor
      · intro hregion
        exact (Finset.disjoint_left.mp (M.externalBoundary_disjoint_region region))
          hexternal hregion
      · exact Finset.mem_union_right _ hexternal⟩
  invFun := fun site => ⟨site, by
    have hexternal : (site : L.Site) ∈ M.externalBoundary region := by
      rcases Finset.mem_union.mp site.property.2 with hregion | hexternal
      · exact False.elim (site.property.1 hregion)
      · exact hexternal
    constructor
    · intro hinternal
      exact site.property.1 (Finset.mem_inter.mp hinternal).2
    · rw [M.boundary_eq_internal_union_external region]
      exact Finset.mem_union_right _ hexternal⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl
def boundaryComplementAdditionalCoordinateEquiv
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region)).AdditionalRetainedCoordinates
      (M.regionSubsystem (region ∪ M.externalBoundary region)) ≃
      (M.regionSubsystem (M.interior region)).SelectedCoordinates where
  toFun := fun site => ⟨site, by
    have hnotBoundary : (site : L.Site) ∉ M.boundary region := site.property.1
    rcases Finset.mem_union.mp site.property.2 with hregion | hexternal
    · refine Finset.mem_sdiff.mpr ⟨hregion, ?_⟩
      intro hinternal
      have hboundary : (site : L.Site) ∈ M.boundary region :=
        Eq.mp
          (congrArg (fun s : Finset L.Site => (site : L.Site) ∈ s)
            (M.boundary_eq_internal_union_external region)).symm
          (Finset.mem_union_left _ hinternal)
      exact hnotBoundary hboundary
    · have hboundary : (site : L.Site) ∈ M.boundary region :=
        Eq.mp
          (congrArg (fun s : Finset L.Site => (site : L.Site) ∈ s)
            (M.boundary_eq_internal_union_external region)).symm
          (Finset.mem_union_right _ hexternal)
      exact False.elim (hnotBoundary hboundary)⟩
  invFun := fun site => ⟨site, by
    constructor
    · have hinterior' : (site : L.Site) ∈ region \ M.boundary region := by
        rw [← M.interior_eq_region_sdiff_boundary region]
        exact site.property
      exact (Finset.mem_sdiff.mp hinterior').2
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp site.property).1⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl
noncomputable def boundarySelectedToBCTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region)) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    have hinternal : site ∈ M.internalBoundary region := hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hinternal
  let splitB := B.selectedFactorization BC hBBC
  let relabelC := quditCoordinateRelabel
    (q := B.additionalRetainedDimensions BC)
    (r := (M.regionSubsystem region).additionalRetainedDimensions
      (M.regionSubsystem (region ∪ M.externalBoundary region)))
    (M.boundaryAdditionalCoordinateEquiv region) (by
    intro site
    rfl)
  exact composeUnitaryTransport
    (composeUnitaryTransport splitB
      (unitaryRTensor (M.fourFactorBCoordinateRelabel region)
        (B.additionalRetainedSystem BC)))
    (unitaryLTensor (M.fourFactorB region) relabelC)
noncomputable def boundaryComplementToADTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).complementSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorD region)) := by
  let BC := M.regionSubsystem (M.boundary region)
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hBCABC : BC.selected ⊆ ABC.selected := by
    intro site hsite
    have hboundary : site ∈ M.boundary region := hsite
    change site ∈ region ∪ M.externalBoundary region
    rw [M.boundary_eq_internal_union_external region] at hboundary
    rcases Finset.mem_union.mp hboundary with hinternal | hexternal
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
    · exact Finset.mem_union_right _ hexternal
  let splitAD := BC.complementFactorization ABC hBCABC
  let relabelA := quditCoordinateRelabel
    (q := BC.additionalRetainedDimensions ABC)
    (r := (M.regionSubsystem (M.interior region)).selectedDimensions)
    (M.boundaryComplementAdditionalCoordinateEquiv region) (by
      intro site
      rfl)
  exact composeUnitaryTransport splitAD
    (unitaryRTensor relabelA ABC.complementSystem)
noncomputable def boundaryComplementToADBasisVector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).complementDimensions) :
    Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorD region) :=
  (quditCoordinateRelabel
      (q := (M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
        (M.regionSubsystem (region ∪ M.externalBoundary region)))
      (r := (M.regionSubsystem (M.interior region)).selectedDimensions)
      (M.boundaryComplementAdditionalCoordinateEquiv region) (by
        intro site
        rfl))
    (EuclideanSpace.basisFun
      (Semantics.Qudit.Label
        ((M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
          (M.regionSubsystem (region ∪ M.externalBoundary region))))
      Complex
      ((M.regionSubsystem (M.boundary region)).splitComplementLabel
        (M.regionSubsystem (region ∪ M.externalBoundary region))
        (by
          intro site hsite
          change site ∈ region ∪ M.externalBoundary region
          rw [M.boundary_eq_internal_union_external region] at hsite
          rcases Finset.mem_union.mp hsite with hinternal | hexternal
          · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
          · exact Finset.mem_union_right _ hexternal)
        labels).1) ⊗ₜ[Complex]
  EuclideanSpace.basisFun
    (Semantics.Qudit.Label
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
    ((M.regionSubsystem (M.boundary region)).splitComplementLabel
      (M.regionSubsystem (region ∪ M.externalBoundary region))
      (by
        intro site hsite
        change site ∈ region ∪ M.externalBoundary region
        rw [M.boundary_eq_internal_union_external region] at hsite
        rcases Finset.mem_union.mp hsite with hinternal | hexternal
        · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
        · exact Finset.mem_union_right _ hexternal)
      labels).2
noncomputable def boundaryToMiddleReorder
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D] :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem B C)
        (Semantics.CompositeSystem A D))
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem B C) D)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (tensorAssociatorUnitary (Semantics.CompositeSystem B C) A D).symm
    (unitaryRTensor (tensorSwapUnitary (Semantics.CompositeSystem B C) A) D))
    (tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D)
@[simp]
theorem boundaryToMiddleReorder_toLinearEquiv_apply_tmul
    (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (a : A) (b : B) (c : C) (d : D) :
    (boundaryToMiddleReorder A B C D).toLinearEquiv
        ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] (a ⊗ₜ[Complex] d)) =
      a ⊗ₜ[Complex] ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] d) := by
  simp only [boundaryToMiddleReorder, composeUnitaryTransport_toLinearEquiv_apply,
    tensorAssociatorUnitary_symm_toLinearEquiv_apply_tmul,
    unitaryRTensor_toLinearEquiv_apply_tmul,
    tensorSwapUnitary_toLinearEquiv_apply_tmul,
    tensorAssociatorUnitary_toLinearEquiv_apply_tmul]
noncomputable def boundaryGlobalToMiddleTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem (M.fourFactorA region)
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
          (M.fourFactorD region))) := by
  let BC := M.regionSubsystem (M.boundary region)
  let splitSelected := M.boundarySelectedToBCTransport region
  let splitComplement := M.boundaryComplementToADTransport region
  exact composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport BC.registerFactorization
        (unitaryRTensor splitSelected BC.complementSystem))
      (unitaryLTensor (Semantics.CompositeSystem (M.fourFactorB region)
        (M.fourFactorC region)) splitComplement))
    (boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
      (M.fourFactorC region) (M.fourFactorD region))
noncomputable def boundaryGlobalToFourFactorTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register (M.fourFactorSystem region) :=
  composeUnitaryTransport (M.boundaryGlobalToMiddleTransport region)
    (M.fourFactorMiddleReassociate region).symm
noncomputable def boundaryLocalUnitaryToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    Semantics.UnitaryTransport L.Register L.Register :=
  extendLocalUnitaryToRegister L.localDimension
    (M.regionSubsystem (M.boundary region)) U
noncomputable def activeSectorBoundaryUnitary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem :=
  conjugateUnitaryTransport (M.boundarySelectedToBCTransport region)
    (activeSectorPhysicalUnitary SB SC UB UC U)
noncomputable def activeSectorBoundaryGlobalUnitary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    Semantics.UnitaryTransport L.Register L.Register :=
  M.boundaryLocalUnitaryToRegister region
    (M.activeSectorBoundaryUnitary region SB SC UB UC U)
theorem support_subset_region_of_mem_interior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) (check : kappa)
    {site : L.Site} (hsupport : site ∈ M.support check) (hinterior : site ∈ M.interior region) :
    M.support check ⊆ region := by
  intro other hother
  by_contra hnotregion
  have hcouples : M.supportCouples check region := by
    constructor
    · exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, (Finset.mem_sdiff.mp hinterior).1⟩⟩
    · exact ⟨other, Finset.mem_sdiff.mpr ⟨hother, hnotregion⟩⟩
  have hboundary : site ∈ M.boundary region :=
    M.support_subset_boundary_of_couples region check hcouples hsupport
  have hinterior' : site ∈ region \ M.boundary region := by
    rw [← M.interior_eq_region_sdiff_boundary region]
    exact hinterior
  exact (Finset.mem_sdiff.mp hinterior').2 hboundary
theorem support_subset_complement_of_mem_exterior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) (check : kappa)
    {site : L.Site} (hsupport : site ∈ M.support check) (hexterior : site ∈ M.exterior region) :
    M.support check ⊆ regionᶜ := by
  intro other hother
  apply Finset.mem_compl.mpr
  by_contra hregion
  have hcouples : M.supportCouples check region := by
    constructor
    · exact ⟨other, Finset.mem_inter.mpr ⟨hother, hregion⟩⟩
    · exact ⟨site, Finset.mem_sdiff.mpr ⟨hsupport,
        Finset.mem_compl.mp (Finset.mem_sdiff.mp hexterior).1⟩⟩
  have hexternal : site ∈ M.externalBoundary region :=
    (M.mem_externalBoundary_iff region site).mpr
      ⟨Finset.mem_compl.mp (Finset.mem_sdiff.mp hexterior).1, check, hcouples, hsupport⟩
  exact (Finset.mem_sdiff.mp hexterior).2 hexternal
theorem support_subset_boundary_of_not_mem_interior_not_mem_exterior
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) (check : kappa)
    (hinterior : ∀ site, site ∈ M.support check → site ∉ M.interior region)
    (hexterior : ∀ site, site ∈ M.support check → site ∉ M.exterior region) :
    M.support check ⊆ M.boundary region := by
  intro site hsupport
  by_cases hregion : site ∈ region
  · have hsplit : site ∈ M.interior region ∪ M.internalBoundary region := by
      rw [← M.region_eq_interior_union_internalBoundary region]
      exact hregion
    rcases Finset.mem_union.mp hsplit with hinside | hboundary
    · exact False.elim (hinterior site hsupport hinside)
    · exact (Finset.mem_inter.mp hboundary).1
  · have hcomplement : site ∈ regionᶜ := Finset.mem_compl.mpr hregion
    have hsplit : site ∈ M.externalBoundary region ∪ M.exterior region := by
      rw [← M.complement_eq_externalBoundary_union_exterior region]
      exact hcomplement
    rcases Finset.mem_union.mp hsplit with hboundary | houtside
    · exact (Finset.mem_sdiff.mp hboundary).1
    · exact False.elim (hexterior site hsupport houtside)
noncomputable def interiorChecks (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset kappa :=
  Finset.univ.filter fun check => (M.support check ∩ M.interior region).Nonempty
noncomputable def exteriorChecks (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset kappa :=
  Finset.univ.filter fun check => (M.support check ∩ M.exterior region).Nonempty
noncomputable def boundaryChecks (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Finset kappa :=
  Finset.univ \ (M.interiorChecks region ∪ M.exteriorChecks region)
theorem support_subset_region_of_mem_interiorChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {check : kappa} (hcheck : check ∈ M.interiorChecks region) :
    M.support check ⊆ region := by
  rcases (Finset.mem_filter.mp hcheck).2 with ⟨site, hsite⟩
  exact M.support_subset_region_of_mem_interior region check
    (Finset.mem_inter.mp hsite).1 (Finset.mem_inter.mp hsite).2
theorem support_subset_complement_of_mem_exteriorChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {check : kappa} (hcheck : check ∈ M.exteriorChecks region) :
    M.support check ⊆ regionᶜ := by
  rcases (Finset.mem_filter.mp hcheck).2 with ⟨site, hsite⟩
  exact M.support_subset_complement_of_mem_exterior region check
    (Finset.mem_inter.mp hsite).1 (Finset.mem_inter.mp hsite).2
theorem support_subset_boundary_of_mem_boundaryChecks
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {check : kappa} (hcheck : check ∈ M.boundaryChecks region) :
    M.support check ⊆ M.boundary region := by
  have hnotInterior : check ∉ M.interiorChecks region :=
    fun hmem => (Finset.mem_sdiff.mp hcheck).2 (Finset.mem_union_left _ hmem)
  have hnotExterior : check ∉ M.exteriorChecks region :=
    fun hmem => (Finset.mem_sdiff.mp hcheck).2 (Finset.mem_union_right _ hmem)
  apply M.support_subset_boundary_of_not_mem_interior_not_mem_exterior region check
  · intro site hsupport hinterior
    apply hnotInterior
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨site,
      Finset.mem_inter.mpr ⟨hsupport, hinterior⟩⟩⟩
  · intro site hsupport hexterior
    apply hnotExterior
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨site,
      Finset.mem_inter.mpr ⟨hsupport, hexterior⟩⟩⟩
theorem projectorPairwiseCommute (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    (checks : Set kappa).Pairwise (Function.onFun Commute M.projector) := by
  intro check _ other _ _
  exact M.projector_commute check other
noncomputable def projectorProductOn (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) : Semantics.Operator L.Register :=
  checks.noncommProd M.projector (M.projectorPairwiseCommute checks)
theorem operatorSupportedOnRegister_comp
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {A B : Semantics.Operator L.Register}
    (hA : (M.regionSubsystem region).OperatorSupportedOnRegister A)
    (hB : (M.regionSubsystem region).OperatorSupportedOnRegister B) :
    (M.regionSubsystem region).OperatorSupportedOnRegister (A.comp B) := by
  rcases hA with ⟨localA, hlocalA⟩
  rcases hB with ⟨localB, hlocalB⟩
  refine ⟨localA.comp localB, ?_⟩
  rw [← localExtension_comp, hlocalA, hlocalB]
theorem projectorProductOn_supportedOnRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (checks : Finset kappa)
    (hsupported : ∀ check, check ∈ checks →
      (M.regionSubsystem region).OperatorSupportedOnRegister (M.projector check)) :
    (M.regionSubsystem region).OperatorSupportedOnRegister
      (M.projectorProductOn checks) := by
  classical
  induction checks using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      change (M.regionSubsystem region).registerFactorization.symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
          (1 : Semantics.Operator (M.regionSubsystem region).complementSystem)) = 1
      rw [TensorProduct.map_one]
      exact (M.regionSubsystem region).registerFactorization.symm.conjOperator_one
  | insert check checks hnotmem induction =>
      have hrest : (checks : Set kappa).Pairwise (Function.onFun Commute M.projector) :=
        (M.projectorPairwiseCommute (insert check checks)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := checks.noncommProd M.projector hrest
      have hfactor : (insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks)) =
          M.projector check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem checks check M.projector
          (M.projectorPairwiseCommute (insert check checks)) hnotmem]
      have hcheck :
          (M.regionSubsystem region).OperatorSupportedOnRegister (M.projector check) :=
        hsupported check (Finset.mem_insert_self check checks)
      have hproductRest :
          (M.regionSubsystem region).OperatorSupportedOnRegister productRest := by
        dsimp [productRest]
        simpa [projectorProductOn] using induction
          (fun other hother => hsupported other (Finset.mem_insert_of_mem hother))
      change (M.regionSubsystem region).OperatorSupportedOnRegister
        ((insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks)))
      rw [hfactor]
      exact M.operatorSupportedOnRegister_comp region hcheck hproductRest
noncomputable def projectorAB (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Semantics.Operator L.Register :=
  M.projectorProductOn (M.interiorChecks region)
noncomputable def projectorBC (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Semantics.Operator L.Register :=
  M.projectorProductOn (M.boundaryChecks region)
noncomputable def projectorCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Semantics.Operator L.Register :=
  M.projectorProductOn (M.exteriorChecks region)
theorem projectorAB_supportedOnRegister_region
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem region).OperatorSupportedOnRegister (M.projectorAB region) := by
  apply M.projectorProductOn_supportedOnRegister region (M.interiorChecks region)
  intro check hcheck
  exact M.projector_supportedOnRegister_of_support_subset check region
    (M.support_subset_region_of_mem_interiorChecks region hcheck)
theorem projectorBC_supportedOnRegister_boundary
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region)).OperatorSupportedOnRegister (M.projectorBC region) := by
  apply M.projectorProductOn_supportedOnRegister (M.boundary region) (M.boundaryChecks region)
  intro check hcheck
  exact M.projector_supportedOnRegister_of_support_subset check (M.boundary region)
    (M.support_subset_boundary_of_mem_boundaryChecks region hcheck)
theorem projectorCD_supportedOnRegister_complement
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).OperatorSupportedOnRegister (M.projectorCD region) := by
  apply M.projectorProductOn_supportedOnRegister regionᶜ (M.exteriorChecks region)
  intro check hcheck
  exact M.projector_supportedOnRegister_of_support_subset check regionᶜ
    (M.support_subset_complement_of_mem_exteriorChecks region hcheck)
noncomputable def projectorABLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (M.regionSubsystem region).selectedSystem :=
  Classical.choose (M.projectorAB_supportedOnRegister_region region)
noncomputable def projectorBCLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (M.regionSubsystem (M.boundary region)).selectedSystem :=
  Classical.choose (M.projectorBC_supportedOnRegister_boundary region)
noncomputable def projectorCDLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (M.regionSubsystem regionᶜ).selectedSystem :=
  Classical.choose (M.projectorCD_supportedOnRegister_complement region)
noncomputable def fourFactorProjectorCDLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem
      ((M.regionSubsystem region).additionalRetainedSystem
        (M.regionSubsystem (region ∪ M.externalBoundary region)))
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem) :=
  (M.fourFactorCDCoordinateTransport region).conjOperator (M.projectorCDLocal region)
noncomputable def fourFactorProjectorBCLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem
      (M.fourFactorB region) (M.fourFactorC region)) :=
  (M.boundarySelectedToBCTransport region).conjOperator (M.projectorBCLocal region)
noncomputable def fourFactorProjectorABLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem
      (M.fourFactorA region) (M.fourFactorB region)) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  exact (A.selectedFactorization AB hAAB).conjOperator (M.projectorABLocal region)
noncomputable def firstCutProjectorMC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (M.fourFactorC region)) :=
  TensorProduct.map (M.fourFactorProjectorABLocal region)
      (1 : Semantics.Operator (M.fourFactorC region)) *
    overlapLiftRight (A := M.fourFactorA region) (M.fourFactorProjectorBCLocal region)
noncomputable def firstCutCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region))
      (M.fourFactorSystem region) :=
  composeUnitaryTransport
    (tensorAssociatorUnitary
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (M.fourFactorC region) (M.fourFactorD region))
    (tensorAssociatorUnitary (M.fourFactorA region) (M.fourFactorB region)
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
def externalAdditionalToRegionCoordinateEquiv (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.regionSubsystem (M.externalBoundary region)).AdditionalRetainedCoordinates
        (M.regionSubsystem (region ∪ M.externalBoundary region)) ≃
      (M.regionSubsystem region).SelectedCoordinates where
  toFun := fun site => ⟨site, by
    rcases Finset.mem_union.mp site.property.2 with hregion | hexternal
    · exact hregion
    · exact False.elim (site.property.1 hexternal)⟩
  invFun := fun site => ⟨site, by
    constructor
    · intro hexternal
      exact (Finset.disjoint_left.mp (M.externalBoundary_disjoint_region region))
        hexternal site.property
    · exact Finset.mem_union_left _ site.property⟩
  left_inv := by
    intro site
    exact Subtype.ext rfl
  right_inv := by
    intro site
    exact Subtype.ext rfl
noncomputable def externalAdditionalToRegionCoordinateRelabel
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      ((M.regionSubsystem (M.externalBoundary region)).additionalRetainedSystem
        (M.regionSubsystem (region ∪ M.externalBoundary region)))
      (M.regionSubsystem region).selectedSystem :=
  quditCoordinateRelabel
    (q := (M.regionSubsystem (M.externalBoundary region)).additionalRetainedDimensions
      (M.regionSubsystem (region ∪ M.externalBoundary region)))
    (r := (M.regionSubsystem region).selectedDimensions)
    (M.externalAdditionalToRegionCoordinateEquiv region) (by
      intro site
      rfl)
noncomputable def externalSelectedFactorizationReorder
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (M.regionSubsystem (M.externalBoundary region)).selectedSystem
        ((M.regionSubsystem (M.externalBoundary region)).additionalRetainedSystem
          (M.regionSubsystem (region ∪ M.externalBoundary region))))
      (Semantics.CompositeSystem
        (M.regionSubsystem region).selectedSystem
        (M.fourFactorC region)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (unitaryRTensor (M.fourFactorCCoordinateRelabel region)
        ((M.regionSubsystem (M.externalBoundary region)).additionalRetainedSystem
          (M.regionSubsystem (region ∪ M.externalBoundary region))))
      (unitaryLTensor (M.fourFactorC region)
        (M.externalAdditionalToRegionCoordinateRelabel region)))
    (tensorSwapUnitary (M.fourFactorC region)
      (M.regionSubsystem region).selectedSystem)
noncomputable def fourFactorTransportFromNestedRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register (M.fourFactorSystem region) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  exact composeUnitaryTransport
    (composeUnitaryTransport (nestedFactorizationRight AB ABC hABABC)
      (unitaryRTensor splitAB
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))
noncomputable def firstCutCodeLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region)) :=
  overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region) *
    overlapLiftRight
      (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (M.fourFactorProjectorCDLocal region)
noncomputable def firstCutSectorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region)) :=
  overlapLiftLeft (C := M.fourFactorD region)
    (TensorProduct.map
      (1 : Semantics.Operator
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)))
      (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component))
noncomputable def firstCutGlobalCoordinateTransport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Semantics.UnitaryTransport L.Register
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorC region))
        (M.fourFactorD region)) :=
  composeUnitaryTransport (M.fourFactorTransport region)
    (M.firstCutCoordinateTransport region).symm
noncomputable def firstCutDoubleInteractionCoefficient
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) :
    Semantics.Operator (M.fourFactorC region) :=
  leftInteractionCoefficient
    (rightInteractionCoefficient (M.firstCutCodeLift region) d d') a a'
end BPTCommutingProjectorModel
end Bounds
end QEC


