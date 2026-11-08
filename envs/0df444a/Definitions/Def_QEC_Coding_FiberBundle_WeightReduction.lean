-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
-- name    : QEC_Coding_FiberBundle_WeightReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:01:57.427193+00:00
-- url     : https://prove2.me/theorems/60fdefb6-2004-47a0-bf05-f78c03f0678c
-- title:
--   Weight Reduction
-- statement:
--   Definitions and structural lemmas for Weight Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_baseSample_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_isTail_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_typeTwist_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_conj_stdAddChar_neg
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_heavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_lightLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_mediumLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_nonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_twoSidedLightTypeSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
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
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.baseSample_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.isTail_twistSample
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.typeTwist_twistSample
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.conj_stdAddChar_neg
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_lightLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_mediumLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_nonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_twoSidedLightTypeSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inl
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inr
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
namespace QEC.Coding.FiberBundle
universe u
def FiberAutomorphism.id
    {fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    (fiberBoundary : Matrix fiberZero fiberOne (ZMod 2)) :
    FiberAutomorphism fiberZero fiberOne fiberBoundary where
  onZero := Equiv.refl fiberZero
  onOne := Equiv.refl fiberOne
  boundary_naturality := by simp
def baseSupportRelation
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (a : baseZero) (b : baseOne) : Prop :=
  D.baseBoundary a b ≠ 0
instance
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    DecidableRel (baseSupportRelation D) :=
  fun a b => inferInstanceAs (Decidable (D.baseBoundary a b ≠ 0))
def weightReducedConnection
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    ClassicalWeightReduction.WeightReducedBit (baseSupportRelation D) →
      ClassicalWeightReduction.WeightReducedCheck (baseSupportRelation D) →
      FiberAutomorphism fiberZero fiberOne D.fiberBoundary
  | Sum.inl bitIncidence, Sum.inl checkIncidence =>
      if bitIncidence = checkIncidence then
        D.connection bitIncidence.1.2 bitIncidence.1.1
      else
        FiberAutomorphism.id D.fiberBoundary
  | _, _ => FiberAutomorphism.id D.fiberBoundary
noncomputable def weightReducedData
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Data
      (ClassicalWeightReduction.WeightReducedCheck (baseSupportRelation D))
      (ClassicalWeightReduction.WeightReducedBit (baseSupportRelation D))
      fiberZero fiberOne where
  baseBoundary := fun a b =>
    ClassicalWeightReduction.basisBoundary
      (F := ZMod 2) (baseSupportRelation D) b a
  fiberBoundary := D.fiberBoundary
  connection := weightReducedConnection D
@[simp]
theorem weightReducedData_fiberBoundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (weightReducedData D).fiberBoundary = D.fiberBoundary := by
  rfl
@[simp]
theorem weightReducedConnection_primary_self
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (e : ClassicalWeightReduction.Incidence (baseSupportRelation D)) :
    weightReducedConnection D (Sum.inl e) (Sum.inl e) =
      D.connection e.1.2 e.1.1 := by
  simp [weightReducedConnection]
@[simp]
theorem weightReducedConnection_primary_ne
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (e e' : ClassicalWeightReduction.Incidence (baseSupportRelation D))
    (h : e ≠ e') :
    weightReducedConnection D (Sum.inl e) (Sum.inl e') =
      FiberAutomorphism.id D.fiberBoundary := by
  simp [weightReducedConnection, h]
section TwistedForward
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
noncomputable def reducedQubitBasisWord
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne) := by
  classical
  exact Pi.single q 1
noncomputable def reducedC0BasisWord
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero) :
    Word (ZMod 2)
      (C0Index (ClassicalWeightReduction.WeightReducedCheck R) fiberZero) := by
  classical
  exact Pi.single (q, i) 1
noncomputable def reducedC2BasisWord
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne) :
    Word (ZMod 2)
      (C2Index (ClassicalWeightReduction.WeightReducedBit R) fiberOne) := by
  classical
  exact Pi.single (q, j) 1
@[simp]
theorem boundary1_single (q : QubitIndex baseZero baseOne fiberZero fiberOne) :
    boundary1 D (Pi.single q 1) = fun p => boundary1Matrix D p q := by
  rw [boundary1, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl
omit [DecidableEq baseZero] [DecidableEq fiberZero] in
@[simp]
theorem boundary2_single (q : C2Index baseOne fiberOne) :
    boundary2 D (Pi.single q 1) = fun p => boundary2Matrix D p q := by
  rw [boundary2, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl
theorem boundary1_single_inl (b : baseOne) (j : fiberZero) :
    boundary1 D (Pi.single (Sum.inl (b, j)) 1) =
      fun ai =>
        if ai.2 = (D.connection b ai.1).onZero j then
          D.baseBoundary ai.1 b
        else 0 := by
  rw [boundary1_single]
  rfl
theorem boundary1_single_inr (a : baseZero) (j : fiberOne) :
    boundary1 D (Pi.single (Sum.inr (a, j)) 1) =
      fun ai => if ai.1 = a then D.fiberBoundary ai.2 j else 0 := by
  rw [boundary1_single]
  rfl
omit [DecidableEq baseZero] [DecidableEq fiberZero] in
theorem boundary2_single_apply_inl
    (b : baseOne) (j : fiberOne) (b' : baseOne) (i : fiberZero) :
    boundary2 D (Pi.single (b, j) 1) (Sum.inl (b', i)) =
      if b' = b then D.fiberBoundary i j else 0 := by
  rw [boundary2_single]
  rfl
omit [DecidableEq baseZero] [DecidableEq fiberZero] in
theorem boundary2_single_apply_inr
    (b : baseOne) (j : fiberOne) (a : baseZero) (j' : fiberOne) :
    boundary2 D (Pi.single (b, j) 1) (Sum.inr (a, j')) =
      if j' = (D.connection b a).onOne j then
        D.baseBoundary a b
      else 0 := by
  rw [boundary2_single]
  rfl
noncomputable def weightReductionForwardBaseZeroBasis
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  match q with
  | Sum.inl e => Pi.single (e.1.1, i) 1
  | Sum.inr a =>
      ∑ e : ClassicalWeightReduction.Incidence R,
        (ClassicalWeightReduction.combineForwardMap0Basis
            (F := ZMod 2) R (Sum.inr a) e) •
          Pi.single
            (e.1.1, (D.connection e.1.2 e.1.1).onZero i) 1
noncomputable def weightReductionForwardBaseZeroOneBasis
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    Word (ZMod 2) (baseZero × fiberOne) :=
  match q with
  | Sum.inl e => Pi.single (e.1.1, j) 1
  | Sum.inr a =>
      ∑ e : ClassicalWeightReduction.Incidence R,
        (ClassicalWeightReduction.combineForwardMap0Basis
            (F := ZMod 2) R (Sum.inr a) e) •
          Pi.single
            (e.1.1, (D.connection e.1.2 e.1.1).onOne j) 1
noncomputable def weightReductionForwardBaseOneBasis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    Word (ZMod 2) (baseOne × fiberZero) :=
  match q with
  | Sum.inl e =>
      if ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2 then
        Pi.single (e.1.2, i) 1
      else 0
  | Sum.inr _ => 0
noncomputable def weightReductionForwardBaseOneOneBasis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne) :
    Word (ZMod 2) (baseOne × fiberOne) :=
  match q with
  | Sum.inl e =>
      if ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2 then
        Pi.single (e.1.2, j) 1
      else 0
  | Sum.inr _ => 0
noncomputable def weightReductionForwardMap0
    : Word (ZMod 2)
        (C0Index
          (ClassicalWeightReduction.WeightReducedCheck R) fiberZero) →ₗ[ZMod 2]
      Word (ZMod 2) (C0Index baseZero fiberZero) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (F := ZMod 2) (fun qi =>
        weightReductionForwardBaseZeroBasis D qi.1 qi.2)
noncomputable def weightReductionForwardMap1
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (F := ZMod 2) (fun q target =>
        match q, target with
        | Sum.inl bi, Sum.inl target' =>
            weightReductionForwardBaseOneBasis D h bi.1 bi.2 target'
        | Sum.inr aj, Sum.inr target' =>
            weightReductionForwardBaseZeroOneBasis D aj.1 aj.2 target'
        | _, _ => 0)
noncomputable def weightReductionForwardMap2
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    Word (ZMod 2)
        (C2Index (ClassicalWeightReduction.WeightReducedBit R) fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2) (C2Index baseOne fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (F := ZMod 2) (fun qj =>
        weightReductionForwardBaseOneOneBasis D h qj.1 qj.2)
omit [DecidableEq fiberOne] in
theorem weightReductionForwardMap0_reducedC0BasisWord
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero) :
    weightReductionForwardMap0 D (reducedC0BasisWord D q i) =
      weightReductionForwardBaseZeroBasis D q i := by
  classical
  unfold reducedC0BasisWord weightReductionForwardMap0
  rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
theorem weightReductionForwardMap1_reducedQubitBasisWord_inl
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    weightReductionForwardMap1 D h
        (reducedQubitBasisWord D
          (Sum.inl (q, i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne)) =
      fun target : QubitIndex baseZero baseOne fiberZero fiberOne =>
        match target with
        | Sum.inl target' =>
            weightReductionForwardBaseOneBasis D h q i target'
        | Sum.inr _ => 0 := by
  classical
  unfold reducedQubitBasisWord weightReductionForwardMap1
  rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
  ext target
  cases target <;> rfl
theorem weightReductionForwardMap1_reducedQubitBasisWord_inr
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    weightReductionForwardMap1 D h
        (reducedQubitBasisWord D
          (Sum.inr (q, j) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne)) =
      fun target : QubitIndex baseZero baseOne fiberZero fiberOne =>
        match target with
        | Sum.inl _ => 0
        | Sum.inr target' =>
            weightReductionForwardBaseZeroOneBasis D q j target' := by
  classical
  unfold reducedQubitBasisWord weightReductionForwardMap1
  rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
  ext target
  cases target <;> rfl
omit [DecidableEq fiberZero] in
theorem weightReductionForwardMap2_reducedC2BasisWord
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne) :
    weightReductionForwardMap2 D h (reducedC2BasisWord D q j) =
      weightReductionForwardBaseOneOneBasis D h q j := by
  classical
  unfold reducedC2BasisWord weightReductionForwardMap2
  rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
omit [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [DecidableEq fiberOne] in
theorem sum_fiberBoundary_transport_single
    (P : FiberAutomorphism fiberZero fiberOne D.fiberBoundary)
    (coefficient : ZMod 2) (k : fiberZero) (j : fiberOne) :
    (∑ i : fiberZero,
        D.fiberBoundary i j *
          if k = P.onZero i then coefficient else 0) =
      D.fiberBoundary k (P.onOne j) * coefficient := by
  calc
    _ = ∑ y : fiberZero,
        D.fiberBoundary (P.onZero.symm y) j *
          if k = y then coefficient else 0 := by
      apply Fintype.sum_equiv P.onZero
      intro i
      simp
    _ = D.fiberBoundary (P.onZero.symm k) j * coefficient := by
      simp
    _ = D.fiberBoundary k (P.onOne j) * coefficient := by
      rw [← P.boundary_naturality (P.onZero.symm k) j]
      simp
omit [Fintype baseZero] [Fintype baseOne]
    [DecidableEq baseOne] [DecidableEq fiberOne] in
theorem sum_fiberBoundary_transport_single_at_base
    (P : FiberAutomorphism fiberZero fiberOne D.fiberBoundary)
    (coefficient : ZMod 2) (a c : baseZero)
    (k : fiberZero) (j : fiberOne) :
    (∑ i : fiberZero,
        D.fiberBoundary i j *
          if (a, k) = (c, P.onZero i) then coefficient else 0) =
      if a = c then
        D.fiberBoundary k (P.onOne j) * coefficient
      else 0 := by
  by_cases hac : a = c
  · subst c
    simpa [Prod.ext_iff] using
      sum_fiberBoundary_transport_single D P coefficient k j
  · simp [hac]
theorem ite_fintype_sum_zero
    {I : Type*} [Fintype I] (p : Prop) [Decidable p]
    (f : I → ZMod 2) :
    (if p then ∑ i, f i else 0) = ∑ i, if p then f i else 0 := by
  by_cases hp : p <;> simp [hp]
theorem ite_add_zero (p : Prop) [Decidable p] (x y : ZMod 2) :
    (if p then x + y else 0) =
      (if p then x else 0) + (if p then y else 0) := by
  by_cases hp : p <;> simp [hp]
omit [DecidableEq fiberZero] [DecidableEq fiberOne] in
theorem sum_target_times_incidence_single
    {I : Type*} [DecidableEq I]
    (target : baseZero × I)
    (location : ClassicalWeightReduction.Incidence R →
      baseZero × I)
    (e : ClassicalWeightReduction.Incidence R) :
    (∑ x : ClassicalWeightReduction.Incidence R,
        if target = location x then
          (if x = e then (1 : ZMod 2) else 0)
        else 0) =
      if target = location e then 1 else 0 := by
  rw [Fintype.sum_eq_single e]
  · simp
  · intro x hxe
    simp [hxe]
omit [Fintype baseOne] [DecidableEq fiberZero] [DecidableEq fiberOne] in
@[simp]
theorem optionalAuxiliaryCheckSingle_apply_primary
    (b : baseOne)
    (o : Option
      (Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1)))
    (e : ClassicalWeightReduction.Incidence R) :
    ClassicalWeightReduction.optionalSingle (F := ZMod 2)
        (o.map (ClassicalWeightReduction.auxiliaryCheckIndex R b))
        (Sum.inl e) = 0 := by
  cases o <;> simp [ClassicalWeightReduction.optionalSingle,
    ClassicalWeightReduction.auxiliaryCheckIndex]
noncomputable def incidenceTransportZero (i : fiberZero) :
    Word (ZMod 2) (ClassicalWeightReduction.Incidence R) →ₗ[ZMod 2]
      Word (ZMod 2) (baseZero × fiberZero) :=
  ClassicalWeightReduction.linearMapOfBasisImages
    (fun e => Pi.single
      (e.1.1, (D.connection e.1.2 e.1.1).onZero i) 1)
omit [DecidableEq fiberOne] in
@[simp]
theorem incidenceTransportZero_apply (i : fiberZero)
    (w : Word (ZMod 2) (ClassicalWeightReduction.Incidence R))
    (ai : baseZero × fiberZero) :
    incidenceTransportZero D i w ai =
      ∑ e : ClassicalWeightReduction.Incidence R,
        if ai = (e.1.1, (D.connection e.1.2 e.1.1).onZero i) then
          w e
        else 0 := by
  classical
  unfold incidenceTransportZero
    ClassicalWeightReduction.linearMapOfBasisImages
  simp [Pi.single_apply]
omit [DecidableEq fiberZero] [DecidableEq fiberOne] in
theorem combineForwardMap0_primaryBitBoundary_apply
    (e x : ClassicalWeightReduction.Incidence R) :
    ClassicalWeightReduction.combineForwardMap0 (F := ZMod 2) R
        (ClassicalWeightReduction.primaryBitBoundary (F := ZMod 2) R e) x =
      (if x = e then 1 else 0) +
        ∑ a : ClassicalWeightReduction.AuxiliaryCheck R,
          (ClassicalWeightReduction.optionalSingle
                (F := ZMod 2)
                ((ClassicalWeightReduction.pathPrevious
                    (ClassicalWeightReduction.bitPosition R e)).map
                  (ClassicalWeightReduction.auxiliaryCheckIndex R e.1.2))
                (Sum.inr a) +
            ClassicalWeightReduction.optionalSingle
                (F := ZMod 2)
                ((ClassicalWeightReduction.pathNext
                    (ClassicalWeightReduction.bitPosition R e)).map
                  (ClassicalWeightReduction.auxiliaryCheckIndex R e.1.2))
                (Sum.inr a)) *
            ClassicalWeightReduction.combineForwardMap0Basis
              (F := ZMod 2) R (Sum.inr a) x := by
  classical
  unfold ClassicalWeightReduction.combineForwardMap0
    ClassicalWeightReduction.linearMapOfBasisImages
    ClassicalWeightReduction.primaryBitBoundary
  simp_rw [Fintype.sum_sum_type]
  simp [ClassicalWeightReduction.combineForwardMap0Basis,
    Pi.single_apply]
theorem weightReductionForward_primaryBoundary_eq_transport
    (e : ClassicalWeightReduction.Incidence R) (i : fiberZero) :
    weightReductionForwardMap0 D
        (boundary1 (weightReducedData D)
          (reducedQubitBasisWord D
            (Sum.inl (Sum.inl e, i) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))) =
      incidenceTransportZero D i
        (ClassicalWeightReduction.combineForwardMap0 (F := ZMod 2) R
          (ClassicalWeightReduction.primaryBitBoundary
            (F := ZMod 2) R e)) := by
  classical
  let w := ClassicalWeightReduction.combineForwardMap0 (F := ZMod 2) R
    (ClassicalWeightReduction.primaryBitBoundary (F := ZMod 2) R e)
  change weightReductionForwardMap0 D
      (boundary1 (weightReducedData D)
        (reducedQubitBasisWord D
          (Sum.inl (Sum.inl e, i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne))) =
    incidenceTransportZero D i w
  ext ai
  rw [incidenceTransportZero_apply]
  unfold reducedQubitBasisWord weightReductionForwardMap0
    ClassicalWeightReduction.linearMapOfBasisImages
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sum_type]
  simp (config := { zeta := false })
    [boundary1, Matrix.toLin'_apply, weightReducedData, boundary1Matrix,
    weightReductionForwardBaseZeroBasis, Pi.single_apply,
    weightReducedConnection, FiberAutomorphism.id,
    ClassicalWeightReduction.basisBoundary,
    ClassicalWeightReduction.primaryBitBoundary,
    ClassicalWeightReduction.auxiliaryBitBoundary]
  rw [← sum_target_times_incidence_single D ai
    (fun x =>
      (x.1.1, (D.connection x.1.2 x.1.1).onZero i)) e]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hai :
      ai = (x.1.1, (D.connection x.1.2 x.1.1).onZero i)
  · simp [hai, w, combineForwardMap0_primaryBitBoundary_apply]
  · simp [hai]
theorem zmod_two_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  apply (ZMod.val_eq_one (n := 2) (by omega) x).mp
  have hpos : 0 < x.val := ZMod.val_pos.mpr hx
  have hlt : x.val < 2 := x.val_lt
  omega
theorem incidenceTransportZero_bitSplitPrimaryBoundary
    (b : baseOne) (i : fiberZero) :
    incidenceTransportZero D i
        (ClassicalWeightReduction.bitSplitPrimaryBoundary
          (F := ZMod 2) R b) =
      boundary1 D (Pi.single (Sum.inl (b, i)) 1) := by
  classical
  ext ai
  rw [incidenceTransportZero_apply, boundary1_single_inl]
  unfold ClassicalWeightReduction.bitSplitPrimaryBoundary
  change (∑ e : ClassicalWeightReduction.Incidence R,
      if ai = (e.1.1, (D.connection e.1.2 e.1.1).onZero i) then
        (if e.1.2 = b then 1 else 0)
      else 0) =
    if ai.2 = (D.connection b ai.1).onZero i then
      D.baseBoundary ai.1 b
    else 0
  by_cases hbase : D.baseBoundary ai.1 b = 0
  · rw [show (if ai.2 = (D.connection b ai.1).onZero i then
        D.baseBoundary ai.1 b else 0) = 0 by simp [hbase]]
    apply Finset.sum_eq_zero
    intro e _he
    by_cases hlocation :
        ai = (e.1.1, (D.connection e.1.2 e.1.1).onZero i)
    · have hcheck : e.1.1 = ai.1 := by
        exact (congrArg Prod.fst hlocation).symm
      by_cases hbit : e.1.2 = b
      · exfalso
        exact e.2 (by simpa [hcheck, hbit] using hbase)
      · simp [hlocation, hbit]
    · simp [hlocation]
  · let target : ClassicalWeightReduction.Incidence R :=
      ⟨(ai.1, b), hbase⟩
    have hone : D.baseBoundary ai.1 b = 1 :=
      zmod_two_eq_one_of_ne_zero _ hbase
    rw [Fintype.sum_eq_single target]
    · simp [target, hone, Prod.ext_iff]
    · intro e hne
      by_cases hlocation :
          ai = (e.1.1, (D.connection e.1.2 e.1.1).onZero i)
      · by_cases hbit : e.1.2 = b
        · have hcheck : e.1.1 = ai.1 := by
            exact (congrArg Prod.fst hlocation).symm
          have hetarget : e = target := by
            apply Subtype.ext
            exact Prod.ext hcheck hbit
          exact (hne hetarget).elim
        · simp [hlocation, hbit]
      · simp [hlocation]
omit [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne] in
@[simp]
theorem horizontalEmbedding_zero :
    (fun target : QubitIndex baseZero baseOne fiberZero fiberOne =>
      match target with
      | Sum.inl _ => (0 : ZMod 2)
      | Sum.inr _ => (0 : ZMod 2)) =
    (0 : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) := by
  ext target
  cases target <;> rfl
theorem weightReductionForward_commutes_boundary1_vertical
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    weightReductionForwardMap0 D
        (boundary1 (weightReducedData D)
          (reducedQubitBasisWord D
            (Sum.inr (q, j) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))) =
      boundary1 D
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D
            (Sum.inr (q, j) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))) := by
  classical
  rw [weightReductionForwardMap1_reducedQubitBasisWord_inr]
  cases q with
  | inl e =>
      unfold reducedQubitBasisWord weightReductionForwardMap0
        ClassicalWeightReduction.linearMapOfBasisImages
        weightReductionForwardBaseZeroOneBasis
      ext ai
      simp_rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_sum_type]
      simp [boundary1, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, weightReducedData, boundary1Matrix,
        weightReductionForwardBaseZeroBasis, Pi.single_apply]
      rcases ai with ⟨a, i⟩
      by_cases hae : a = e.1.1
      · subst a
        simp
      · simp [hae]
  | inr a =>
      unfold reducedQubitBasisWord weightReductionForwardMap0
        ClassicalWeightReduction.linearMapOfBasisImages
        weightReductionForwardBaseZeroOneBasis
      ext ai
      simp_rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_sum_type]
      simp [boundary1, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, weightReducedData, boundary1Matrix,
        weightReductionForwardBaseZeroBasis, Pi.single_apply]
      simp_rw [Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      simp_rw [ite_fintype_sum_zero]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      rw [sum_fiberBoundary_transport_single_at_base D
        (D.connection e.1.2 e.1.1)
        (ClassicalWeightReduction.combineForwardMap0Basis
          (F := ZMod 2) R (Sum.inr a) e)
        ai.1 e.1.1 ai.2 j]
      symm
      rw [Fintype.sum_eq_single
        (e.1.1, (D.connection e.1.2 e.1.1).onOne j)]
      · simp
      · intro x hx
        simp [hx]
theorem weightReductionForward_commutes_boundary1_horizontal
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    weightReductionForwardMap0 D
        (boundary1 (weightReducedData D)
          (reducedQubitBasisWord D
            (Sum.inl (q, i) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))) =
      boundary1 D
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D
            (Sum.inl (q, i) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))) := by
  classical
  rw [weightReductionForwardMap1_reducedQubitBasisWord_inl]
  cases q with
  | inl e =>
      rw [weightReductionForward_primaryBoundary_eq_transport]
      rw [ClassicalWeightReduction.combineForward_commutes_primaryBit
        (F := ZMod 2) R h e]
      unfold weightReductionForwardBaseOneBasis
      by_cases hroot : ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2
      · simp only [if_pos hroot]
        have hemb :
            boundary1 D
                (fun target :
                    QubitIndex baseZero baseOne fiberZero fiberOne =>
                  match target with
                  | Sum.inl target' =>
                      (Pi.single (e.1.2, i) (1 : ZMod 2) :
                        Word (ZMod 2) (baseOne × fiberZero)) target'
                  | Sum.inr _ => 0) =
              boundary1 D (Pi.single (Sum.inl (e.1.2, i)) 1) := by
          apply congrArg
            (fun w : Word (ZMod 2)
                (QubitIndex baseZero baseOne fiberZero fiberOne) =>
              boundary1 D w)
          ext target
          cases target with
          | inl target' =>
              by_cases htarget : target' = (e.1.2, i)
              · subst target'
                simp
              · have hsum :
                  (Sum.inl target' :
                    QubitIndex baseZero baseOne fiberZero fiberOne) ≠
                      Sum.inl (e.1.2, i) := by
                    simp [htarget]
                simp [htarget, hsum]
          | inr target' => simp
        rw [hemb]
        simpa [
          ClassicalWeightReduction.combineForwardMap1Basis, hroot,
          ClassicalWeightReduction.bitSplitBoundary_single,
          ClassicalWeightReduction.bitSplitBasisBoundary] using
          (incidenceTransportZero_bitSplitPrimaryBoundary D e.1.2 i)
      · simp [
          ClassicalWeightReduction.combineForwardMap1Basis, hroot]
  | inr a =>
      unfold reducedQubitBasisWord weightReductionForwardMap0
        ClassicalWeightReduction.linearMapOfBasisImages
        weightReductionForwardBaseOneBasis
      ext ai
      simp_rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_sum_type]
      simp [boundary1, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, weightReducedData, boundary1Matrix,
        weightReductionForwardBaseZeroBasis, Pi.single_apply,
        weightReducedConnection, FiberAutomorphism.id,
        ClassicalWeightReduction.basisBoundary,
        ClassicalWeightReduction.primaryBitBoundary,
        ClassicalWeightReduction.auxiliaryBitBoundary]
      simp_rw [ite_add_zero]
      rw [Finset.sum_add_distrib]
      rw [sum_target_times_incidence_single D ai
        (fun e => (e.1.1, i))
        (ClassicalWeightReduction.checkIncidenceAt R a.1
          (ClassicalWeightReduction.pathLeft a.2))]
      rw [sum_target_times_incidence_single D ai
        (fun e => (e.1.1, i))
        (ClassicalWeightReduction.checkIncidenceAt R a.1
          (ClassicalWeightReduction.pathRight a.2))]
      by_cases hai : ai = (a.1, i)
      · simp [ClassicalWeightReduction.checkIncidenceAt, hai]
        exact CharP.cast_eq_zero (ZMod 2) 2
      · simp [ClassicalWeightReduction.checkIncidenceAt, hai]
theorem weightReductionForward_commutes_boundary1
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (boundary1 D).comp (weightReductionForwardMap1 D h) =
      (weightReductionForwardMap0 D).comp
        (boundary1 (weightReducedData D)) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro q
  cases q with
  | inl bi =>
      simpa [LinearMap.comp_apply, reducedQubitBasisWord] using
        (weightReductionForward_commutes_boundary1_horizontal
          D h bi.1 bi.2).symm
  | inr aj =>
      simpa [LinearMap.comp_apply, reducedQubitBasisWord] using
        (weightReductionForward_commutes_boundary1_vertical
          D h aj.1 aj.2).symm
noncomputable def incidenceTransportOne (j : fiberOne) :
    Word (ZMod 2) (ClassicalWeightReduction.Incidence R) →ₗ[ZMod 2]
      Word (ZMod 2) (baseZero × fiberOne) :=
  ClassicalWeightReduction.linearMapOfBasisImages
    (fun e => Pi.single
      (e.1.1, (D.connection e.1.2 e.1.1).onOne j) 1)
omit [DecidableEq fiberZero] in
@[simp]
theorem incidenceTransportOne_apply (j : fiberOne)
    (w : Word (ZMod 2) (ClassicalWeightReduction.Incidence R))
    (aj : baseZero × fiberOne) :
    incidenceTransportOne D j w aj =
      ∑ e : ClassicalWeightReduction.Incidence R,
        if aj = (e.1.1, (D.connection e.1.2 e.1.1).onOne j) then
          w e
        else 0 := by
  classical
  unfold incidenceTransportOne
    ClassicalWeightReduction.linearMapOfBasisImages
  simp [Pi.single_apply]
omit [DecidableEq fiberZero] in
theorem weightReductionForwardBaseZeroOne_primaryBoundary_eq_transport
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    weightReductionForwardBaseZeroOneBasis D (Sum.inl e)
        ((D.connection e.1.2 e.1.1).onOne j) +
      (∑ a : ClassicalWeightReduction.AuxiliaryCheck R,
        (ClassicalWeightReduction.optionalSingle
              (F := ZMod 2)
              ((ClassicalWeightReduction.pathPrevious
                  (ClassicalWeightReduction.bitPosition R e)).map
                (ClassicalWeightReduction.auxiliaryCheckIndex R e.1.2))
              (Sum.inr a) +
          ClassicalWeightReduction.optionalSingle
              (F := ZMod 2)
              ((ClassicalWeightReduction.pathNext
                  (ClassicalWeightReduction.bitPosition R e)).map
                (ClassicalWeightReduction.auxiliaryCheckIndex R e.1.2))
              (Sum.inr a)) •
          weightReductionForwardBaseZeroOneBasis D (Sum.inr a) j) =
      incidenceTransportOne D j
        (ClassicalWeightReduction.combineForwardMap0 (F := ZMod 2) R
          (ClassicalWeightReduction.primaryBitBoundary
            (F := ZMod 2) R e)) := by
  classical
  let w := ClassicalWeightReduction.combineForwardMap0 (F := ZMod 2) R
    (ClassicalWeightReduction.primaryBitBoundary (F := ZMod 2) R e)
  change weightReductionForwardBaseZeroOneBasis D (Sum.inl e)
        ((D.connection e.1.2 e.1.1).onOne j) +
      (∑ a : ClassicalWeightReduction.AuxiliaryCheck R,
        (ClassicalWeightReduction.optionalSingle
              (F := ZMod 2)
              ((ClassicalWeightReduction.pathPrevious
                  (ClassicalWeightReduction.bitPosition R e)).map
                (ClassicalWeightReduction.auxiliaryCheckIndex R e.1.2))
              (Sum.inr a) +
          ClassicalWeightReduction.optionalSingle
              (F := ZMod 2)
              ((ClassicalWeightReduction.pathNext
                  (ClassicalWeightReduction.bitPosition R e)).map
                (ClassicalWeightReduction.auxiliaryCheckIndex R e.1.2))
              (Sum.inr a)) •
          weightReductionForwardBaseZeroOneBasis D (Sum.inr a) j) =
    incidenceTransportOne D j w
  ext aj
  rw [incidenceTransportOne_apply]
  simp (config := { zeta := false })
    [weightReductionForwardBaseZeroOneBasis,
      Pi.single_apply]
  rw [← sum_target_times_incidence_single D aj
    (fun x =>
      (x.1.1, (D.connection x.1.2 x.1.1).onOne j)) e]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases haj :
      aj = (x.1.1, (D.connection x.1.2 x.1.1).onOne j)
  · simp [haj, w, combineForwardMap0_primaryBitBoundary_apply]
  · simp [haj]
omit [DecidableEq fiberZero] in
theorem incidenceTransportOne_bitSplitPrimaryBoundary
    (b : baseOne) (j : fiberOne) :
    incidenceTransportOne D j
        (ClassicalWeightReduction.bitSplitPrimaryBoundary
          (F := ZMod 2) R b) =
      fun aj =>
        if aj.2 = (D.connection b aj.1).onOne j then
          D.baseBoundary aj.1 b
        else 0 := by
  classical
  ext aj
  rw [incidenceTransportOne_apply]
  unfold ClassicalWeightReduction.bitSplitPrimaryBoundary
  by_cases hbase : D.baseBoundary aj.1 b = 0
  · rw [show (if aj.2 = (D.connection b aj.1).onOne j then
        D.baseBoundary aj.1 b else 0) = 0 by simp [hbase]]
    apply Finset.sum_eq_zero
    intro e _he
    by_cases hlocation :
        aj = (e.1.1, (D.connection e.1.2 e.1.1).onOne j)
    · have hcheck : e.1.1 = aj.1 := by
        exact (congrArg Prod.fst hlocation).symm
      by_cases hbit : e.1.2 = b
      · exfalso
        exact e.2 (by simpa [hcheck, hbit] using hbase)
      · simp [hlocation, hbit]
    · simp [hlocation]
  · let target : ClassicalWeightReduction.Incidence R :=
      ⟨(aj.1, b), hbase⟩
    have hone : D.baseBoundary aj.1 b = 1 :=
      zmod_two_eq_one_of_ne_zero _ hbase
    rw [Fintype.sum_eq_single target]
    · simp [target, hone, Prod.ext_iff]
    · intro e hne
      by_cases hlocation :
          aj = (e.1.1, (D.connection e.1.2 e.1.1).onOne j)
      · by_cases hbit : e.1.2 = b
        · have hcheck : e.1.1 = aj.1 := by
            exact (congrArg Prod.fst hlocation).symm
          have hetarget : e = target := by
            apply Subtype.ext
            exact Prod.ext hcheck hbit
          exact (hne hetarget).elim
        · simp [hlocation, hbit]
      · simp [hlocation]
theorem weightReductionForwardMap1_apply_inl
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (x : Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne))
    (bi : baseOne × fiberZero) :
    weightReductionForwardMap1 D h x (Sum.inl bi) =
      ∑ qi : ClassicalWeightReduction.WeightReducedBit R × fiberZero,
        x (Sum.inl qi) *
          weightReductionForwardBaseOneBasis D h qi.1 qi.2 bi := by
  classical
  unfold weightReductionForwardMap1
    ClassicalWeightReduction.linearMapOfBasisImages
  simp_rw [Fintype.sum_sum_type]
  simp [smul_eq_mul]
theorem weightReductionForwardMap1_apply_inr
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (x : Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne))
    (aj : baseZero × fiberOne) :
    weightReductionForwardMap1 D h x (Sum.inr aj) =
      ∑ qi : ClassicalWeightReduction.WeightReducedCheck R × fiberOne,
        x (Sum.inr qi) *
          weightReductionForwardBaseZeroOneBasis D qi.1 qi.2 aj := by
  classical
  unfold weightReductionForwardMap1
    ClassicalWeightReduction.linearMapOfBasisImages
  simp_rw [Fintype.sum_sum_type]
  simp [smul_eq_mul]
theorem boundary2_reducedC2BasisWord_apply_inl
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne)
    (q' : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    boundary2 (weightReducedData D) (reducedC2BasisWord D q j)
        (Sum.inl (q', i)) =
      if q' = q then D.fiberBoundary i j else 0 := by
  classical
  unfold reducedC2BasisWord
  rw [boundary2_single_apply_inl]
  rfl
theorem boundary2_reducedC2BasisWord_apply_inr
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne)
    (a : ClassicalWeightReduction.WeightReducedCheck R) (j' : fiberOne) :
    boundary2 (weightReducedData D) (reducedC2BasisWord D q j)
        (Sum.inr (a, j')) =
      if j' = (weightReducedConnection D q a).onOne j then
        ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q a
      else 0 := by
  classical
  unfold reducedC2BasisWord
  rw [boundary2_single_apply_inr]
  rfl
theorem sum_ite_eq_mul
    {I : Type*} [Fintype I] [DecidableEq I]
    (target : I) (coefficient : ZMod 2) (f : I → ZMod 2) :
    (∑ x : I, (if x = target then coefficient else 0) * f x) =
      coefficient * f target := by
  rw [Fintype.sum_eq_single target]
  · simp
  · intro x hne
    simp [hne]
@[simp]
theorem weightReductionForward_auxiliary_boundary2_apply_inl
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (j : fiberOne)
    (bi : baseOne × fiberZero) :
    weightReductionForwardMap1 D h
        (boundary2 (weightReducedData D)
          (reducedC2BasisWord D (Sum.inr a) j)) (Sum.inl bi) = 0 := by
  rw [weightReductionForwardMap1_apply_inl]
  rw [Fintype.sum_prod_type]
  simp [boundary2_reducedC2BasisWord_apply_inl,
    weightReductionForwardBaseOneBasis]
@[simp]
theorem weightReductionForward_auxiliary_boundary2_apply_inr
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (j : fiberOne)
    (aj : baseZero × fiberOne) :
    weightReductionForwardMap1 D h
        (boundary2 (weightReducedData D)
          (reducedC2BasisWord D (Sum.inr a) j)) (Sum.inr aj) = 0 := by
  classical
  rw [weightReductionForwardMap1_apply_inr]
  rw [Fintype.sum_prod_type]
  simp_rw [boundary2_reducedC2BasisWord_apply_inr]
  simp_rw [sum_ite_eq_mul]
  rw [Fintype.sum_sum_type]
  simp [weightReducedConnection, FiberAutomorphism.id,
    ClassicalWeightReduction.basisBoundary,
    ClassicalWeightReduction.auxiliaryBitBoundary,
    weightReductionForwardBaseZeroOneBasis, Pi.single_apply]
  simp_rw [ite_add_zero]
  rw [Finset.sum_add_distrib]
  rw [sum_target_times_incidence_single D aj
    (fun e => (e.1.1, j))
    (ClassicalWeightReduction.checkIncidenceAt R a.1
      (ClassicalWeightReduction.pathLeft a.2))]
  rw [sum_target_times_incidence_single D aj
    (fun e => (e.1.1, j))
    (ClassicalWeightReduction.checkIncidenceAt R a.1
      (ClassicalWeightReduction.pathRight a.2))]
  by_cases haj : aj = (a.1, j)
  · simp [ClassicalWeightReduction.checkIncidenceAt, haj]
    exact CharP.cast_eq_zero (ZMod 2) 2
  · simp [ClassicalWeightReduction.checkIncidenceAt, haj]
theorem weightReductionForward_commutes_boundary2_basis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne) :
    weightReductionForwardMap1 D h
        (boundary2 (weightReducedData D) (reducedC2BasisWord D q j)) =
      boundary2 D
        (weightReductionForwardMap2 D h (reducedC2BasisWord D q j)) := by
  classical
  rw [weightReductionForwardMap2_reducedC2BasisWord]
  cases q with
  | inl e =>
      apply funext
      intro target
      cases target with
      | inl bi =>
          rw [weightReductionForwardMap1_apply_inl]
          rw [Fintype.sum_prod_type]
          simp_rw [boundary2_reducedC2BasisWord_apply_inl]
          unfold weightReductionForwardBaseOneOneBasis
          by_cases hroot : ClassicalWeightReduction.bitPosition R e =
              ClassicalWeightReduction.bitRootPosition R h e.1.2
          · simp [weightReductionForwardBaseOneBasis, hroot]
            rcases bi with ⟨b, i⟩
            by_cases hb : b = e.1.2
            · subst b
              rw [Fintype.sum_eq_single i]
              · simp [boundary2Matrix]
              · intro i' hne
                simp [hne]
            · simp [boundary2Matrix, hb]
          · simp [weightReductionForwardBaseOneBasis, hroot]
      | inr aj =>
          rw [weightReductionForwardMap1_apply_inr]
          rw [Fintype.sum_prod_type]
          simp_rw [boundary2_reducedC2BasisWord_apply_inr]
          simp_rw [sum_ite_eq_mul]
          rw [Fintype.sum_sum_type]
          simp [weightReducedConnection, FiberAutomorphism.id,
            ClassicalWeightReduction.basisBoundary,
            ClassicalWeightReduction.primaryBitBoundary,
            weightReductionForwardBaseOneOneBasis]
          rw [Fintype.sum_eq_single e]
          · simp only [Pi.single_eq_same, one_mul, if_true]
            have hf := congrFun
              (weightReductionForwardBaseZeroOne_primaryBoundary_eq_transport
                D e j) aj
            have hf' :
                weightReductionForwardBaseZeroOneBasis D (Sum.inl e)
                    ((D.connection e.1.2 e.1.1).onOne j) aj +
                  ∑ x : ClassicalWeightReduction.AuxiliaryCheck R,
                    (ClassicalWeightReduction.optionalSingle
                          (F := ZMod 2)
                          ((ClassicalWeightReduction.pathPrevious
                              (ClassicalWeightReduction.bitPosition R e)).map
                            (ClassicalWeightReduction.auxiliaryCheckIndex
                              R e.1.2))
                          (Sum.inr x) +
                      ClassicalWeightReduction.optionalSingle
                          (F := ZMod 2)
                          ((ClassicalWeightReduction.pathNext
                              (ClassicalWeightReduction.bitPosition R e)).map
                            (ClassicalWeightReduction.auxiliaryCheckIndex
                              R e.1.2))
                          (Sum.inr x)) *
                        weightReductionForwardBaseZeroOneBasis
                          D (Sum.inr x) j aj =
                  incidenceTransportOne D j
                    (ClassicalWeightReduction.combineForwardMap0
                      (F := ZMod 2) R
                      (ClassicalWeightReduction.primaryBitBoundary
                        (F := ZMod 2) R e)) aj := by
              simpa [Pi.smul_apply, smul_eq_mul] using hf
            rw [hf']
            rw [ClassicalWeightReduction.combineForward_commutes_primaryBit
              (F := ZMod 2) R h e]
            unfold ClassicalWeightReduction.combineForwardMap1Basis
            by_cases hroot : ClassicalWeightReduction.bitPosition R e =
                ClassicalWeightReduction.bitRootPosition R h e.1.2
            · simp only [hroot, if_pos]
              rw [ClassicalWeightReduction.bitSplitBoundary_single]
              unfold ClassicalWeightReduction.bitSplitBasisBoundary
              rw [incidenceTransportOne_bitSplitPrimaryBoundary]
              rw [boundary2_single_apply_inr]
            · simp [hroot]
          · intro x hne
            simp [hne]
  | inr a =>
      apply funext
      intro target
      cases target
      all_goals simp [weightReductionForwardBaseOneOneBasis]
theorem weightReductionForward_commutes_boundary2
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (boundary2 D).comp (weightReductionForwardMap2 D h) =
      (weightReductionForwardMap1 D h).comp
        (boundary2 (weightReducedData D)) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro qj
  simpa [LinearMap.comp_apply, reducedC2BasisWord] using
    (weightReductionForward_commutes_boundary2_basis
      D h qj.1 qj.2).symm
noncomputable def weightReductionForwardChainMap
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    ThreeTermChainMap (chainComplex (weightReducedData D))
      (chainComplex D) where
  map0 := weightReductionForwardMap0 D
  map1 := weightReductionForwardMap1 D h
  map2 := weightReductionForwardMap2 D h
  commutes_boundary1 := weightReductionForward_commutes_boundary1 D h
  commutes_boundary2 := weightReductionForward_commutes_boundary2 D h
end TwistedForward
section TwistedInverse
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
noncomputable def inverseAuxiliaryCoefficient
    (b : baseOne) (a : ClassicalWeightReduction.AuxiliaryBit R) : ZMod 2 :=
  ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R
    (ClassicalWeightReduction.bitSplitPrimaryBoundary
      (F := ZMod 2) R b) (Sum.inr a)
noncomputable def weightReductionInverseBaseZeroBasis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (c : baseZero) (i : fiberZero) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :=
  Pi.single
    (Sum.inl
      (ClassicalWeightReduction.checkIncidenceAt R c
        (ClassicalWeightReduction.checkRootPosition R h c)), i) 1
noncomputable def weightReductionInverseBaseZeroOneBasis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (c : baseZero) (j : fiberOne) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :=
  Pi.single
    (Sum.inl
      (ClassicalWeightReduction.checkIncidenceAt R c
        (ClassicalWeightReduction.checkRootPosition R h c)), j) 1
noncomputable def weightReductionInverseBaseOneBasis
    (b : baseOne) (i : fiberZero) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedBit R × fiberZero) :=
  (∑ e : ClassicalWeightReduction.Incidence R,
      (if e.1.2 = b then (1 : ZMod 2) else 0) •
        Pi.single (Sum.inl e, i) 1) +
    ∑ a : ClassicalWeightReduction.AuxiliaryBit R,
      inverseAuxiliaryCoefficient D b a •
        Pi.single
          (Sum.inr a, (D.connection b a.1).onZero i) 1
noncomputable def weightReductionInverseBaseOneOneBasis
    (b : baseOne) (j : fiberOne) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedBit R × fiberOne) :=
  (∑ e : ClassicalWeightReduction.Incidence R,
      (if e.1.2 = b then (1 : ZMod 2) else 0) •
        Pi.single (Sum.inl e, j) 1) +
    ∑ a : ClassicalWeightReduction.AuxiliaryBit R,
      inverseAuxiliaryCoefficient D b a •
        Pi.single
          (Sum.inr a, (D.connection b a.1).onOne j) 1
noncomputable def weightReductionInverseMap0
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    Word (ZMod 2) (baseZero × fiberZero) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :=
  ClassicalWeightReduction.linearMapOfBasisImages
    (fun ci => weightReductionInverseBaseZeroBasis D h ci.1 ci.2)
noncomputable def weightReductionInverseMap1
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (fun q target =>
        match q, target with
        | Sum.inl bi, Sum.inl target' =>
            weightReductionInverseBaseOneBasis D bi.1 bi.2 target'
        | Sum.inr aj, Sum.inr target' =>
            weightReductionInverseBaseZeroOneBasis D h aj.1 aj.2 target'
        | _, _ => 0)
noncomputable def weightReductionInverseMap2 :
    Word (ZMod 2) (baseOne × fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedBit R × fiberOne) :=
  ClassicalWeightReduction.linearMapOfBasisImages
    (fun bj => weightReductionInverseBaseOneOneBasis D bj.1 bj.2)
omit [DecidableEq fiberOne] in
@[simp]
theorem weightReductionInverseMap0_single
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (c : baseZero) (i : fiberZero) :
    weightReductionInverseMap0 D h (Pi.single (c, i) 1) =
      weightReductionInverseBaseZeroBasis D h c i := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
@[simp]
theorem weightReductionInverseMap1_single_inl
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (i : fiberZero) :
    weightReductionInverseMap1 D h
        (Pi.single
          (Sum.inl (b, i) :
            QubitIndex baseZero baseOne fiberZero fiberOne) 1) =
      fun target =>
        match target with
        | Sum.inl target' =>
            weightReductionInverseBaseOneBasis D b i target'
        | Sum.inr _ => 0 := by
  classical
  unfold weightReductionInverseMap1
  rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
  ext target
  cases target <;> rfl
@[simp]
theorem weightReductionInverseMap1_single_inr
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (c : baseZero) (j : fiberOne) :
    weightReductionInverseMap1 D h
        (Pi.single
          (Sum.inr (c, j) :
            QubitIndex baseZero baseOne fiberZero fiberOne) 1) =
      fun target =>
        match target with
        | Sum.inl _ => 0
        | Sum.inr target' =>
            weightReductionInverseBaseZeroOneBasis D h c j target' := by
  classical
  unfold weightReductionInverseMap1
  rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
  ext target
  cases target <;> rfl
omit [DecidableEq fiberZero] in
@[simp]
theorem weightReductionInverseMap2_single
    (b : baseOne) (j : fiberOne) :
    weightReductionInverseMap2 D (Pi.single (b, j) 1) =
      weightReductionInverseBaseOneOneBasis D b j := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
omit [DecidableEq fiberOne] in
@[simp]
theorem weightReductionForward_inverse_baseZero
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (c : baseZero) (i : fiberZero) :
    weightReductionForwardMap0 D
        (weightReductionInverseBaseZeroBasis D h c i) =
      Pi.single (c, i) 1 := by
  classical
  unfold weightReductionInverseBaseZeroBasis weightReductionForwardMap0
  rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
  simp [weightReductionForwardBaseZeroBasis,
    ClassicalWeightReduction.checkIncidenceAt]
@[simp]
theorem weightReductionForward_inverse_baseZeroOne
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (c : baseZero) (j : fiberOne) :
    weightReductionForwardMap1 D h
        (fun target =>
          match target with
          | Sum.inl _ => 0
          | Sum.inr target' =>
              weightReductionInverseBaseZeroOneBasis D h c j target') =
      Pi.single
        (Sum.inr (c, j) :
          QubitIndex baseZero baseOne fiberZero fiberOne) 1 := by
  classical
  apply funext
  intro target
  cases target with
  | inl bi =>
      rw [weightReductionForwardMap1_apply_inl]
      simp
  | inr aj =>
      rw [weightReductionForwardMap1_apply_inr]
      unfold weightReductionInverseBaseZeroOneBasis
      rw [Fintype.sum_eq_single
        (Sum.inl
          (ClassicalWeightReduction.checkIncidenceAt R c
            (ClassicalWeightReduction.checkRootPosition R h c)), j)]
      · simp [weightReductionForwardBaseZeroOneBasis, Pi.single_apply,
          ClassicalWeightReduction.checkIncidenceAt]
      · intro x hne
        simp [hne]
omit [DecidableEq fiberOne] in
@[simp]
theorem weightReductionInverseBaseOneBasis_apply_primary
    (b : baseOne) (i : fiberZero)
    (e : ClassicalWeightReduction.Incidence R) (k : fiberZero) :
    weightReductionInverseBaseOneBasis D b i (Sum.inl e, k) =
      if e.1.2 = b ∧ k = i then 1 else 0 := by
  classical
  unfold weightReductionInverseBaseOneBasis
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, Sum.inl.injEq,
    Prod.mk.injEq, Sum.inl.injEq,
    Sum.inl_ne_inr, false_and, if_false, mul_zero,
    Finset.sum_const_zero, add_zero]
  by_cases heb : e.1.2 = b
  · rw [Fintype.sum_eq_single e]
    · simp [heb]
    · intro c hne
      simp [Ne.symm hne]
  · rw [show (if e.1.2 = b ∧ k = i then (1 : ZMod 2) else 0) = 0 by
      simp [heb]]
    apply Finset.sum_eq_zero
    intro c _hc
    by_cases hce : c = e
    · subst c
      simp [heb]
    · simp [Ne.symm hce]
omit [DecidableEq fiberZero] in
@[simp]
theorem weightReductionInverseBaseOneOneBasis_apply_primary
    (b : baseOne) (j : fiberOne)
    (e : ClassicalWeightReduction.Incidence R) (k : fiberOne) :
    weightReductionInverseBaseOneOneBasis D b j (Sum.inl e, k) =
      if e.1.2 = b ∧ k = j then 1 else 0 := by
  classical
  unfold weightReductionInverseBaseOneOneBasis
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, Sum.inl.injEq,
    Prod.mk.injEq, Sum.inl.injEq,
    Sum.inl_ne_inr, false_and, if_false, mul_zero,
    Finset.sum_const_zero, add_zero]
  by_cases heb : e.1.2 = b
  · rw [Fintype.sum_eq_single e]
    · simp [heb]
    · intro c hne
      simp [Ne.symm hne]
  · rw [show (if e.1.2 = b ∧ k = j then (1 : ZMod 2) else 0) = 0 by
      simp [heb]]
    apply Finset.sum_eq_zero
    intro c _hc
    by_cases hce : c = e
    · subst c
      simp [heb]
    · simp [Ne.symm hce]
@[simp]
theorem weightReductionInverseBaseOneBasis_apply_auxiliary
    (b : baseOne) (i : fiberZero)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (k : fiberZero) :
    weightReductionInverseBaseOneBasis D b i (Sum.inr a, k) =
      if k = (D.connection b a.1).onZero i then
        inverseAuxiliaryCoefficient D b a
      else 0 := by
  classical
  unfold weightReductionInverseBaseOneBasis
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, Sum.inr.injEq,
    Sum.inr_ne_inl, if_false, mul_zero,
    Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_eq_single a]
  · simp [Prod.ext_iff, mul_comm]
  · intro a' hne
    simp [Ne.symm hne]
omit [DecidableEq fiberZero] in
@[simp]
theorem weightReductionInverseBaseOneOneBasis_apply_auxiliary
    (b : baseOne) (j : fiberOne)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (k : fiberOne) :
    weightReductionInverseBaseOneOneBasis D b j (Sum.inr a, k) =
      if k = (D.connection b a.1).onOne j then
        inverseAuxiliaryCoefficient D b a
      else 0 := by
  classical
  unfold weightReductionInverseBaseOneOneBasis
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, Sum.inr.injEq,
    Sum.inr_ne_inl, if_false, mul_zero,
    Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_eq_single a]
  · simp [Prod.ext_iff, mul_comm]
  · intro a' hne
    simp [Ne.symm hne]
omit [DecidableEq baseZero] [DecidableEq fiberZero]
    [DecidableEq fiberOne] in
theorem rootedPrimarySum
    {K : Type*} [Fintype K] [DecidableEq K]
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (k : K) (target : baseOne × K) :
    (∑ e : ClassicalWeightReduction.Incidence R,
      ∑ l : K,
        (if e.1.2 = b ∧ l = k then (1 : ZMod 2) else 0) *
          (if ClassicalWeightReduction.bitPosition R e =
              ClassicalWeightReduction.bitRootPosition R h e.1.2 then
            (Pi.single (e.1.2, l) 1 :
              Word (ZMod 2) (baseOne × K))
          else 0) target) =
      (Pi.single (b, k) 1 : Word (ZMod 2) (baseOne × K)) target := by
  classical
  let root := ClassicalWeightReduction.bitIncidenceAt R b
    (ClassicalWeightReduction.bitRootPosition R h b)
  rw [Fintype.sum_eq_single root]
  · rw [Fintype.sum_eq_single k]
    · have hrootpos :=
        ClassicalWeightReduction.bitPosition_bitIncidenceAt R b
          (ClassicalWeightReduction.bitRootPosition R h b)
      have hrootbit : root.1.2 = b := by
        rfl
      have hrootpos' : ClassicalWeightReduction.bitPosition R root =
          ClassicalWeightReduction.bitRootPosition R h root.1.2 := by
        dsimp [root]
        exact hrootpos
      rw [if_pos (And.intro hrootbit rfl), if_pos hrootpos']
      rw [hrootbit]
      simp
    · intro l hne
      simp [hne]
  · intro e hne
    apply Finset.sum_eq_zero
    intro l _hl
    by_cases heb : e.1.2 = b
    · have hpos : ClassicalWeightReduction.bitPosition R e ≠
          ClassicalWeightReduction.bitRootPosition R h e.1.2 := by
        intro heq
        apply hne
        calc
          e = ClassicalWeightReduction.bitIncidenceAt R e.1.2
                (ClassicalWeightReduction.bitPosition R e) :=
            (ClassicalWeightReduction.bitIncidenceAt_bitPosition R e).symm
          _ = root := by
            subst b
            simp [root, heq]
      simp [heb, hpos]
    · simp [heb]
@[simp]
theorem weightReductionForward_inverse_baseOne
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (i : fiberZero) :
    weightReductionForwardMap1 D h
        (fun target =>
          match target with
          | Sum.inl target' =>
              weightReductionInverseBaseOneBasis D b i target'
          | Sum.inr _ => 0) =
      Pi.single
        (Sum.inl (b, i) :
          QubitIndex baseZero baseOne fiberZero fiberOne) 1 := by
  classical
  apply funext
  intro target
  cases target with
  | inl bi =>
      rw [weightReductionForwardMap1_apply_inl]
      rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
      simp [weightReductionForwardBaseOneBasis, Pi.single_apply]
      simpa [Pi.single_apply, ite_mul, mul_ite] using
        (rootedPrimarySum D h b i bi)
  | inr aj =>
      rw [weightReductionForwardMap1_apply_inr]
      simp
omit [DecidableEq fiberZero] in
@[simp]
theorem weightReductionForward_inverse_baseOneOne
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (j : fiberOne) :
    weightReductionForwardMap2 D h
        (weightReductionInverseBaseOneOneBasis D b j) =
      Pi.single (b, j) 1 := by
  classical
  apply funext
  intro target
  unfold weightReductionForwardMap2
    ClassicalWeightReduction.linearMapOfBasisImages
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp [weightReductionForwardBaseOneOneBasis, Pi.single_apply]
  calc
    _ = ∑ e : ClassicalWeightReduction.Incidence R,
        ∑ k : fiberOne,
          (if e.1.2 = b ∧ k = j then (1 : ZMod 2) else 0) *
            (if ClassicalWeightReduction.bitPosition R e =
                ClassicalWeightReduction.bitRootPosition R h e.1.2 then
              (Pi.single (e.1.2, k) 1 :
                Word (ZMod 2) (baseOne × fiberOne))
            else 0) target := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hpos : ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2
      · simp [hpos]
        apply Finset.sum_congr rfl
        intro k _hk
        by_cases hcoefficient : e.1.2 = b ∧ k = j
        · simp [hcoefficient]
        · simp [hcoefficient]
      · simp [hpos]
    _ = _ := by
      simpa [Pi.single_apply] using
        (rootedPrimarySum D h b j target)
omit [DecidableEq fiberOne] in
/-- The forward map followed after the rooted inverse is strictly the
identity in degree zero. -/
theorem weightReductionForwardMap0_comp_inverseMap0
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (weightReductionForwardMap0 D).comp
        (weightReductionInverseMap0 D h) = LinearMap.id := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro ci
  rw [LinearMap.comp_apply, weightReductionInverseMap0_single,
    LinearMap.id_apply]
  exact weightReductionForward_inverse_baseZero D h ci.1 ci.2
theorem weightReductionForwardMap1_comp_inverseMap1
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (weightReductionForwardMap1 D h).comp
        (weightReductionInverseMap1 D h) = LinearMap.id := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro q
  cases q with
  | inl bi =>
      rw [LinearMap.comp_apply, weightReductionInverseMap1_single_inl,
        LinearMap.id_apply]
      exact weightReductionForward_inverse_baseOne D h bi.1 bi.2
  | inr aj =>
      rw [LinearMap.comp_apply, weightReductionInverseMap1_single_inr,
        LinearMap.id_apply]
      exact weightReductionForward_inverse_baseZeroOne D h aj.1 aj.2
omit [DecidableEq fiberZero] in
/-- The forward map followed after the rooted inverse is strictly the
identity in degree two. -/
theorem weightReductionForwardMap2_comp_inverseMap2
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (weightReductionForwardMap2 D h).comp
        (weightReductionInverseMap2 D) = LinearMap.id := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro bj
  rw [LinearMap.comp_apply, weightReductionInverseMap2_single,
    LinearMap.id_apply]
  exact weightReductionForward_inverse_baseOneOne D h bj.1 bj.2
theorem weightReductionInverse_commutes_boundary1_vertical
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (c : baseZero) (j : fiberOne) :
    boundary1 (weightReducedData D)
        (weightReductionInverseMap1 D h
          (Pi.single
            (Sum.inr (c, j) :
              QubitIndex baseZero baseOne fiberZero fiberOne) 1)) =
      weightReductionInverseMap0 D h
        (boundary1 D
          (Pi.single
            (Sum.inr (c, j) :
              QubitIndex baseZero baseOne fiberZero fiberOne) 1)) := by
  classical
  rw [weightReductionInverseMap1_single_inr]
  have hword :
      (fun target : QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne =>
        match target with
        | Sum.inl _ => 0
        | Sum.inr target' =>
            weightReductionInverseBaseZeroOneBasis D h c j target') =
        reducedQubitBasisWord D
          (Sum.inr
            (Sum.inl
              (ClassicalWeightReduction.checkIncidenceAt R c
                (ClassicalWeightReduction.checkRootPosition R h c)), j)) := by
    ext target
    cases target <;>
      simp [weightReductionInverseBaseZeroOneBasis,
        reducedQubitBasisWord, Pi.single_apply]
  rw [hword]
  rw [boundary1_single_inr (D := D)]
  ext target
  unfold reducedQubitBasisWord boundary1 weightReductionInverseMap0
    ClassicalWeightReduction.linearMapOfBasisImages
  simp_rw [Fintype.sum_prod_type]
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    weightReducedData, boundary1Matrix,
    weightReductionInverseBaseZeroBasis, Pi.single_apply,
    ClassicalWeightReduction.checkIncidenceAt]
  rw [Fintype.sum_eq_single c]
  · simp only [if_true, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_apply, mul_ite, mul_one]
    let rootCheck : ClassicalWeightReduction.WeightReducedCheck R :=
      Sum.inl
        (ClassicalWeightReduction.checkIncidenceAt R c
          (ClassicalWeightReduction.checkRootPosition R h c))
    change (if target.1 = rootCheck then D.fiberBoundary target.2 j else 0) =
      ∑ i : fiberZero,
        if target = (rootCheck, i) then D.fiberBoundary i j else 0
    by_cases ht : target.1 = rootCheck
    · rw [if_pos ht, Fintype.sum_eq_single target.2]
      · simp [Prod.ext_iff, ht]
      · intro i hne
        simp [Prod.ext_iff, ht, Ne.symm hne]
    · rw [if_neg ht]
      symm
      apply Finset.sum_eq_zero
      intro i _hi
      simp [Prod.ext_iff, ht]
  · intro c' hne
    simp [hne]
noncomputable def inverseClassicalBaseOneBasis (b : baseOne) :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R) :=
  (∑ e : ClassicalWeightReduction.Incidence R,
      (if e.1.2 = b then (1 : ZMod 2) else 0) •
        Pi.single (Sum.inl e) 1) +
    ∑ a : ClassicalWeightReduction.AuxiliaryBit R,
      inverseAuxiliaryCoefficient D b a • Pi.single (Sum.inr a) 1
@[simp]
theorem inverseClassicalBaseOneBasis_apply_primary
    (b : baseOne) (e : ClassicalWeightReduction.Incidence R) :
    inverseClassicalBaseOneBasis D b (Sum.inl e) =
      if e.1.2 = b then 1 else 0 := by
  classical
  unfold inverseClassicalBaseOneBasis
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, Sum.inl.injEq,
    Sum.inl_ne_inr, false_and, if_false, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_eq_single e]
  · simp
  · intro e' hne
    simp [Ne.symm hne]
@[simp]
theorem inverseClassicalBaseOneBasis_apply_auxiliary
    (b : baseOne) (a : ClassicalWeightReduction.AuxiliaryBit R) :
    inverseClassicalBaseOneBasis D b (Sum.inr a) =
      inverseAuxiliaryCoefficient D b a := by
  classical
  unfold inverseClassicalBaseOneBasis
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, Sum.inr.injEq,
    Sum.inr_ne_inl, if_false, mul_zero,
    Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro a' hne
    simp [Ne.symm hne]
noncomputable def inverseBitTransportZero (b : baseOne) (i : fiberZero) :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (fun q =>
        match q with
        | Sum.inl e => Pi.single (Sum.inl (Sum.inl e, i)) 1
        | Sum.inr a =>
            Pi.single
              (Sum.inl
                (Sum.inr a, (D.connection b a.1).onZero i)) 1)
noncomputable def inverseCheckTransportZero (b : baseOne) (i : fiberZero) :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedCheck R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :=
  ClassicalWeightReduction.linearMapOfBasisImages
    (fun q =>
      match q with
      | Sum.inl e =>
          Pi.single
            (Sum.inl e, (D.connection b e.1.1).onZero i) 1
      | Sum.inr a => Pi.single (Sum.inr a, i) 1)
@[simp]
theorem inverseBitTransportZero_classicalBasis
    (b : baseOne) (i : fiberZero) :
    inverseBitTransportZero D b i (inverseClassicalBaseOneBasis D b) =
      fun target =>
        match target with
        | Sum.inl target' =>
            weightReductionInverseBaseOneBasis D b i target'
        | Sum.inr _ => 0 := by
  classical
  unfold inverseBitTransportZero
    ClassicalWeightReduction.linearMapOfBasisImages
  ext target
  simp_rw [Fintype.sum_sum_type]
  cases target with
  | inl target' =>
      rcases target' with ⟨q, k⟩
      cases q with
      | inl e =>
          simp [weightReductionInverseBaseOneBasis_apply_primary,
            Pi.single_apply]
          by_cases heb : e.1.2 = b
          · rw [Fintype.sum_eq_single e]
            · rw [if_pos heb, Pi.single_apply]
              simp [heb, Prod.ext_iff]
            · intro e' hne
              by_cases he'b : e'.1.2 = b
              · rw [if_pos he'b, Pi.single_apply]
                simp [Ne.symm hne]
              · rw [if_neg he'b]
                rfl
          · rw [show (if e.1.2 = b ∧ k = i then (1 : ZMod 2) else 0) = 0 by
              simp [heb]]
            apply Finset.sum_eq_zero
            intro e' _he
            by_cases he'e : e' = e
            · subst e'
              rw [if_neg heb]
              rfl
            · by_cases he'b : e'.1.2 = b
              · rw [if_pos he'b, Pi.single_apply]
                simp [Ne.symm he'e]
              · rw [if_neg he'b]
                rfl
      | inr a =>
          simp [weightReductionInverseBaseOneBasis, Pi.single_apply]
          apply Finset.sum_congr rfl
          intro e _he
          by_cases heb : e.1.2 = b
          · rw [if_pos heb, if_pos heb, Pi.single_apply, Pi.single_apply]
            simp
          · simp [heb]
  | inr target' =>
      simp [Pi.single_apply]
      apply Finset.sum_eq_zero
      intro e _he
      by_cases heb : e.1.2 = b
      · rw [if_pos heb, Pi.single_apply]
        simp
      · rw [if_neg heb]
        rfl
theorem collapseHomotopy0_apply_original_anyUniverse
    (x : Word (ZMod 2) (ClassicalWeightReduction.BitSplitCheck R))
    (b : baseOne) :
    ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R x
        (Sum.inl b) = 0 := by
  classical
  unfold ClassicalWeightReduction.collapseHomotopy0
    ClassicalWeightReduction.linearMapOfBasisImages
  change (∑ e : ClassicalWeightReduction.BitSplitCheck R,
    x e • ClassicalWeightReduction.collapseHomotopy0Basis
      (F := ZMod 2) R e) (Sum.inl b) = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro e _he
  simp [ClassicalWeightReduction.collapseHomotopy0Basis,
    ClassicalWeightReduction.checkPathAuxiliaryPrefix]
theorem inverseClassicalBaseOneBasis_eq_composedInverse
    (b : baseOne) :
    inverseClassicalBaseOneBasis D b =
      ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
        (ClassicalWeightReduction.collapseInverseMap1 (F := ZMod 2) R
          (Pi.single b 1)) := by
  classical
  rw [ClassicalWeightReduction.collapseInverseMap1_single]
  unfold ClassicalWeightReduction.collapseInverseMap1Basis
  rw [map_add, ClassicalWeightReduction.combineInverseMap1_single]
  unfold ClassicalWeightReduction.combineInverseMap1Basis
  ext q
  cases q with
  | inl e =>
      simp [inverseClassicalBaseOneBasis_apply_primary,
        ClassicalWeightReduction.allPrimaryBitCopies,
        ClassicalWeightReduction.combineInverseMap1,
        ClassicalWeightReduction.linearMapOfBasisImages,
        ClassicalWeightReduction.combineInverseMap1Basis]
      exact collapseHomotopy0_apply_original_anyUniverse D
        (ClassicalWeightReduction.bitSplitPrimaryBoundary
          (F := ZMod 2) R b) e.1.2
  | inr a =>
      simp [inverseClassicalBaseOneBasis_apply_auxiliary,
        ClassicalWeightReduction.combineInverseMap1,
        ClassicalWeightReduction.linearMapOfBasisImages,
        ClassicalWeightReduction.combineInverseMap1Basis,
        ClassicalWeightReduction.allPrimaryBitCopies,
        inverseAuxiliaryCoefficient, Pi.single_apply]
theorem boundary_inverseClassicalBaseOneBasis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) :
    ClassicalWeightReduction.boundary (F := ZMod 2) R
        (inverseClassicalBaseOneBasis D b) =
      ClassicalWeightReduction.combineInverseMap0 (F := ZMod 2) R
        (ClassicalWeightReduction.collapseInverseMap0 (F := ZMod 2) R h
          (ClassicalWeightReduction.originalBasisBoundary
            (F := ZMod 2) R b)) := by
  rw [inverseClassicalBaseOneBasis_eq_composedInverse]
  calc
    ClassicalWeightReduction.boundary (F := ZMod 2) R
          (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseInverseMap1
              (F := ZMod 2) R (Pi.single b 1))) =
        ClassicalWeightReduction.combineInverseMap0 (F := ZMod 2) R
          (ClassicalWeightReduction.bitSplitBoundary (F := ZMod 2) R
            (ClassicalWeightReduction.collapseInverseMap1
              (F := ZMod 2) R (Pi.single b 1))) := by
      exact LinearMap.congr_fun
        (ClassicalWeightReduction.combineInverse_commutes_boundary
          (F := ZMod 2) R)
        (ClassicalWeightReduction.collapseInverseMap1
          (F := ZMod 2) R (Pi.single b 1))
    _ = ClassicalWeightReduction.combineInverseMap0 (F := ZMod 2) R
          (ClassicalWeightReduction.collapseInverseMap0
            (F := ZMod 2) R h
            (ClassicalWeightReduction.originalBoundary (F := ZMod 2) R
              (Pi.single b 1))) := by
      congr 1
      exact LinearMap.congr_fun
        (ClassicalWeightReduction.collapseInverse_commutes_boundary
          (F := ZMod 2) R h) (Pi.single b 1)
    _ = _ := by
      rw [ClassicalWeightReduction.originalBoundary_single]
theorem inverseTransport_primary_boundary
    (b : baseOne) (i : fiberZero)
    (e : ClassicalWeightReduction.Incidence R)
    (heb : e.1.2 = b) :
    boundary1 (weightReducedData D)
        (reducedQubitBasisWord D
          (Sum.inl (Sum.inl e, i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne)) =
      inverseCheckTransportZero D b i
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (Pi.single (Sum.inl e) 1)) := by
  classical
  ext target
  unfold reducedQubitBasisWord boundary1 inverseCheckTransportZero
    ClassicalWeightReduction.boundary
    ClassicalWeightReduction.linearMapOfBasisImages
  simp
    [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    weightReducedData, boundary1Matrix, weightReducedConnection,
    FiberAutomorphism.id, ClassicalWeightReduction.basisBoundary,
    ClassicalWeightReduction.primaryBitBoundary,
    ClassicalWeightReduction.auxiliaryBitBoundary,
    Pi.single_apply, heb]
  rw [Fintype.sum_eq_single e]
  · rcases target with ⟨q, k⟩
    cases q with
    | inl e' =>
        simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inl_ne_inr,
          false_and, if_false, Finset.sum_const_zero, add_zero]
        by_cases hee' : e = e'
        · subst e'
          rw [Fintype.sum_eq_single e]
          · simp [weightReducedConnection, heb]
          · intro x hne
            simp [Ne.symm hne]
        · rw [Fintype.sum_eq_single e']
          · simp [weightReducedConnection, hee', Ne.symm hee']
          · intro x hne
            simp [Ne.symm hne]
    | inr a =>
        simp only [Prod.mk.injEq, Sum.inr.injEq, Sum.inr_ne_inl,
          false_and, if_false, Finset.sum_const_zero, zero_add]
        rw [Fintype.sum_eq_single a]
        · simp <;> rfl
        · intro x hne
          simp [Ne.symm hne]
  · intro e' hne
    simp [hne]
theorem inverseTransport_auxiliary_boundary
    (b : baseOne) (i : fiberZero)
    (a : ClassicalWeightReduction.AuxiliaryBit R) :
    boundary1 (weightReducedData D)
        (reducedQubitBasisWord D
          (Sum.inl
            (Sum.inr a, (D.connection b a.1).onZero i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne)) =
      inverseCheckTransportZero D b i
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (Pi.single (Sum.inr a) 1)) := by
  classical
  ext target
  unfold reducedQubitBasisWord boundary1 inverseCheckTransportZero
    ClassicalWeightReduction.boundary
    ClassicalWeightReduction.linearMapOfBasisImages
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    weightReducedData, boundary1Matrix, weightReducedConnection,
    FiberAutomorphism.id, ClassicalWeightReduction.basisBoundary,
    ClassicalWeightReduction.primaryBitBoundary,
    ClassicalWeightReduction.auxiliaryBitBoundary,
    Pi.single_apply]
  rw [Fintype.sum_eq_single a]
  · rcases target with ⟨q, k⟩
    cases q with
    | inl e =>
        simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inl_ne_inr,
          false_and, if_false, Finset.sum_const_zero, add_zero]
        rw [Fintype.sum_eq_single e]
        · by_cases hel : e =
              ClassicalWeightReduction.checkIncidenceAt R a.1
                (ClassicalWeightReduction.pathLeft a.2)
          · subst e
            simp [ClassicalWeightReduction.checkIncidenceAt]
            rw [Pi.single_apply]
            simp [ClassicalWeightReduction.checkIncidenceAt]
          · by_cases her : e =
                ClassicalWeightReduction.checkIncidenceAt R a.1
                  (ClassicalWeightReduction.pathRight a.2)
            · subst e
              simp [ClassicalWeightReduction.checkIncidenceAt]
              rw [Pi.single_apply]
              simp [ClassicalWeightReduction.checkIncidenceAt]
            · simp [hel, her]
        · intro e' hne
          simp [Ne.symm hne]
    | inr a' =>
        simp only [Prod.mk.injEq, Sum.inr.injEq, Sum.inr_ne_inl,
          false_and, if_false, Finset.sum_const_zero, zero_add]
        rw [Fintype.sum_eq_single a']
        · simp [weightReducedConnection, FiberAutomorphism.id]
        · intro x hne
          simp [Ne.symm hne]
  · intro a' hne
    simp [hne]
theorem inverseTransport_boundary_classicalBasis
    (b : baseOne) (i : fiberZero) :
    boundary1 (weightReducedData D)
        (inverseBitTransportZero D b i
          (inverseClassicalBaseOneBasis D b)) =
      inverseCheckTransportZero D b i
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (inverseClassicalBaseOneBasis D b)) := by
  classical
  unfold inverseClassicalBaseOneBasis
  simp only [map_add, map_sum, map_smul]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _he
    by_cases heb : e.1.2 = b
    · rw [if_pos heb, one_smul, one_smul]
      unfold inverseBitTransportZero
      rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
      exact inverseTransport_primary_boundary D b i e heb
    · simp [heb]
  · apply Finset.sum_congr rfl
    intro a _ha
    congr 1
    unfold inverseBitTransportZero
    rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
    exact inverseTransport_auxiliary_boundary D b i a
theorem inverseCheckTransport_classicalRootedBoundary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (i : fiberZero) :
    inverseCheckTransportZero D b i
        (ClassicalWeightReduction.combineInverseMap0 (F := ZMod 2) R
          (ClassicalWeightReduction.collapseInverseMap0
            (F := ZMod 2) R h
            (ClassicalWeightReduction.originalBasisBoundary
              (F := ZMod 2) R b))) =
      weightReductionInverseMap0 D h
        (boundary1 D
          (Pi.single
            (Sum.inl (b, i) :
              QubitIndex baseZero baseOne fiberZero fiberOne) 1)) := by
  classical
  rw [boundary1_single_inl]
  ext target
  unfold inverseCheckTransportZero
    ClassicalWeightReduction.combineInverseMap0
    ClassicalWeightReduction.collapseInverseMap0
    ClassicalWeightReduction.originalBasisBoundary
    weightReductionInverseMap0
    ClassicalWeightReduction.linearMapOfBasisImages
  simp_rw [Fintype.sum_prod_type]
  simp [ClassicalWeightReduction.combineInverseMap0Basis,
    ClassicalWeightReduction.collapseInverseMap0Basis,
    weightReductionInverseBaseZeroBasis, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hcb : R c b
  · have hnonzero : D.baseBoundary c b ≠ 0 := hcb
    have hone : D.baseBoundary c b = 1 :=
      zmod_two_eq_one_of_ne_zero _ hnonzero
    rw [Fintype.sum_eq_single
      (ClassicalWeightReduction.checkIncidenceAt R c
        (ClassicalWeightReduction.checkRootPosition R h c))]
    · simp [hcb, hone, ClassicalWeightReduction.checkIncidenceAt]
    · intro e hne
      by_cases htarget : target =
          (Sum.inl e, (D.connection b e.1.1).onZero i)
      · rw [if_pos htarget, if_pos hcb, Pi.single_apply]
        simp [hne]
      · rw [if_neg htarget]
  · have hzero : D.baseBoundary c b = 0 := by
      by_contra hne
      exact hcb hne
    rw [show (if target =
          (Sum.inl
              (ClassicalWeightReduction.checkIncidenceAt R c
                (ClassicalWeightReduction.checkRootPosition R h c)),
            (D.connection b c).onZero i) then
          D.baseBoundary c b else 0) = 0 by simp [hzero]]
    apply Finset.sum_eq_zero
    intro e _he
    simp [hcb]
theorem weightReductionInverse_commutes_boundary1_horizontal
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (i : fiberZero) :
    boundary1 (weightReducedData D)
        (weightReductionInverseMap1 D h
          (Pi.single
            (Sum.inl (b, i) :
              QubitIndex baseZero baseOne fiberZero fiberOne) 1)) =
      weightReductionInverseMap0 D h
        (boundary1 D
          (Pi.single
            (Sum.inl (b, i) :
              QubitIndex baseZero baseOne fiberZero fiberOne) 1)) := by
  rw [weightReductionInverseMap1_single_inl]
  rw [← inverseBitTransportZero_classicalBasis D b i]
  rw [inverseTransport_boundary_classicalBasis D b i]
  rw [boundary_inverseClassicalBaseOneBasis D h b]
  exact inverseCheckTransport_classicalRootedBoundary D h b i
theorem weightReductionInverse_commutes_boundary1
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (boundary1 (weightReducedData D)).comp
        (weightReductionInverseMap1 D h) =
      (weightReductionInverseMap0 D h).comp (boundary1 D) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro q
  cases q with
  | inl bi =>
      simpa [LinearMap.comp_apply] using
        weightReductionInverse_commutes_boundary1_horizontal
          D h bi.1 bi.2
  | inr aj =>
      simpa [LinearMap.comp_apply] using
        weightReductionInverse_commutes_boundary1_vertical
          D h aj.1 aj.2
theorem boundary2_apply_inl_word
    (x : Word (ZMod 2) (baseOne × fiberOne))
    (b : baseOne) (i : fiberZero) :
    boundary2 D x (Sum.inl (b, i)) =
      ∑ j : fiberOne, D.fiberBoundary i j * x (b, j) := by
  classical
  unfold boundary2
  rw [Matrix.toLin'_apply]
  unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single b]
  · simp [boundary2Matrix, mul_comm]
  · intro b' hne
    apply Finset.sum_eq_zero
    intro j _hj
    simp [boundary2Matrix, hne, Ne.symm hne]
theorem weightReductionInverseMap1_apply_inl
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (x : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (qi : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    weightReductionInverseMap1 D h x (Sum.inl qi) =
      ∑ bi : baseOne × fiberZero,
        x (Sum.inl bi) *
          weightReductionInverseBaseOneBasis D bi.1 bi.2 qi := by
  classical
  unfold weightReductionInverseMap1
    ClassicalWeightReduction.linearMapOfBasisImages
  simp_rw [Fintype.sum_sum_type]
  simp [smul_eq_mul]
theorem weightReductionInverseMap1_apply_inr
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (x : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (qj : ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
    weightReductionInverseMap1 D h x (Sum.inr qj) =
      ∑ aj : baseZero × fiberOne,
        x (Sum.inr aj) *
          weightReductionInverseBaseZeroOneBasis D h aj.1 aj.2 qj := by
  classical
  unfold weightReductionInverseMap1
    ClassicalWeightReduction.linearMapOfBasisImages
  simp_rw [Fintype.sum_sum_type]
  simp [smul_eq_mul]
theorem weightReductionInverse_commutes_boundary2_basis_apply_inl
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (j : fiberOne)
    (qi : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    boundary2 (weightReducedData D)
        (weightReductionInverseMap2 D (Pi.single (b, j) 1))
        (Sum.inl qi) =
      weightReductionInverseMap1 D h
        (boundary2 D (Pi.single (b, j) 1)) (Sum.inl qi) := by
  classical
  rw [weightReductionInverseMap2_single]
  rw [boundary2_apply_inl_word]
  rw [weightReductionInverseMap1_apply_inl]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single b]
  · rcases qi with ⟨q, i⟩
    cases q with
    | inl e =>
        simp only [weightReductionInverseBaseOneOneBasis_apply_primary,
          weightReductionInverseBaseOneBasis_apply_primary]
        by_cases heb : e.1.2 = b
        · rw [Fintype.sum_eq_single j]
          · rw [Fintype.sum_eq_single i]
            · simp [heb]
            · intro i' hne
              simp [heb, Ne.symm hne]
          · intro j' hne
            simp [hne]
        · simp [heb]
    | inr a =>
        simp only [weightReductionInverseBaseOneOneBasis_apply_auxiliary,
          weightReductionInverseBaseOneBasis_apply_auxiliary]
        rw [Fintype.sum_eq_single
          ((D.connection b a.1).onOne j)]
        · simpa [mul_comm] using
            (sum_fiberBoundary_transport_single D
              (D.connection b a.1)
              (inverseAuxiliaryCoefficient D b a) i j).symm
        · intro j' hne
          simp [hne]
  · intro b' hne
    apply Finset.sum_eq_zero
    intro i _hi
    simp [hne]
noncomputable def inverseBitTransportOne (b : baseOne) (j : fiberOne) :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedBit R × fiberOne) :=
  ClassicalWeightReduction.linearMapOfBasisImages
    (fun q =>
      match q with
      | Sum.inl e => Pi.single (Sum.inl e, j) 1
      | Sum.inr a =>
          Pi.single
            (Sum.inr a, (D.connection b a.1).onOne j) 1)
noncomputable def inverseCheckTransportOne (b : baseOne) (j : fiberOne) :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedCheck R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :=
  ClassicalWeightReduction.linearMapOfBasisImages
    (fun q =>
      match q with
      | Sum.inl e =>
          Pi.single
            (Sum.inl e, (D.connection b e.1.1).onOne j) 1
      | Sum.inr a => Pi.single (Sum.inr a, j) 1)
@[simp]
theorem inverseBitTransportOne_classicalBasis
    (b : baseOne) (j : fiberOne) :
    inverseBitTransportOne D b j (inverseClassicalBaseOneBasis D b) =
      weightReductionInverseBaseOneOneBasis D b j := by
  classical
  unfold inverseBitTransportOne inverseClassicalBaseOneBasis
    weightReductionInverseBaseOneOneBasis
  simp only [map_add, map_sum, map_smul]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _he
    by_cases heb : e.1.2 = b
    · rw [if_pos heb, one_smul, one_smul]
      rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
    · simp [heb]
  · apply Finset.sum_congr rfl
    intro a _ha
    congr 1
    rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
theorem inverseTransportOne_primary_boundary_apply
    (b : baseOne) (j : fiberOne)
    (e : ClassicalWeightReduction.Incidence R)
    (heb : e.1.2 = b)
    (target : ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
    boundary2 (weightReducedData D)
        (reducedC2BasisWord D (Sum.inl e) j) (Sum.inr target) =
      inverseCheckTransportOne D b j
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (Pi.single (Sum.inl e) 1)) target := by
  classical
  unfold reducedC2BasisWord boundary2 inverseCheckTransportOne
    ClassicalWeightReduction.boundary
    ClassicalWeightReduction.linearMapOfBasisImages
  simp
    [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    weightReducedData, boundary2Matrix, weightReducedConnection,
    FiberAutomorphism.id, ClassicalWeightReduction.basisBoundary,
    ClassicalWeightReduction.primaryBitBoundary,
    ClassicalWeightReduction.auxiliaryBitBoundary,
    Pi.single_apply, heb]
  rw [Fintype.sum_eq_single e]
  · rcases target with ⟨q, k⟩
    cases q with
    | inl e' =>
        simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inl_ne_inr,
          false_and, if_false, Finset.sum_const_zero, add_zero]
        by_cases hee' : e = e'
        · subst e'
          rw [Fintype.sum_eq_single e]
          · simp [weightReducedConnection, heb]
          · intro x hne
            simp [Ne.symm hne]
        · rw [Fintype.sum_eq_single e']
          · simp [weightReducedConnection, hee', Ne.symm hee']
          · intro x hne
            simp [Ne.symm hne]
    | inr a =>
        simp only [Prod.mk.injEq, Sum.inr.injEq, Sum.inr_ne_inl,
          false_and, if_false, Finset.sum_const_zero, zero_add]
        rw [Fintype.sum_eq_single a]
        · simp <;> rfl
        · intro x hne
          simp [Ne.symm hne]
  · intro e' hne
    simp [hne]
theorem inverseTransportOne_auxiliary_boundary_apply
    (b : baseOne) (j : fiberOne)
    (a : ClassicalWeightReduction.AuxiliaryBit R)
    (target : ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
    boundary2 (weightReducedData D)
        (reducedC2BasisWord D (Sum.inr a)
          ((D.connection b a.1).onOne j)) (Sum.inr target) =
      inverseCheckTransportOne D b j
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (Pi.single (Sum.inr a) 1)) target := by
  classical
  unfold reducedC2BasisWord boundary2 inverseCheckTransportOne
    ClassicalWeightReduction.boundary
    ClassicalWeightReduction.linearMapOfBasisImages
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    weightReducedData, boundary2Matrix, weightReducedConnection,
    FiberAutomorphism.id, ClassicalWeightReduction.basisBoundary,
    ClassicalWeightReduction.primaryBitBoundary,
    ClassicalWeightReduction.auxiliaryBitBoundary,
    Pi.single_apply]
  rw [Fintype.sum_eq_single a]
  · rcases target with ⟨q, k⟩
    cases q with
    | inl e =>
        simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inl_ne_inr,
          false_and, if_false, Finset.sum_const_zero, add_zero]
        rw [Fintype.sum_eq_single e]
        · by_cases hel : e =
              ClassicalWeightReduction.checkIncidenceAt R a.1
                (ClassicalWeightReduction.pathLeft a.2)
          · subst e
            simp [ClassicalWeightReduction.checkIncidenceAt]
            rw [Pi.single_apply]
            simp [ClassicalWeightReduction.checkIncidenceAt]
          · by_cases her : e =
                ClassicalWeightReduction.checkIncidenceAt R a.1
                  (ClassicalWeightReduction.pathRight a.2)
            · subst e
              simp [ClassicalWeightReduction.checkIncidenceAt]
              rw [Pi.single_apply]
              simp [ClassicalWeightReduction.checkIncidenceAt]
            · simp [hel, her]
        · intro e' hne
          simp [Ne.symm hne]
    | inr a' =>
        simp only [Prod.mk.injEq, Sum.inr.injEq, Sum.inr_ne_inl,
          false_and, if_false, Finset.sum_const_zero, zero_add]
        rw [Fintype.sum_eq_single a']
        · simp [weightReducedConnection, FiberAutomorphism.id]
        · intro x hne
          simp [Ne.symm hne]
  · intro a' hne
    simp [hne]
theorem inverseTransportOne_boundary_classicalBasis_apply
    (b : baseOne) (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
    boundary2 (weightReducedData D)
        (inverseBitTransportOne D b j
          (inverseClassicalBaseOneBasis D b)) (Sum.inr target) =
      inverseCheckTransportOne D b j
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (inverseClassicalBaseOneBasis D b)) target := by
  classical
  unfold inverseClassicalBaseOneBasis
  simp only [map_add, map_sum, map_smul, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _he
    by_cases heb : e.1.2 = b
    · rw [if_pos heb, one_smul, one_smul]
      unfold inverseBitTransportOne
      rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
      exact inverseTransportOne_primary_boundary_apply
        D b j e heb target
    · simp [heb]
  · apply Finset.sum_congr rfl
    intro a _ha
    congr 1
    unfold inverseBitTransportOne
    rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
    exact inverseTransportOne_auxiliary_boundary_apply
      D b j a target
theorem inverseCheckTransportOne_classicalRootedBoundary_apply
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
    inverseCheckTransportOne D b j
        (ClassicalWeightReduction.combineInverseMap0 (F := ZMod 2) R
          (ClassicalWeightReduction.collapseInverseMap0
            (F := ZMod 2) R h
            (ClassicalWeightReduction.originalBasisBoundary
              (F := ZMod 2) R b))) target =
      weightReductionInverseMap1 D h
        (boundary2 D (Pi.single (b, j) 1)) (Sum.inr target) := by
  classical
  rw [weightReductionInverseMap1_apply_inr]
  rw [Fintype.sum_prod_type]
  simp_rw [boundary2_single_apply_inr]
  unfold inverseCheckTransportOne
    ClassicalWeightReduction.combineInverseMap0
    ClassicalWeightReduction.collapseInverseMap0
    ClassicalWeightReduction.originalBasisBoundary
    ClassicalWeightReduction.linearMapOfBasisImages
  simp [ClassicalWeightReduction.combineInverseMap0Basis,
    ClassicalWeightReduction.collapseInverseMap0Basis,
    weightReductionInverseBaseZeroOneBasis, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hcb : R c b
  · have hnonzero : D.baseBoundary c b ≠ 0 := hcb
    have hone : D.baseBoundary c b = 1 :=
      zmod_two_eq_one_of_ne_zero _ hnonzero
    rw [Fintype.sum_eq_single
      (ClassicalWeightReduction.checkIncidenceAt R c
        (ClassicalWeightReduction.checkRootPosition R h c))]
    · rw [Fintype.sum_eq_single ((D.connection b c).onOne j)]
      · simp [hcb, hone, ClassicalWeightReduction.checkIncidenceAt]
      · intro k hne
        simp [hne]
    · intro e hne
      by_cases htarget : target =
          (Sum.inl e, (D.connection b e.1.1).onOne j)
      · rw [if_pos htarget, if_pos hcb, Pi.single_apply]
        simp [hne]
      · rw [if_neg htarget]
  · have hzero : D.baseBoundary c b = 0 := by
      by_contra hne
      exact hcb hne
    simp [hcb, hzero]
theorem weightReductionInverse_commutes_boundary2_basis_apply_inr
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
    boundary2 (weightReducedData D)
        (weightReductionInverseMap2 D (Pi.single (b, j) 1))
        (Sum.inr target) =
      weightReductionInverseMap1 D h
        (boundary2 D (Pi.single (b, j) 1)) (Sum.inr target) := by
  rw [weightReductionInverseMap2_single]
  rw [← inverseBitTransportOne_classicalBasis D b j]
  rw [inverseTransportOne_boundary_classicalBasis_apply D b j target]
  rw [boundary_inverseClassicalBaseOneBasis D h b]
  exact inverseCheckTransportOne_classicalRootedBoundary_apply
    D h b j target
theorem weightReductionInverse_commutes_boundary2_basis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne) (j : fiberOne) :
    boundary2 (weightReducedData D)
        (weightReductionInverseMap2 D (Pi.single (b, j) 1)) =
      weightReductionInverseMap1 D h
        (boundary2 D (Pi.single (b, j) 1)) := by
  apply funext
  intro target
  cases target with
  | inl qi =>
      exact weightReductionInverse_commutes_boundary2_basis_apply_inl
        D h b j qi
  | inr qj =>
      exact weightReductionInverse_commutes_boundary2_basis_apply_inr
        D h b j qj
theorem weightReductionInverse_commutes_boundary2
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (boundary2 (weightReducedData D)).comp
        (weightReductionInverseMap2 D) =
      (weightReductionInverseMap1 D h).comp (boundary2 D) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro bj
  simpa [LinearMap.comp_apply] using
    weightReductionInverse_commutes_boundary2_basis
      D h bj.1 bj.2
noncomputable def weightReductionInverseChainMap
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    ThreeTermChainMap (chainComplex D)
      (chainComplex (weightReducedData D)) where
  map0 := weightReductionInverseMap0 D h
  map1 := weightReductionInverseMap1 D h
  map2 := weightReductionInverseMap2 D
  commutes_boundary1 := weightReductionInverse_commutes_boundary1 D h
  commutes_boundary2 := weightReductionInverse_commutes_boundary2 D h
noncomputable def horizontalLiftAt (i : fiberZero) :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (fun q => reducedQubitBasisWord D (Sum.inl (q, i)))
@[simp]
theorem horizontalLiftAt_apply_inl
    (i k : fiberZero)
    (x : Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R))
    (q : ClassicalWeightReduction.WeightReducedBit R) :
    horizontalLiftAt D i x (Sum.inl (q, k)) =
      if k = i then x q else 0 := by
  classical
  unfold horizontalLiftAt
    ClassicalWeightReduction.linearMapOfBasisImages reducedQubitBasisWord
  change (∑ q', x q' • Pi.single (Sum.inl (q', i)) 1)
      (Sum.inl (q, k)) = _
  rw [Finset.sum_apply, Fintype.sum_eq_single q]
  · simp [Pi.single_apply, Prod.ext_iff, mul_comm]
  · intro q' hne
    simp [Pi.single_apply, Ne.symm hne]
@[simp]
theorem horizontalLiftAt_apply_inr
    (i : fiberZero)
    (x : Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R))
    (q : ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
    horizontalLiftAt D i x (Sum.inr q) = 0 := by
  classical
  unfold horizontalLiftAt
    ClassicalWeightReduction.linearMapOfBasisImages reducedQubitBasisWord
  simp [Pi.single_apply]
noncomputable def auxiliaryHorizontalLiftAt (i : fiberZero) :
    Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (fun a => reducedQubitBasisWord D (Sum.inl (Sum.inr a, i)))
noncomputable def primaryCheckLiftAt (i : fiberZero) :
    Word (ZMod 2) (ClassicalWeightReduction.Incidence R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (fun e => Pi.single (Sum.inl e, i) 1)
@[simp]
theorem primaryCheckLiftAt_single
    (i : fiberZero) (e : ClassicalWeightReduction.Incidence R) :
    primaryCheckLiftAt D i (Pi.single e 1) =
      Pi.single (Sum.inl e, i) 1 := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
theorem boundary1_auxiliaryHorizontalLiftAt_single
    (i : fiberZero) (a : ClassicalWeightReduction.AuxiliaryBit R) :
    boundary1 (weightReducedData D)
        (auxiliaryHorizontalLiftAt D i (Pi.single a 1)) =
      primaryCheckLiftAt D i
        (ClassicalWeightReduction.bitSplitAuxiliaryBoundary
          (F := ZMod 2) R a) := by
  classical
  rw [show auxiliaryHorizontalLiftAt D i (Pi.single a 1) =
      reducedQubitBasisWord D (Sum.inl (Sum.inr a, i)) by
        exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _]
  ext target
  unfold reducedQubitBasisWord boundary1 primaryCheckLiftAt
    ClassicalWeightReduction.bitSplitAuxiliaryBoundary
    ClassicalWeightReduction.linearMapOfBasisImages
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    weightReducedData, boundary1Matrix, weightReducedConnection,
    FiberAutomorphism.id, ClassicalWeightReduction.basisBoundary,
    ClassicalWeightReduction.auxiliaryBitBoundary, Pi.single_apply]
  rcases target with ⟨q, k⟩
  cases q with
  | inl e =>
      by_cases hki : k = i
      · subst k
        rw [Fintype.sum_eq_single e]
        · simp
        · intro e' hne
          simp [Ne.symm hne]
      · simp [hki]
  | inr a' =>
      simp
noncomputable def embedAuxiliaryBitsLinearMap :
    Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R) →ₗ[ZMod 2]
      Word (ZMod 2) (ClassicalWeightReduction.BitSplitBit R) where
  toFun := ClassicalWeightReduction.embedAuxiliaryBits
    (F := ZMod 2) R
  map_add' x y := by
    ext q
    cases q <;> rfl
  map_smul' coefficient x := by
    ext q
    cases q <;> rfl
noncomputable def auxiliaryPathBoundary :
    Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R) →ₗ[ZMod 2]
      Word (ZMod 2) (ClassicalWeightReduction.Incidence R) :=
  (ClassicalWeightReduction.bitSplitBoundary (F := ZMod 2) R).comp
    (embedAuxiliaryBitsLinearMap D)
@[simp]
theorem auxiliaryPathBoundary_single
    (a : ClassicalWeightReduction.AuxiliaryBit R) :
    auxiliaryPathBoundary D (Pi.single a 1) =
      ClassicalWeightReduction.bitSplitAuxiliaryBoundary
        (F := ZMod 2) R a := by
  classical
  unfold auxiliaryPathBoundary embedAuxiliaryBitsLinearMap
  rw [LinearMap.comp_apply]
  change ClassicalWeightReduction.bitSplitBoundary (F := ZMod 2) R
      (ClassicalWeightReduction.embedAuxiliaryBits (F := ZMod 2) R
        (Pi.single a 1)) = _
  have hembed :
      ClassicalWeightReduction.embedAuxiliaryBits (F := ZMod 2) R
          (Pi.single a 1) =
        Pi.single (Sum.inr a) 1 := by
    ext q
    cases q <;> simp [ClassicalWeightReduction.embedAuxiliaryBits,
      Pi.single_apply]
  rw [hembed, ClassicalWeightReduction.bitSplitBoundary_single]
  rfl
theorem boundary1_comp_auxiliaryHorizontalLiftAt
    (i : fiberZero) :
    (boundary1 (weightReducedData D)).comp
        (auxiliaryHorizontalLiftAt D i) =
      (primaryCheckLiftAt D i).comp (auxiliaryPathBoundary D) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro a
  simp only [LinearMap.comp_apply]
  rw [auxiliaryPathBoundary_single]
  exact boundary1_auxiliaryHorizontalLiftAt_single D i a
theorem auxiliaryPathBoundary_eq_bitSplitBoundary_embed
    (x : Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R)) :
    auxiliaryPathBoundary D x =
      ClassicalWeightReduction.bitSplitBoundary (F := ZMod 2) R
        (ClassicalWeightReduction.embedAuxiliaryBits
          (F := ZMod 2) R x) := by
  rfl
theorem boundary1_auxiliaryCheckPathPrefix
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (i : fiberZero) (e : ClassicalWeightReduction.Incidence R) :
    boundary1 (weightReducedData D)
        (auxiliaryHorizontalLiftAt D i
          (ClassicalWeightReduction.checkPathPrefixWord
            (F := ZMod 2) R e.1.1
            (ClassicalWeightReduction.checkPosition R e))) =
      primaryCheckLiftAt D i
        (Pi.single
            (ClassicalWeightReduction.checkIncidenceAt R e.1.1
              (ClassicalWeightReduction.checkRootPosition R h e.1.1)) 1 +
          Pi.single e 1) := by
  have hchain := LinearMap.congr_fun
    (boundary1_comp_auxiliaryHorizontalLiftAt D i)
    (ClassicalWeightReduction.checkPathPrefixWord
      (F := ZMod 2) R e.1.1
      (ClassicalWeightReduction.checkPosition R e))
  simp only [LinearMap.comp_apply] at hchain
  rw [hchain]
  congr 1
  rw [auxiliaryPathBoundary_eq_bitSplitBoundary_embed D]
  rw [← ClassicalWeightReduction.checkPathAuxiliaryPrefix_eq_embed]
  rw [ClassicalWeightReduction.bitSplitBoundary_checkPathAuxiliaryPrefix
    (F := ZMod 2) R h]
  rw [ClassicalWeightReduction.checkIncidenceAt_checkPosition]
def collapseHomotopyCoordinate
    (q : ClassicalWeightReduction.WeightReducedCheck R)
    (i : fiberZero) (e : ClassicalWeightReduction.Incidence R) : fiberZero :=
  match q with
  | Sum.inl _ => i
  | Sum.inr _ => (D.connection e.1.2 e.1.1).onZero i
noncomputable def weightReductionHomotopy0Basis
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero) :
    Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne) :=
  horizontalLiftAt D i
      (ClassicalWeightReduction.combineHomotopy0Basis
        (F := ZMod 2) R q) +
    ∑ e : ClassicalWeightReduction.Incidence R,
      ClassicalWeightReduction.combineForwardMap0Basis
          (F := ZMod 2) R q e •
        auxiliaryHorizontalLiftAt D
          (collapseHomotopyCoordinate D q i e)
          (ClassicalWeightReduction.checkPathPrefixWord
            (F := ZMod 2) R e.1.1
            (ClassicalWeightReduction.checkPosition R e))
noncomputable def weightReductionHomotopy0 :
    Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberZero) →ₗ[ZMod 2]
      Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (fun qi => weightReductionHomotopy0Basis D qi.1 qi.2)
@[simp]
theorem weightReductionHomotopy0_single
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero) :
    weightReductionHomotopy0 D (Pi.single (q, i) 1) =
      weightReductionHomotopy0Basis D q i := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
theorem weightReductionHomotopy0Basis_primary
    (e : ClassicalWeightReduction.Incidence R) (i : fiberZero) :
    weightReductionHomotopy0Basis D (Sum.inl e) i =
      auxiliaryHorizontalLiftAt D i
        (ClassicalWeightReduction.checkPathPrefixWord
          (F := ZMod 2) R e.1.1
          (ClassicalWeightReduction.checkPosition R e)) := by
  classical
  unfold weightReductionHomotopy0Basis collapseHomotopyCoordinate
    ClassicalWeightReduction.combineHomotopy0Basis
    ClassicalWeightReduction.combineForwardMap0Basis
  simp only [zero_apply, map_zero, zero_add, Pi.single_apply,
    ite_smul, one_smul, zero_smul]
  rw [Fintype.sum_eq_single e]
  · simp
  · intro e' hne
    rw [if_neg hne]
theorem weightReduction_homotopy_degree0_primary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (i : fiberZero) :
    weightReductionInverseMap0 D h
        (weightReductionForwardMap0 D
          (reducedC0BasisWord D (Sum.inl e) i)) -
      reducedC0BasisWord D (Sum.inl e) i =
    boundary1 (weightReducedData D)
      (weightReductionHomotopy0 D
        (reducedC0BasisWord D (Sum.inl e) i)) := by
  classical
  rw [weightReductionForwardMap0_reducedC0BasisWord]
  change weightReductionInverseMap0 D h (Pi.single (e.1.1, i) 1) - _ = _
  rw [weightReductionInverseMap0_single]
  unfold weightReductionInverseBaseZeroBasis
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  unfold reducedC0BasisWord
  rw [weightReductionHomotopy0_single,
    weightReductionHomotopy0Basis_primary]
  rw [boundary1_auxiliaryCheckPathPrefix D h i e]
  rw [map_add, primaryCheckLiftAt_single, primaryCheckLiftAt_single]
theorem inverseTransport_primaryBitSuffix_boundary
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    boundary1 (weightReducedData D)
        (inverseBitTransportZero D b i
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b j)) =
      inverseCheckTransportZero D b i
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b j)) := by
  classical
  unfold inverseBitTransportZero
    ClassicalWeightReduction.boundary
    ClassicalWeightReduction.linearMapOfBasisImages
  change boundary1 (weightReducedData D)
      (∑ q : ClassicalWeightReduction.WeightReducedBit R,
        ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b j q •
          match q with
          | Sum.inl e => Pi.single (Sum.inl (Sum.inl e, i)) 1
          | Sum.inr a => Pi.single
              (Sum.inl (Sum.inr a, (D.connection b a.1).onZero i)) 1) =
    inverseCheckTransportZero D b i
      (∑ q : ClassicalWeightReduction.WeightReducedBit R,
        ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b j q •
          ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q)
  simp only [map_sum, map_smul]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [ClassicalWeightReduction.primaryBitSuffix_auxiliary,
    zero_smul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heb : e.1.2 = b
  · congr 1
    simpa [reducedQubitBasisWord,
      ClassicalWeightReduction.boundary_single] using
      inverseTransport_primary_boundary D b i e heb
  · have hcoeff :
        ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b j (Sum.inl e) = 0 := by
      simp [ClassicalWeightReduction.primaryBitSuffix,
        ClassicalWeightReduction.bitFiberSuffix,
        ClassicalWeightReduction.incidenceBitPosition, heb]
    simp [hcoeff]
theorem horizontalLiftAt_primaryBitSuffix_eq_inverseTransport
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    horizontalLiftAt D i
        (ClassicalWeightReduction.primaryBitSuffix
          (F := ZMod 2) R b j) =
      inverseBitTransportZero D b i
        (ClassicalWeightReduction.primaryBitSuffix
          (F := ZMod 2) R b j) := by
  classical
  unfold horizontalLiftAt inverseBitTransportZero
    ClassicalWeightReduction.linearMapOfBasisImages reducedQubitBasisWord
  ext target
  simp_rw [Fintype.sum_sum_type]
  cases target with
  | inl qi =>
      rcases qi with ⟨q, k⟩
      cases q <;>
        simp [ClassicalWeightReduction.primaryBitSuffix, Pi.single_apply]
  | inr qj =>
      simp [ClassicalWeightReduction.primaryBitSuffix, Pi.single_apply]
noncomputable def transportedBitCheckSuffix
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :=
  ∑ e : ClassicalWeightReduction.Incidence R,
    ClassicalWeightReduction.bitCheckSuffix (F := ZMod 2) R b j e •
      Pi.single
        (Sum.inl e, (D.connection e.1.2 e.1.1).onZero i) 1
noncomputable def rootedBitCheckSuffix
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :=
  ∑ e : ClassicalWeightReduction.Incidence R,
    ClassicalWeightReduction.bitCheckSuffix (F := ZMod 2) R b j e •
      weightReductionInverseBaseZeroBasis D h e.1.1
        ((D.connection e.1.2 e.1.1).onZero i)
theorem inverseCheckTransport_combineInverse_bitCheckSuffix
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    inverseCheckTransportZero D b i
        (ClassicalWeightReduction.combineInverseMap0 (F := ZMod 2) R
          (ClassicalWeightReduction.bitCheckSuffix
            (F := ZMod 2) R b j)) =
      transportedBitCheckSuffix D b j i := by
  classical
  unfold ClassicalWeightReduction.combineInverseMap0
    inverseCheckTransportZero transportedBitCheckSuffix
    ClassicalWeightReduction.linearMapOfBasisImages
  change inverseCheckTransportZero D b i
      (∑ e : ClassicalWeightReduction.Incidence R,
        ClassicalWeightReduction.bitCheckSuffix
            (F := ZMod 2) R b j e • Pi.single (Sum.inl e) 1) = _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heb : e.1.2 = b
  · congr 1
    unfold inverseCheckTransportZero
    rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
    subst b
    rfl
  · have hcoeff :
        ClassicalWeightReduction.bitCheckSuffix
            (F := ZMod 2) R b j e = 0 := by
      simp [ClassicalWeightReduction.bitCheckSuffix, heb]
    simp [hcoeff]
@[simp]
theorem inverseCheckTransportZero_single_auxiliary
    (b : baseOne) (i : fiberZero)
    (a : ClassicalWeightReduction.AuxiliaryCheck R) :
    inverseCheckTransportZero D b i (Pi.single (Sum.inr a) 1) =
      Pi.single (Sum.inr a, i) 1 := by
  classical
  unfold inverseCheckTransportZero
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
theorem boundary1_horizontalLiftAt_primaryBitSuffix
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    boundary1 (weightReducedData D)
        (horizontalLiftAt D i
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b j)) =
      transportedBitCheckSuffix D b j i +
        Pi.single
          ((Sum.inr (⟨b, j⟩ :
              ClassicalWeightReduction.AuxiliaryCheck R) :
              ClassicalWeightReduction.WeightReducedCheck R), i)
          (1 : ZMod 2) := by
  rw [horizontalLiftAt_primaryBitSuffix_eq_inverseTransport]
  rw [inverseTransport_primaryBitSuffix_boundary]
  rw [ClassicalWeightReduction.boundary_primaryBitSuffix]
  rw [map_add, inverseCheckTransport_combineInverse_bitCheckSuffix]
  rw [inverseCheckTransportZero_single_auxiliary]
theorem boundary1_auxiliaryCollapseSuffix
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    boundary1 (weightReducedData D)
        (∑ e : ClassicalWeightReduction.Incidence R,
          ClassicalWeightReduction.bitCheckSuffix
              (F := ZMod 2) R b j e •
            auxiliaryHorizontalLiftAt D
              ((D.connection e.1.2 e.1.1).onZero i)
              (ClassicalWeightReduction.checkPathPrefixWord
                (F := ZMod 2) R e.1.1
                (ClassicalWeightReduction.checkPosition R e))) =
      rootedBitCheckSuffix D h b j i +
        transportedBitCheckSuffix D b j i := by
  classical
  simp only [map_sum, map_smul]
  unfold rootedBitCheckSuffix transportedBitCheckSuffix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  rw [boundary1_auxiliaryCheckPathPrefix D h]
  rw [map_add, primaryCheckLiftAt_single, primaryCheckLiftAt_single]
  rw [smul_add]
  rfl
theorem weightReductionInverseForward_auxiliary_zero
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    weightReductionInverseMap0 D h
        (weightReductionForwardMap0 D
          (reducedC0BasisWord D
            (Sum.inr (⟨b, j⟩ : ClassicalWeightReduction.AuxiliaryCheck R))
            i)) =
      rootedBitCheckSuffix D h b j i := by
  classical
  rw [weightReductionForwardMap0_reducedC0BasisWord]
  unfold weightReductionForwardBaseZeroBasis rootedBitCheckSuffix
    ClassicalWeightReduction.combineForwardMap0Basis
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro e _he
  rw [weightReductionInverseMap0_single]
theorem weightReductionHomotopy0Basis_auxiliary
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    weightReductionHomotopy0Basis D
        (Sum.inr (⟨b, j⟩ : ClassicalWeightReduction.AuxiliaryCheck R)) i =
      horizontalLiftAt D i
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b j) +
        ∑ e : ClassicalWeightReduction.Incidence R,
          ClassicalWeightReduction.bitCheckSuffix
              (F := ZMod 2) R b j e •
            auxiliaryHorizontalLiftAt D
              ((D.connection e.1.2 e.1.1).onZero i)
              (ClassicalWeightReduction.checkPathPrefixWord
                (F := ZMod 2) R e.1.1
                (ClassicalWeightReduction.checkPosition R e)) := by
  rfl
theorem weightReduction_homotopy_degree0_auxiliary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (j : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    weightReductionInverseMap0 D h
        (weightReductionForwardMap0 D
          (reducedC0BasisWord D
            (Sum.inr (⟨b, j⟩ : ClassicalWeightReduction.AuxiliaryCheck R))
            i)) -
      reducedC0BasisWord D
        (Sum.inr (⟨b, j⟩ : ClassicalWeightReduction.AuxiliaryCheck R)) i =
    boundary1 (weightReducedData D)
      (weightReductionHomotopy0 D
        (reducedC0BasisWord D
          (Sum.inr (⟨b, j⟩ : ClassicalWeightReduction.AuxiliaryCheck R))
          i)) := by
  classical
  rw [weightReductionInverseForward_auxiliary_zero]
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  unfold reducedC0BasisWord
  rw [weightReductionHomotopy0_single,
    weightReductionHomotopy0Basis_auxiliary]
  rw [map_add, boundary1_horizontalLiftAt_primaryBitSuffix,
    boundary1_auxiliaryCollapseSuffix]
  let transported := transportedBitCheckSuffix D b j i
  let rooted := rootedBitCheckSuffix D h b j i
  let auxiliary :
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :=
    Pi.single
      ((Sum.inr (⟨b, j⟩ : ClassicalWeightReduction.AuxiliaryCheck R) :
          ClassicalWeightReduction.WeightReducedCheck R), i) 1
  change rooted + auxiliary = (transported + auxiliary) + (rooted + transported)
  calc
    rooted + auxiliary =
        (rooted + auxiliary) + (transported + transported) := by
      rw [ClassicalWeightReduction.word_add_self_eq_zero_of_char_two,
        add_zero]
    _ = (transported + auxiliary) + (rooted + transported) := by
      ac_rfl
theorem weightReduction_homotopy_degree0
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (weightReductionInverseMap0 D h).comp
          (weightReductionForwardMap0 D) - LinearMap.id =
      (boundary1 (weightReducedData D)).comp
        (weightReductionHomotopy0 D) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro qi
  rcases qi with ⟨q, i⟩
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  cases q with
  | inl e =>
      simpa [reducedC0BasisWord] using
        weightReduction_homotopy_degree0_primary D h e i
  | inr a =>
      rcases a with ⟨b, j⟩
      simpa [reducedC0BasisWord] using
        weightReduction_homotopy_degree0_auxiliary D h b j i
noncomputable def degreeTwoLiftAt (j : fiberOne) :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedBit R × fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (fun q => reducedC2BasisWord D q j)
@[simp]
theorem degreeTwoLiftAt_single
    (j : fiberOne) (q : ClassicalWeightReduction.WeightReducedBit R) :
    degreeTwoLiftAt D j (Pi.single q 1) =
      reducedC2BasisWord D q j := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
noncomputable def auxiliaryDegreeTwoLiftAt (j : fiberOne) :
    Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedBit R × fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (fun a => reducedC2BasisWord D (Sum.inr a) j)
@[simp]
theorem auxiliaryDegreeTwoLiftAt_single
    (j : fiberOne) (a : ClassicalWeightReduction.AuxiliaryBit R) :
    auxiliaryDegreeTwoLiftAt D j (Pi.single a 1) =
      reducedC2BasisWord D (Sum.inr a) j := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
def collapseHomotopyCoordinateOne
    (q : ClassicalWeightReduction.WeightReducedCheck R)
    (j : fiberOne) (e : ClassicalWeightReduction.Incidence R) : fiberOne :=
  match q with
  | Sum.inl _ => j
  | Sum.inr _ => (D.connection e.1.2 e.1.1).onOne j
noncomputable def weightReductionHomotopy1Basis :
    QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne →
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedBit R × fiberOne)
  | Sum.inl _ => 0
  | Sum.inr (q, j) =>
      degreeTwoLiftAt D j
          (ClassicalWeightReduction.combineHomotopy0Basis
            (F := ZMod 2) R q) +
        ∑ e : ClassicalWeightReduction.Incidence R,
          ClassicalWeightReduction.combineForwardMap0Basis
              (F := ZMod 2) R q e •
            auxiliaryDegreeTwoLiftAt D
              (collapseHomotopyCoordinateOne D q j e)
              (ClassicalWeightReduction.checkPathPrefixWord
                (F := ZMod 2) R e.1.1
                (ClassicalWeightReduction.checkPosition R e))
noncomputable def weightReductionHomotopy1 :
    Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedBit R × fiberOne) :=
  by
    classical
    exact ClassicalWeightReduction.linearMapOfBasisImages
      (weightReductionHomotopy1Basis D)
@[simp]
theorem weightReductionHomotopy1_single
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    weightReductionHomotopy1 D (reducedQubitBasisWord D q) =
      weightReductionHomotopy1Basis D q := by
  classical
  unfold reducedQubitBasisWord
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
@[simp]
theorem weightReductionHomotopy1Basis_horizontal
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    weightReductionHomotopy1Basis D (Sum.inl (q, i)) = 0 := by
  rfl
theorem weightReductionHomotopy1Basis_vertical_primary
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    weightReductionHomotopy1Basis D (Sum.inr (Sum.inl e, j)) =
      auxiliaryDegreeTwoLiftAt D j
        (ClassicalWeightReduction.checkPathPrefixWord
          (F := ZMod 2) R e.1.1
          (ClassicalWeightReduction.checkPosition R e)) := by
  classical
  unfold weightReductionHomotopy1Basis collapseHomotopyCoordinateOne
    ClassicalWeightReduction.combineHomotopy0Basis
    ClassicalWeightReduction.combineForwardMap0Basis
  simp only [map_zero, zero_add, Pi.single_apply, ite_smul, one_smul,
    zero_smul]
  rw [Fintype.sum_eq_single e]
  · simp
  · intro e' hne
    rw [if_neg hne]
theorem weightReductionHomotopy1Basis_vertical_auxiliary
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    weightReductionHomotopy1Basis D
        (Sum.inr
          (Sum.inr
            (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R), j)) =
      degreeTwoLiftAt D j
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k) +
        ∑ e : ClassicalWeightReduction.Incidence R,
          ClassicalWeightReduction.bitCheckSuffix
              (F := ZMod 2) R b k e •
            auxiliaryDegreeTwoLiftAt D
              ((D.connection e.1.2 e.1.1).onOne j)
              (ClassicalWeightReduction.checkPathPrefixWord
                (F := ZMod 2) R e.1.1
                (ClassicalWeightReduction.checkPosition R e)) := by
  rfl
noncomputable def twistedHomotopyBoundaryOne
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedBit R × fiberOne) :=
  ∑ a : ClassicalWeightReduction.WeightReducedCheck R,
    ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q a •
      weightReductionHomotopy1Basis D
        (Sum.inr (a, (weightReducedConnection D q a).onOne j))
theorem weightReductionHomotopy1_boundary2_basis
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne) :
    weightReductionHomotopy1 D
        (boundary2 (weightReducedData D) (reducedC2BasisWord D q j)) =
      twistedHomotopyBoundaryOne D q j := by
  classical
  unfold weightReductionHomotopy1
    ClassicalWeightReduction.linearMapOfBasisImages
    twistedHomotopyBoundaryOne
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have hinl (qi :
      ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
      boundary2 (weightReducedData D) (reducedC2BasisWord D q j)
          (Sum.inl qi) =
        if qi.1 = q then D.fiberBoundary qi.2 j else 0 := by
    exact boundary2_reducedC2BasisWord_apply_inl D q j qi.1 qi.2
  have hinr (aj :
      ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
      boundary2 (weightReducedData D) (reducedC2BasisWord D q j)
          (Sum.inr aj) =
        if aj.2 = (weightReducedConnection D q aj.1).onOne j then
          ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q aj.1
        else 0 := by
    exact boundary2_reducedC2BasisWord_apply_inr D q j aj.1 aj.2
  have hhorizontal (qi :
      ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
      weightReductionHomotopy1Basis D (Sum.inl qi) = 0 := by
    rcases qi with ⟨q', i⟩
    exact weightReductionHomotopy1Basis_horizontal D q' i
  rw [Fintype.sum_sum_type]
  simp_rw [hinl]
  simp_rw [hinr]
  simp only [hhorizontal, smul_zero,
    Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Fintype.sum_eq_single ((weightReducedConnection D q a).onOne j)]
  · simp
  · intro j' hne
    rw [if_neg hne, zero_smul]
theorem weightReductionInverseForwardMap2_basis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (j : fiberOne) :
    weightReductionInverseMap2 D
        (weightReductionForwardMap2 D h
          (reducedC2BasisWord D q j)) =
      match q with
      | Sum.inl e =>
          if ClassicalWeightReduction.bitPosition R e =
              ClassicalWeightReduction.bitRootPosition R h e.1.2 then
            weightReductionInverseBaseOneOneBasis D e.1.2 j
          else 0
      | Sum.inr _ => 0 := by
  rw [weightReductionForwardMap2_reducedC2BasisWord]
  cases q with
  | inl e =>
      by_cases hroot : ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2
      · simp [weightReductionForwardBaseOneOneBasis, hroot,
          weightReductionInverseMap2_single]
      · simp [weightReductionForwardBaseOneOneBasis, hroot]
  | inr a =>
      simp [weightReductionForwardBaseOneOneBasis]
theorem twistedHomotopyBoundaryOne_auxiliary
    (a : ClassicalWeightReduction.AuxiliaryBit R) (j : fiberOne) :
    twistedHomotopyBoundaryOne D (Sum.inr a) j =
      reducedC2BasisWord D (Sum.inr a) j := by
  classical
  rcases a with ⟨c, k⟩
  unfold twistedHomotopyBoundaryOne
    ClassicalWeightReduction.basisBoundary
    ClassicalWeightReduction.auxiliaryBitBoundary
  simp only [Pi.add_apply, Finset.sum_add_distrib, add_smul]
  simp [weightReducedConnection,
    weightReductionHomotopy1Basis_vertical_primary,
    ClassicalWeightReduction.checkPosition_checkIncidenceAt]
  change auxiliaryDegreeTwoLiftAt D j
        (ClassicalWeightReduction.checkPathPrefixWord
          (F := ZMod 2) R c (ClassicalWeightReduction.pathLeft k)) +
      auxiliaryDegreeTwoLiftAt D j
        (ClassicalWeightReduction.checkPathPrefixWord
          (F := ZMod 2) R c (ClassicalWeightReduction.pathRight k)) = _
  rw [← map_add]
  have hprefix :
      ClassicalWeightReduction.checkPathPrefixWord
            (F := ZMod 2) R c (ClassicalWeightReduction.pathLeft k) +
          ClassicalWeightReduction.checkPathPrefixWord
            (F := ZMod 2) R c (ClassicalWeightReduction.pathRight k) =
        Pi.single
          (⟨c, k⟩ : ClassicalWeightReduction.AuxiliaryBit R) 1 := by
    ext a
    have hfull := congrFun
      (ClassicalWeightReduction.checkPathAuxiliaryPrefix_left_add_right
        (F := ZMod 2) R c k) (Sum.inr a)
    change
      ClassicalWeightReduction.checkPathPrefixWord
            (F := ZMod 2) R c (ClassicalWeightReduction.pathLeft k) a +
          ClassicalWeightReduction.checkPathPrefixWord
            (F := ZMod 2) R c (ClassicalWeightReduction.pathRight k) a =
        (Pi.single
          (⟨c, k⟩ : ClassicalWeightReduction.AuxiliaryBit R)
          (1 : ZMod 2) :
            Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R)) a
    convert hfull using 1 <;>
      simp [ClassicalWeightReduction.checkPathAuxiliaryPrefix,
        ClassicalWeightReduction.checkPathPrefixWord, Pi.single_apply]
  rw [hprefix, auxiliaryDegreeTwoLiftAt_single]
theorem weightReduction_homotopy_degree2_auxiliary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (j : fiberOne) :
    weightReductionInverseMap2 D
        (weightReductionForwardMap2 D h
          (reducedC2BasisWord D (Sum.inr a) j)) -
      reducedC2BasisWord D (Sum.inr a) j =
    weightReductionHomotopy1 D
      (boundary2 (weightReducedData D)
        (reducedC2BasisWord D (Sum.inr a) j)) := by
  rw [weightReductionInverseForwardMap2_basis]
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two, zero_add]
  rw [weightReductionHomotopy1_boundary2_basis]
  exact (twistedHomotopyBoundaryOne_auxiliary D a j).symm
noncomputable def classicalCompositeHomotopyBasis
    (q : ClassicalWeightReduction.WeightReducedCheck R) :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R) :=
  ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
      (ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R
        (ClassicalWeightReduction.combineForwardMap0Basis
          (F := ZMod 2) R q)) +
    ClassicalWeightReduction.combineHomotopy0Basis (F := ZMod 2) R q
noncomputable def classicalCompositeHomotopy :
    Word (ZMod 2) (ClassicalWeightReduction.WeightReducedCheck R) →ₗ[ZMod 2]
      Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R) :=
  (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R).comp
      ((ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R).comp
        (ClassicalWeightReduction.combineForwardMap0 (F := ZMod 2) R)) +
    ClassicalWeightReduction.combineHomotopy0 (F := ZMod 2) R
@[simp]
theorem classicalCompositeHomotopy_single
    (q : ClassicalWeightReduction.WeightReducedCheck R) :
    classicalCompositeHomotopy D (Pi.single q 1) =
      classicalCompositeHomotopyBasis D q := by
  classical
  unfold classicalCompositeHomotopy classicalCompositeHomotopyBasis
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    ClassicalWeightReduction.combineForwardMap0_single,
    ClassicalWeightReduction.combineHomotopy0_single]
theorem classicalCompositeHomotopy_degree1
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    ((ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R).comp
        (ClassicalWeightReduction.collapseInverseMap1 (F := ZMod 2) R)).comp
          ((ClassicalWeightReduction.collapseForwardMap1 (F := ZMod 2) R).comp
            (ClassicalWeightReduction.combineForwardMap1
              (F := ZMod 2) R h)) - LinearMap.id =
      (classicalCompositeHomotopy D).comp
        (ClassicalWeightReduction.boundary (F := ZMod 2) R) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply]
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  let y := ClassicalWeightReduction.combineForwardMap1
    (F := ZMod 2) R h x
  let u := ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R y
  let z := ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R
    (ClassicalWeightReduction.bitSplitBoundary (F := ZMod 2) R y)
  have hc := LinearMap.congr_fun
    (ClassicalWeightReduction.collapseInverseForward_homotopy_degree1
      (F := ZMod 2) R) y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hc
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two] at hc
  have hcmap := congrArg
    (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R) hc
  simp only [map_add] at hcmap
  have hb := LinearMap.congr_fun
    (ClassicalWeightReduction.combineInverseForward_homotopy_degree1
      (F := ZMod 2) R h) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hb
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two] at hb
  have hforward := LinearMap.congr_fun
    (ClassicalWeightReduction.combineForward_commutes_boundary
      (F := ZMod 2) R h) x
  simp only [LinearMap.comp_apply] at hforward
  have hdouble : u + u = 0 :=
    ClassicalWeightReduction.word_add_self_eq_zero_of_char_two
      (F := ZMod 2) u
  change ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
          (ClassicalWeightReduction.collapseInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseForwardMap1
              (F := ZMod 2) R y)) + x =
    ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
        (ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R
          (ClassicalWeightReduction.combineForwardMap0 (F := ZMod 2) R
            (ClassicalWeightReduction.boundary (F := ZMod 2) R x))) +
      ClassicalWeightReduction.combineHomotopy0 (F := ZMod 2) R
        (ClassicalWeightReduction.boundary (F := ZMod 2) R x)
  calc
    _ = (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseInverseMap1 (F := ZMod 2) R
              (ClassicalWeightReduction.collapseForwardMap1
                (F := ZMod 2) R y)) + x) + 0 := by simp
    _ = (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseInverseMap1 (F := ZMod 2) R
              (ClassicalWeightReduction.collapseForwardMap1
                (F := ZMod 2) R y)) + x) + (u + u) := by rw [hdouble]
    _ = (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseInverseMap1 (F := ZMod 2) R
              (ClassicalWeightReduction.collapseForwardMap1
                (F := ZMod 2) R y)) + u) + (u + x) := by abel
    _ = ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R z +
          ClassicalWeightReduction.combineHomotopy0 (F := ZMod 2) R
            (ClassicalWeightReduction.boundary (F := ZMod 2) R x) := by
      rw [← hcmap, ← hb]
    _ = _ := by rw [← hforward]
theorem weightReductionHomotopy1Basis_primary_eq_transport
    (b : baseOne) (e : ClassicalWeightReduction.Incidence R)
    (j : fiberOne) :
    weightReductionHomotopy1Basis D
        (Sum.inr
          (Sum.inl e, (D.connection b e.1.1).onOne j)) =
      inverseBitTransportOne D b j
        (classicalCompositeHomotopyBasis D (Sum.inl e)) := by
  classical
  unfold classicalCompositeHomotopyBasis
    weightReductionHomotopy1Basis collapseHomotopyCoordinateOne
    ClassicalWeightReduction.combineForwardMap0Basis
    ClassicalWeightReduction.combineHomotopy0Basis
  simp only [map_zero, add_zero]
  rw [ClassicalWeightReduction.collapseHomotopy0_single]
  unfold ClassicalWeightReduction.collapseHomotopy0Basis
  have hconnection (c : ClassicalWeightReduction.AuxiliaryBit R) :
      (if c.1 = e.1.1 ∧
          c.2.1 < (ClassicalWeightReduction.checkPosition R e).1 then
        (Pi.single
          (Sum.inr c, (D.connection b e.1.1).onOne j) (1 : ZMod 2) :
            Word (ZMod 2)
              (ClassicalWeightReduction.WeightReducedBit R × fiberOne))
      else 0) =
      (if c.1 = e.1.1 ∧
          c.2.1 < (ClassicalWeightReduction.checkPosition R e).1 then
        (Pi.single
          (Sum.inr c, (D.connection b c.1).onOne j) (1 : ZMod 2) :
            Word (ZMod 2)
              (ClassicalWeightReduction.WeightReducedBit R × fiberOne))
      else 0) := by
    by_cases hs : c.1 = e.1.1 ∧
        c.2.1 < (ClassicalWeightReduction.checkPosition R e).1
    · rw [if_pos hs, if_pos hs, hs.1]
    · rw [if_neg hs, if_neg hs]
  ext target
  cases target with
  | mk q k =>
      cases q <;>
        simp [auxiliaryDegreeTwoLiftAt, inverseBitTransportOne,
          ClassicalWeightReduction.combineInverseMap1,
          ClassicalWeightReduction.combineInverseMap1Basis,
          ClassicalWeightReduction.checkPathAuxiliaryPrefix,
          ClassicalWeightReduction.checkPathPrefixWord,
          ClassicalWeightReduction.linearMapOfBasisImages,
          reducedC2BasisWord, Pi.single_apply, Prod.ext_iff,
          Sum.inl.injEq, Sum.inr.injEq, apply_ite] <;>
        apply Finset.sum_congr rfl <;>
        intro c _hc <;>
        exact congrFun (hconnection c) _
theorem weightReductionHomotopy1Basis_auxiliary_eq_transport
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    weightReductionHomotopy1Basis D
        (Sum.inr
          (Sum.inr
            (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R), j)) =
      inverseBitTransportOne D b j
        (classicalCompositeHomotopyBasis D
          (Sum.inr
            (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R))) := by
  classical
  unfold classicalCompositeHomotopyBasis
    weightReductionHomotopy1Basis collapseHomotopyCoordinateOne
    ClassicalWeightReduction.combineForwardMap0Basis
    ClassicalWeightReduction.combineHomotopy0Basis
  rw [map_add]
  have hcollapse :
      (∑ e : ClassicalWeightReduction.Incidence R,
        ClassicalWeightReduction.bitCheckSuffix
            (F := ZMod 2) R b k e •
          auxiliaryDegreeTwoLiftAt D
            ((D.connection e.1.2 e.1.1).onOne j)
            (ClassicalWeightReduction.checkPathPrefixWord
              (F := ZMod 2) R e.1.1
              (ClassicalWeightReduction.checkPosition R e))) =
        inverseBitTransportOne D b j
          (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R
              (ClassicalWeightReduction.bitCheckSuffix
                (F := ZMod 2) R b k))) := by
    unfold ClassicalWeightReduction.collapseHomotopy0
      ClassicalWeightReduction.linearMapOfBasisImages
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases heb : e.1.2 = b
    · subst b
      congr 1
      simpa [classicalCompositeHomotopyBasis,
        ClassicalWeightReduction.combineForwardMap0Basis,
        ClassicalWeightReduction.combineHomotopy0Basis,
        weightReductionHomotopy1Basis_vertical_primary] using
        weightReductionHomotopy1Basis_primary_eq_transport D e.1.2 e j
    · have hcoeff :
          ClassicalWeightReduction.bitCheckSuffix
              (F := ZMod 2) R b k e = 0 := by
        simp [ClassicalWeightReduction.bitCheckSuffix, heb]
      simp [hcoeff]
  have hprimary :
      degreeTwoLiftAt D j
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k) =
        inverseBitTransportOne D b j
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k) := by
    ext target
    cases target with
    | mk q j' =>
        cases q <;>
          simp [degreeTwoLiftAt, inverseBitTransportOne,
            ClassicalWeightReduction.primaryBitSuffix,
            ClassicalWeightReduction.linearMapOfBasisImages,
            reducedC2BasisWord, Pi.single_apply]
  change degreeTwoLiftAt D j
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k) +
        (∑ e : ClassicalWeightReduction.Incidence R,
          ClassicalWeightReduction.bitCheckSuffix
              (F := ZMod 2) R b k e •
            auxiliaryDegreeTwoLiftAt D
              ((D.connection e.1.2 e.1.1).onOne j)
              (ClassicalWeightReduction.checkPathPrefixWord
                (F := ZMod 2) R e.1.1
                (ClassicalWeightReduction.checkPosition R e))) =
      inverseBitTransportOne D b j
          (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R
              (ClassicalWeightReduction.bitCheckSuffix
                (F := ZMod 2) R b k))) +
        inverseBitTransportOne D b j
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k)
  rw [hcollapse, hprimary, add_comm]
theorem primaryBoundary_homotopy_term_eq_transport
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne)
    (a : ClassicalWeightReduction.WeightReducedCheck R) :
    ClassicalWeightReduction.basisBoundary
          (F := ZMod 2) R (Sum.inl e) a •
        weightReductionHomotopy1Basis D
          (Sum.inr
            (a, (weightReducedConnection D (Sum.inl e) a).onOne j)) =
      ClassicalWeightReduction.basisBoundary
          (F := ZMod 2) R (Sum.inl e) a •
        inverseBitTransportOne D e.1.2 j
          (classicalCompositeHomotopyBasis D a) := by
  classical
  cases a with
  | inl x =>
      by_cases hxe : x = e
      · subst x
        simp [ClassicalWeightReduction.basisBoundary,
          ClassicalWeightReduction.primaryBitBoundary,
          weightReducedConnection,
          weightReductionHomotopy1Basis_primary_eq_transport]
      · have hcoeff :
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inl e) (Sum.inl x) = 0 := by
          simp [ClassicalWeightReduction.basisBoundary,
            ClassicalWeightReduction.primaryBitBoundary, hxe]
        simp [hcoeff]
  | inr a =>
      rcases a with ⟨b, k⟩
      by_cases hbe : b = e.1.2
      · subst b
        exact congrArg
          (fun w =>
            ClassicalWeightReduction.basisBoundary
                (F := ZMod 2) R (Sum.inl e)
                  (Sum.inr
                    (⟨e.1.2, k⟩ :
                      ClassicalWeightReduction.AuxiliaryCheck R)) • w)
          (weightReductionHomotopy1Basis_auxiliary_eq_transport
            D e.1.2 k j)
      · have hcoeff :
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inl e)
              (Sum.inr
                (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R)) = 0 := by
          unfold ClassicalWeightReduction.basisBoundary
            ClassicalWeightReduction.primaryBitBoundary
          simp only [Pi.add_apply, Pi.single_apply, Sum.inl_ne_inr,
            if_false, zero_add]
          rw [ClassicalWeightReduction.optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
            (F := ZMod 2) R (Ne.symm hbe)
            (ClassicalWeightReduction.pathPrevious
              (ClassicalWeightReduction.bitPosition R e)) k]
          rw [ClassicalWeightReduction.optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
            (F := ZMod 2) R (Ne.symm hbe)
            (ClassicalWeightReduction.pathNext
              (ClassicalWeightReduction.bitPosition R e)) k]
          rfl
        simp [hcoeff]
theorem twistedHomotopyBoundaryOne_primary_eq_transport
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    twistedHomotopyBoundaryOne D (Sum.inl e) j =
      inverseBitTransportOne D e.1.2 j
        (∑ a : ClassicalWeightReduction.WeightReducedCheck R,
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inl e) a •
            classicalCompositeHomotopyBasis D a) := by
  classical
  unfold twistedHomotopyBoundaryOne
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro a _ha
  exact primaryBoundary_homotopy_term_eq_transport D e j a
theorem classicalCompositeHomotopy_boundary_basis
    (q : ClassicalWeightReduction.WeightReducedBit R) :
    (∑ a : ClassicalWeightReduction.WeightReducedCheck R,
      ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q a •
        classicalCompositeHomotopyBasis D a) =
      classicalCompositeHomotopy D
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (Pi.single q 1)) := by
  classical
  rw [ClassicalWeightReduction.boundary_single]
  have hexpand :
      ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q =
        ∑ a : ClassicalWeightReduction.WeightReducedCheck R,
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R q a • Pi.single a 1 := by
    ext a
    simp [Pi.single_apply]
  conv_rhs => rw [hexpand]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [map_smul, classicalCompositeHomotopy_single]
theorem classicalCompositeHomotopy_primary_boundary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) :
    (∑ a : ClassicalWeightReduction.WeightReducedCheck R,
      ClassicalWeightReduction.basisBoundary
          (F := ZMod 2) R (Sum.inl e) a •
        classicalCompositeHomotopyBasis D a) =
      (if ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2 then
        inverseClassicalBaseOneBasis D e.1.2
      else 0) + Pi.single (Sum.inl e) 1 := by
  rw [classicalCompositeHomotopy_boundary_basis]
  have hdegree := LinearMap.congr_fun
    (classicalCompositeHomotopy_degree1 D h)
    (Pi.single (Sum.inl e) 1)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hdegree
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two] at hdegree
  rw [ClassicalWeightReduction.combineForwardMap1_single] at hdegree
  simp only [ClassicalWeightReduction.combineForwardMap1Basis] at hdegree
  by_cases hroot : ClassicalWeightReduction.bitPosition R e =
      ClassicalWeightReduction.bitRootPosition R h e.1.2
  · rw [if_pos hroot] at hdegree
    rw [ClassicalWeightReduction.collapseForwardMap1_single] at hdegree
    unfold ClassicalWeightReduction.collapseForwardMap1Basis at hdegree
    rw [← inverseClassicalBaseOneBasis_eq_composedInverse D] at hdegree
    simpa [hroot] using hdegree.symm
  · rw [if_neg hroot, map_zero, map_zero] at hdegree
    simpa [hroot] using hdegree.symm
@[simp]
theorem inverseBitTransportOne_single_primary
    (b : baseOne) (j : fiberOne)
    (e : ClassicalWeightReduction.Incidence R) :
    inverseBitTransportOne D b j (Pi.single (Sum.inl e) 1) =
      reducedC2BasisWord D (Sum.inl e) j := by
  classical
  unfold inverseBitTransportOne reducedC2BasisWord
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
theorem twistedHomotopyBoundaryOne_primary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    twistedHomotopyBoundaryOne D (Sum.inl e) j =
      (if ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2 then
        weightReductionInverseBaseOneOneBasis D e.1.2 j
      else 0) +
        reducedC2BasisWord D (Sum.inl e) j := by
  rw [twistedHomotopyBoundaryOne_primary_eq_transport]
  rw [classicalCompositeHomotopy_primary_boundary D h e]
  rw [map_add, inverseBitTransportOne_single_primary]
  by_cases hroot : ClassicalWeightReduction.bitPosition R e =
      ClassicalWeightReduction.bitRootPosition R h e.1.2
  · rw [if_pos hroot, if_pos hroot]
    exact congrArg
      (fun w => w + reducedC2BasisWord D (Sum.inl e) j)
      (inverseBitTransportOne_classicalBasis D e.1.2 j)
  · rw [if_neg hroot, if_neg hroot, map_zero]
theorem weightReduction_homotopy_degree2_primary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    weightReductionInverseMap2 D
        (weightReductionForwardMap2 D h
          (reducedC2BasisWord D (Sum.inl e) j)) -
      reducedC2BasisWord D (Sum.inl e) j =
    weightReductionHomotopy1 D
      (boundary2 (weightReducedData D)
        (reducedC2BasisWord D (Sum.inl e) j)) := by
  rw [weightReductionInverseForwardMap2_basis]
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  rw [weightReductionHomotopy1_boundary2_basis]
  exact (twistedHomotopyBoundaryOne_primary D h e j).symm
theorem weightReduction_homotopy_degree2
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (weightReductionInverseMap2 D).comp
          (weightReductionForwardMap2 D h) - LinearMap.id =
      (weightReductionHomotopy1 D).comp
        (boundary2 (weightReducedData D)) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro qj
  rcases qj with ⟨q, j⟩
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  cases q with
  | inl e =>
      simpa [reducedC2BasisWord] using
        weightReduction_homotopy_degree2_primary D h e j
  | inr a =>
      simpa [reducedC2BasisWord] using
        weightReduction_homotopy_degree2_auxiliary D h a j
noncomputable def twistedHomotopyBoundaryZero
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne) :=
  ∑ a : ClassicalWeightReduction.WeightReducedCheck R,
    ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q a •
      weightReductionHomotopy0Basis D a
        ((weightReducedConnection D q a).onZero i)
theorem weightReductionHomotopy0_boundary1_horizontal_basis
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    weightReductionHomotopy0 D
        (boundary1 (weightReducedData D)
          (reducedQubitBasisWord D (Sum.inl (q, i)))) =
      twistedHomotopyBoundaryZero D q i := by
  letI : DecidableEq
      (ClassicalWeightReduction.WeightReducedCheck R) := inferInstance
  letI : DecidableEq
      (ClassicalWeightReduction.WeightReducedBit R) := inferInstance
  letI : DecidableEq
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne) := inferInstance
  classical
  have hboundary (ai :
      ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :
      boundary1 (weightReducedData D)
          (reducedQubitBasisWord D (Sum.inl (q, i))) ai =
        if ai.2 = (weightReducedConnection D q ai.1).onZero i then
          ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q ai.1
        else 0 := by
    unfold reducedQubitBasisWord boundary1
    rw [Matrix.toLin'_apply]
    unfold Matrix.mulVec dotProduct
    rw [Fintype.sum_eq_single (Sum.inl (q, i))]
    · simp [boundary1Matrix, weightReducedData] <;> rfl
    · intro target hne
      simp [Pi.single_apply, hne]
  unfold weightReductionHomotopy0
    ClassicalWeightReduction.linearMapOfBasisImages
    twistedHomotopyBoundaryZero
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Fintype.sum_eq_single ((weightReducedConnection D q a).onZero i)]
  · rw [hboundary, if_pos rfl]
  · intro i' hne
    rw [hboundary, if_neg hne, zero_smul]
theorem weightReductionInverseForwardMap1_horizontal_basis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    weightReductionInverseMap1 D h
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D (Sum.inl (q, i)))) =
      match q with
      | Sum.inl e =>
          if ClassicalWeightReduction.bitPosition R e =
              ClassicalWeightReduction.bitRootPosition R h e.1.2 then
            fun target =>
              match target with
              | Sum.inl target' =>
                  weightReductionInverseBaseOneBasis D e.1.2 i target'
              | Sum.inr _ => 0
          else 0
      | Sum.inr _ => 0 := by
  rw [weightReductionForwardMap1_reducedQubitBasisWord_inl]
  cases q with
  | inl e =>
      by_cases hroot : ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2
      · simp only [weightReductionForwardBaseOneBasis, hroot, if_pos]
        have hsingle :
            (fun target : QubitIndex baseZero baseOne fiberZero fiberOne =>
              match target with
              | Sum.inl target' =>
                  (Pi.single (e.1.2, i) (1 : ZMod 2) :
                    Word (ZMod 2) (baseOne × fiberZero)) target'
              | Sum.inr _ => 0) =
              Pi.single (Sum.inl (e.1.2, i)) 1 := by
            ext target
            cases target <;> simp [Pi.single_apply]
        rw [hsingle, weightReductionInverseMap1_single_inl]
      · simp [weightReductionForwardBaseOneBasis, hroot]
  | inr a =>
      simp [weightReductionForwardBaseOneBasis]
theorem weightReductionHomotopy0Basis_primary_eq_transport
    (b : baseOne) (e : ClassicalWeightReduction.Incidence R)
    (i : fiberZero) :
    weightReductionHomotopy0Basis D (Sum.inl e)
        ((D.connection b e.1.1).onZero i) =
      inverseBitTransportZero D b i
        (classicalCompositeHomotopyBasis D (Sum.inl e)) := by
  classical
  change
    horizontalLiftAt D ((D.connection b e.1.1).onZero i)
        (ClassicalWeightReduction.combineHomotopy0Basis
          (F := ZMod 2) R (Sum.inl e)) +
      ∑ e' : ClassicalWeightReduction.Incidence R,
        ClassicalWeightReduction.combineForwardMap0Basis
            (F := ZMod 2) R (Sum.inl e) e' •
          auxiliaryHorizontalLiftAt D
            ((D.connection b e.1.1).onZero i)
            (ClassicalWeightReduction.checkPathPrefixWord
              (F := ZMod 2) R e'.1.1
              (ClassicalWeightReduction.checkPosition R e')) = _
  simp only [
    ClassicalWeightReduction.combineHomotopy0Basis,
    ClassicalWeightReduction.combineForwardMap0Basis,
    zero_apply, map_zero, zero_add, Pi.single_apply,
    ite_smul, one_smul, zero_smul]
  rw [Fintype.sum_eq_single e]
  swap
  · intro e' hne
    rw [if_neg hne]
  simp only [classicalCompositeHomotopyBasis,
    ClassicalWeightReduction.combineForwardMap0Basis,
    ClassicalWeightReduction.combineHomotopy0Basis,
    map_zero, add_zero]
  rw [ClassicalWeightReduction.collapseHomotopy0_single]
  simp only [ClassicalWeightReduction.collapseHomotopy0Basis]
  have hconnection (c : ClassicalWeightReduction.AuxiliaryBit R) :
      (if c.1 = e.1.1 ∧
          c.2.1 < (ClassicalWeightReduction.checkPosition R e).1 then
        (Pi.single
          (Sum.inl
            (Sum.inr c, (D.connection b e.1.1).onZero i)) (1 : ZMod 2) :
            Word (ZMod 2)
              (QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))
      else 0) =
      (if c.1 = e.1.1 ∧
          c.2.1 < (ClassicalWeightReduction.checkPosition R e).1 then
        (Pi.single
          (Sum.inl
            (Sum.inr c, (D.connection b c.1).onZero i)) (1 : ZMod 2) :
            Word (ZMod 2)
              (QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))
      else 0) := by
    by_cases hs : c.1 = e.1.1 ∧
        c.2.1 < (ClassicalWeightReduction.checkPosition R e).1
    · rw [if_pos hs, if_pos hs, hs.1]
    · rw [if_neg hs, if_neg hs]
  ext target
  cases target with
  | inl qi =>
      rcases qi with ⟨q, k⟩
      cases q <;>
        simp [auxiliaryHorizontalLiftAt, inverseBitTransportZero,
          ClassicalWeightReduction.combineInverseMap1,
          ClassicalWeightReduction.combineInverseMap1Basis,
          ClassicalWeightReduction.checkPathAuxiliaryPrefix,
          ClassicalWeightReduction.checkPathPrefixWord,
          ClassicalWeightReduction.linearMapOfBasisImages,
          reducedQubitBasisWord, Pi.single_apply, apply_ite] <;>
        apply Finset.sum_congr rfl <;>
        intro c _hc <;>
        exact congrFun (hconnection c) _
  | inr qj =>
      simp only [auxiliaryHorizontalLiftAt, inverseBitTransportZero,
        ClassicalWeightReduction.combineInverseMap1,
        ClassicalWeightReduction.combineInverseMap1Basis,
        ClassicalWeightReduction.checkPathAuxiliaryPrefix,
        ClassicalWeightReduction.checkPathPrefixWord,
        ClassicalWeightReduction.linearMapOfBasisImages,
        reducedQubitBasisWord,
        LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, zero_apply]
      have hleft :
          (∑ c : ClassicalWeightReduction.AuxiliaryBit R,
            (if c.1 = e.1.1 ∧
                c.2.1 < (ClassicalWeightReduction.checkPosition R e).1 then
              (1 : ZMod 2)
            else 0) *
              (Pi.single
                (Sum.inl
                  (Sum.inr c, (D.connection b e.1.1).onZero i)) 1 :
                Word (ZMod 2)
                  (QubitIndex
                    (ClassicalWeightReduction.WeightReducedCheck R)
                    (ClassicalWeightReduction.WeightReducedBit R)
                    fiberZero fiberOne)) (Sum.inr qj)) = 0 := by
        apply Finset.sum_eq_zero
        intro c _hc
        have hne :
            (Sum.inl
                (Sum.inr c, (D.connection b e.1.1).onZero i) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne) ≠ Sum.inr qj := by
          simp
        rw [Pi.single_eq_of_ne hne.symm, mul_zero]
      simp only [if_true, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hleft]
      symm
      apply Finset.sum_eq_zero
      intro x _hx
      cases x with
      | inl e' =>
          have hne :
              (Sum.inl (Sum.inl e', i) :
                QubitIndex
                  (ClassicalWeightReduction.WeightReducedCheck R)
                  (ClassicalWeightReduction.WeightReducedBit R)
                  fiberZero fiberOne) ≠ Sum.inr qj := by
            simp
          dsimp only
          rw [Pi.single_eq_of_ne hne.symm, mul_zero]
      | inr a =>
          have hne :
              (Sum.inl
                  (Sum.inr a, (D.connection b a.1).onZero i) :
                QubitIndex
                  (ClassicalWeightReduction.WeightReducedCheck R)
                  (ClassicalWeightReduction.WeightReducedBit R)
                  fiberZero fiberOne) ≠ Sum.inr qj := by
            simp
          dsimp only
          rw [Pi.single_eq_of_ne hne.symm, mul_zero]
theorem weightReductionHomotopy0Basis_auxiliary_eq_transport
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (i : fiberZero) :
    weightReductionHomotopy0Basis D
        (Sum.inr
          (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R)) i =
      inverseBitTransportZero D b i
        (classicalCompositeHomotopyBasis D
          (Sum.inr
            (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R))) := by
  classical
  unfold classicalCompositeHomotopyBasis
    ClassicalWeightReduction.combineForwardMap0Basis
    ClassicalWeightReduction.combineHomotopy0Basis
  rw [map_add]
  have hcollapse :
      (∑ e : ClassicalWeightReduction.Incidence R,
        ClassicalWeightReduction.bitCheckSuffix
            (F := ZMod 2) R b k e •
          auxiliaryHorizontalLiftAt D
            ((D.connection e.1.2 e.1.1).onZero i)
            (ClassicalWeightReduction.checkPathPrefixWord
              (F := ZMod 2) R e.1.1
              (ClassicalWeightReduction.checkPosition R e))) =
        inverseBitTransportZero D b i
          (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R
              (ClassicalWeightReduction.bitCheckSuffix
                (F := ZMod 2) R b k))) := by
    unfold ClassicalWeightReduction.collapseHomotopy0
      ClassicalWeightReduction.linearMapOfBasisImages
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases heb : e.1.2 = b
    · subst b
      congr 1
      simpa [classicalCompositeHomotopyBasis,
        ClassicalWeightReduction.combineForwardMap0Basis,
        ClassicalWeightReduction.combineHomotopy0Basis,
        weightReductionHomotopy0Basis_primary] using
        weightReductionHomotopy0Basis_primary_eq_transport D e.1.2 e i
    · have hcoeff :
          ClassicalWeightReduction.bitCheckSuffix
              (F := ZMod 2) R b k e = 0 := by
        simp [ClassicalWeightReduction.bitCheckSuffix, heb]
      simp [hcoeff]
  have hprimary :
      horizontalLiftAt D i
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k) =
        inverseBitTransportZero D b i
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k) :=
    horizontalLiftAt_primaryBitSuffix_eq_inverseTransport D b k i
  change horizontalLiftAt D i
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k) +
        (∑ e : ClassicalWeightReduction.Incidence R,
          ClassicalWeightReduction.bitCheckSuffix
              (F := ZMod 2) R b k e •
            auxiliaryHorizontalLiftAt D
              ((D.connection e.1.2 e.1.1).onZero i)
              (ClassicalWeightReduction.checkPathPrefixWord
                (F := ZMod 2) R e.1.1
                (ClassicalWeightReduction.checkPosition R e))) =
      inverseBitTransportZero D b i
          (ClassicalWeightReduction.combineInverseMap1 (F := ZMod 2) R
            (ClassicalWeightReduction.collapseHomotopy0 (F := ZMod 2) R
              (ClassicalWeightReduction.bitCheckSuffix
                (F := ZMod 2) R b k))) +
        inverseBitTransportZero D b i
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k)
  rw [hcollapse, hprimary, add_comm]
theorem primaryBoundary_homotopy0_term_eq_transport
    (e : ClassicalWeightReduction.Incidence R) (i : fiberZero)
    (a : ClassicalWeightReduction.WeightReducedCheck R) :
    ClassicalWeightReduction.basisBoundary
          (F := ZMod 2) R (Sum.inl e) a •
        weightReductionHomotopy0Basis D a
          ((weightReducedConnection D (Sum.inl e) a).onZero i) =
      ClassicalWeightReduction.basisBoundary
          (F := ZMod 2) R (Sum.inl e) a •
        inverseBitTransportZero D e.1.2 i
          (classicalCompositeHomotopyBasis D a) := by
  classical
  cases a with
  | inl x =>
      by_cases hxe : x = e
      · subst x
        simpa [ClassicalWeightReduction.basisBoundary,
          ClassicalWeightReduction.primaryBitBoundary,
          weightReducedConnection] using congrArg
          (fun w =>
            ClassicalWeightReduction.basisBoundary
                (F := ZMod 2) R (Sum.inl e) (Sum.inl e) • w)
          (weightReductionHomotopy0Basis_primary_eq_transport
            D e.1.2 e i)
      · have hcoeff :
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inl e) (Sum.inl x) = 0 := by
          simp [ClassicalWeightReduction.basisBoundary,
            ClassicalWeightReduction.primaryBitBoundary, hxe]
        simp [hcoeff]
  | inr a =>
      rcases a with ⟨b, k⟩
      by_cases hbe : b = e.1.2
      · subst b
        exact congrArg
          (fun w =>
            ClassicalWeightReduction.basisBoundary
                (F := ZMod 2) R (Sum.inl e)
                  (Sum.inr
                    (⟨e.1.2, k⟩ :
                      ClassicalWeightReduction.AuxiliaryCheck R)) • w)
          (weightReductionHomotopy0Basis_auxiliary_eq_transport
            D e.1.2 k i)
      · have hcoeff :
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inl e)
              (Sum.inr
                (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R)) = 0 := by
          unfold ClassicalWeightReduction.basisBoundary
            ClassicalWeightReduction.primaryBitBoundary
          simp only [Pi.add_apply, Pi.single_apply, Sum.inl_ne_inr,
            if_false, zero_add]
          rw [ClassicalWeightReduction.optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
            (F := ZMod 2) R (Ne.symm hbe)
            (ClassicalWeightReduction.pathPrevious
              (ClassicalWeightReduction.bitPosition R e)) k]
          rw [ClassicalWeightReduction.optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
            (F := ZMod 2) R (Ne.symm hbe)
            (ClassicalWeightReduction.pathNext
              (ClassicalWeightReduction.bitPosition R e)) k]
          rfl
        simp [hcoeff]
theorem twistedHomotopyBoundaryZero_primary_eq_transport
    (e : ClassicalWeightReduction.Incidence R) (i : fiberZero) :
    twistedHomotopyBoundaryZero D (Sum.inl e) i =
      inverseBitTransportZero D e.1.2 i
        (∑ a : ClassicalWeightReduction.WeightReducedCheck R,
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inl e) a •
            classicalCompositeHomotopyBasis D a) := by
  classical
  unfold twistedHomotopyBoundaryZero
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro a _ha
  exact primaryBoundary_homotopy0_term_eq_transport D e i a
@[simp]
theorem inverseBitTransportZero_single_primary
    (b : baseOne) (i : fiberZero)
    (e : ClassicalWeightReduction.Incidence R) :
    inverseBitTransportZero D b i (Pi.single (Sum.inl e) 1) =
      reducedQubitBasisWord D
        (Sum.inl (Sum.inl e, i) :
          QubitIndex
            (ClassicalWeightReduction.WeightReducedCheck R)
            (ClassicalWeightReduction.WeightReducedBit R)
            fiberZero fiberOne) := by
  classical
  unfold inverseBitTransportZero reducedQubitBasisWord
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
theorem twistedHomotopyBoundaryZero_primary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (i : fiberZero) :
    twistedHomotopyBoundaryZero D (Sum.inl e) i =
      (if ClassicalWeightReduction.bitPosition R e =
          ClassicalWeightReduction.bitRootPosition R h e.1.2 then
        fun target =>
          match target with
          | Sum.inl target' =>
              weightReductionInverseBaseOneBasis D e.1.2 i target'
          | Sum.inr _ => 0
      else (0 : Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne))) +
        reducedQubitBasisWord D
          (Sum.inl (Sum.inl e, i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne) := by
  rw [twistedHomotopyBoundaryZero_primary_eq_transport]
  rw [classicalCompositeHomotopy_primary_boundary D h e]
  rw [map_add, inverseBitTransportZero_single_primary]
  by_cases hroot : ClassicalWeightReduction.bitPosition R e =
      ClassicalWeightReduction.bitRootPosition R h e.1.2
  · rw [if_pos hroot, if_pos hroot]
    exact congrArg
      (fun w => w +
        reducedQubitBasisWord D
          (Sum.inl (Sum.inl e, i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne))
      (inverseBitTransportZero_classicalBasis D e.1.2 i)
  · rw [if_neg hroot, if_neg hroot, map_zero]
theorem weightReduction_homotopy_degree1_horizontal_primary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (i : fiberZero) :
    weightReductionInverseMap1 D h
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D
            (Sum.inl (Sum.inl e, i) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))) -
      reducedQubitBasisWord D
        (Sum.inl (Sum.inl e, i) :
          QubitIndex
            (ClassicalWeightReduction.WeightReducedCheck R)
            (ClassicalWeightReduction.WeightReducedBit R)
            fiberZero fiberOne) =
    weightReductionHomotopy0 D
      (boundary1 (weightReducedData D)
        (reducedQubitBasisWord D
          (Sum.inl (Sum.inl e, i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne))) := by
  rw [weightReductionInverseForwardMap1_horizontal_basis]
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  rw [weightReductionHomotopy0_boundary1_horizontal_basis]
  exact (twistedHomotopyBoundaryZero_primary D h e i).symm
theorem weightReductionHomotopy0Basis_primary_eq_horizontalLiftAt
    (e : ClassicalWeightReduction.Incidence R) (i : fiberZero) :
    weightReductionHomotopy0Basis D (Sum.inl e) i =
      horizontalLiftAt D i
        (classicalCompositeHomotopyBasis D (Sum.inl e)) := by
  classical
  rw [weightReductionHomotopy0Basis_primary]
  unfold classicalCompositeHomotopyBasis
    ClassicalWeightReduction.combineForwardMap0Basis
    ClassicalWeightReduction.combineHomotopy0Basis
  simp only [map_zero, add_zero]
  rw [ClassicalWeightReduction.collapseHomotopy0_single]
  unfold ClassicalWeightReduction.collapseHomotopy0Basis
  ext target
  cases target with
  | inl qi =>
      rcases qi with ⟨q, k⟩
      cases q <;>
        simp [auxiliaryHorizontalLiftAt, horizontalLiftAt,
          ClassicalWeightReduction.combineInverseMap1,
          ClassicalWeightReduction.combineInverseMap1Basis,
          ClassicalWeightReduction.checkPathAuxiliaryPrefix,
          ClassicalWeightReduction.checkPathPrefixWord,
          ClassicalWeightReduction.linearMapOfBasisImages,
          reducedQubitBasisWord, Pi.single_apply, apply_ite]
  | inr qj =>
      simp [auxiliaryHorizontalLiftAt, horizontalLiftAt,
        ClassicalWeightReduction.combineInverseMap1,
        ClassicalWeightReduction.combineInverseMap1Basis,
        ClassicalWeightReduction.checkPathAuxiliaryPrefix,
        ClassicalWeightReduction.checkPathPrefixWord,
        ClassicalWeightReduction.linearMapOfBasisImages,
        reducedQubitBasisWord, Pi.single_apply, apply_ite]
theorem classicalCompositeHomotopy_auxiliary_boundary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) :
    (∑ q : ClassicalWeightReduction.WeightReducedCheck R,
      ClassicalWeightReduction.basisBoundary
          (F := ZMod 2) R (Sum.inr a) q •
        classicalCompositeHomotopyBasis D q) =
      Pi.single (Sum.inr a) 1 := by
  rw [classicalCompositeHomotopy_boundary_basis]
  have hdegree := LinearMap.congr_fun
    (classicalCompositeHomotopy_degree1 D h)
    (Pi.single (Sum.inr a) 1)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hdegree
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two] at hdegree
  rw [ClassicalWeightReduction.combineForwardMap1_single] at hdegree
  simp only [ClassicalWeightReduction.combineForwardMap1Basis] at hdegree
  rw [ClassicalWeightReduction.collapseForwardMap1_single] at hdegree
  simp only [ClassicalWeightReduction.collapseForwardMap1Basis,
    map_zero] at hdegree
  simpa using hdegree.symm
theorem auxiliaryBoundary_homotopy0_term_eq_horizontalLiftAt
    (a : ClassicalWeightReduction.AuxiliaryBit R) (i : fiberZero)
    (q : ClassicalWeightReduction.WeightReducedCheck R) :
    ClassicalWeightReduction.basisBoundary
          (F := ZMod 2) R (Sum.inr a) q •
        weightReductionHomotopy0Basis D q
          ((weightReducedConnection D (Sum.inr a) q).onZero i) =
      ClassicalWeightReduction.basisBoundary
          (F := ZMod 2) R (Sum.inr a) q •
        horizontalLiftAt D i (classicalCompositeHomotopyBasis D q) := by
  classical
  cases q with
  | inl e =>
      simpa [weightReducedConnection, FiberAutomorphism.id] using congrArg
        (fun w =>
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inr a) (Sum.inl e) • w)
        (weightReductionHomotopy0Basis_primary_eq_horizontalLiftAt D e i)
  | inr c =>
      have hcoeff :
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inr a) (Sum.inr c) = 0 := by
        rfl
      simp [hcoeff]
theorem twistedHomotopyBoundaryZero_auxiliary_eq_horizontalLiftAt
    (a : ClassicalWeightReduction.AuxiliaryBit R) (i : fiberZero) :
    twistedHomotopyBoundaryZero D (Sum.inr a) i =
      horizontalLiftAt D i
        (∑ q : ClassicalWeightReduction.WeightReducedCheck R,
          ClassicalWeightReduction.basisBoundary
              (F := ZMod 2) R (Sum.inr a) q •
            classicalCompositeHomotopyBasis D q) := by
  classical
  unfold twistedHomotopyBoundaryZero
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro q _hq
  exact auxiliaryBoundary_homotopy0_term_eq_horizontalLiftAt D a i q
@[simp]
theorem horizontalLiftAt_single_auxiliary
    (a : ClassicalWeightReduction.AuxiliaryBit R) (i : fiberZero) :
    horizontalLiftAt D i (Pi.single (Sum.inr a) 1) =
      reducedQubitBasisWord D
        (Sum.inl (Sum.inr a, i) :
          QubitIndex
            (ClassicalWeightReduction.WeightReducedCheck R)
            (ClassicalWeightReduction.WeightReducedBit R)
            fiberZero fiberOne) := by
  classical
  unfold horizontalLiftAt
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
theorem twistedHomotopyBoundaryZero_auxiliary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (i : fiberZero) :
    twistedHomotopyBoundaryZero D (Sum.inr a) i =
      reducedQubitBasisWord D
        (Sum.inl (Sum.inr a, i) :
          QubitIndex
            (ClassicalWeightReduction.WeightReducedCheck R)
            (ClassicalWeightReduction.WeightReducedBit R)
            fiberZero fiberOne) := by
  rw [twistedHomotopyBoundaryZero_auxiliary_eq_horizontalLiftAt]
  rw [classicalCompositeHomotopy_auxiliary_boundary D h a]
  rw [horizontalLiftAt_single_auxiliary]
theorem weightReduction_homotopy_degree1_horizontal_auxiliary
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (a : ClassicalWeightReduction.AuxiliaryBit R) (i : fiberZero) :
    weightReductionInverseMap1 D h
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D
            (Sum.inl (Sum.inr a, i) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))) -
      reducedQubitBasisWord D
        (Sum.inl (Sum.inr a, i) :
          QubitIndex
            (ClassicalWeightReduction.WeightReducedCheck R)
            (ClassicalWeightReduction.WeightReducedBit R)
            fiberZero fiberOne) =
    weightReductionHomotopy0 D
      (boundary1 (weightReducedData D)
        (reducedQubitBasisWord D
          (Sum.inl (Sum.inr a, i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne))) := by
  rw [weightReductionInverseForwardMap1_horizontal_basis]
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  rw [weightReductionHomotopy0_boundary1_horizontal_basis]
  simpa using (twistedHomotopyBoundaryZero_auxiliary D h a i).symm
theorem weightReduction_homotopy_degree1_horizontal
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    weightReductionInverseMap1 D h
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D
            (Sum.inl (q, i) :
              QubitIndex
                (ClassicalWeightReduction.WeightReducedCheck R)
                (ClassicalWeightReduction.WeightReducedBit R)
                fiberZero fiberOne))) -
      reducedQubitBasisWord D
        (Sum.inl (q, i) :
          QubitIndex
            (ClassicalWeightReduction.WeightReducedCheck R)
            (ClassicalWeightReduction.WeightReducedBit R)
            fiberZero fiberOne) =
    weightReductionHomotopy0 D
      (boundary1 (weightReducedData D)
        (reducedQubitBasisWord D
          (Sum.inl (q, i) :
            QubitIndex
              (ClassicalWeightReduction.WeightReducedCheck R)
              (ClassicalWeightReduction.WeightReducedBit R)
              fiberZero fiberOne))) := by
  cases q with
  | inl e =>
      exact weightReduction_homotopy_degree1_horizontal_primary D h e i
  | inr a =>
      exact weightReduction_homotopy_degree1_horizontal_auxiliary D h a i
noncomputable def fiberBoundaryHomotopyZero
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne) :=
  ∑ i : fiberZero,
    D.fiberBoundary i j • weightReductionHomotopy0Basis D q i
theorem weightReductionHomotopy0_boundary1_vertical_basis
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    weightReductionHomotopy0 D
        (boundary1 (weightReducedData D)
          (reducedQubitBasisWord D (Sum.inr (q, j)))) =
      fiberBoundaryHomotopyZero D q j := by
  letI : DecidableEq
      (ClassicalWeightReduction.WeightReducedCheck R) := inferInstance
  letI : DecidableEq
      (ClassicalWeightReduction.WeightReducedBit R) := inferInstance
  letI : DecidableEq
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne) := inferInstance
  classical
  have hboundary
      (ai : ClassicalWeightReduction.WeightReducedCheck R × fiberZero) :
      boundary1 (weightReducedData D)
          (reducedQubitBasisWord D (Sum.inr (q, j))) ai =
        if ai.1 = q then D.fiberBoundary ai.2 j else 0 := by
    unfold reducedQubitBasisWord boundary1
    rw [Matrix.toLin'_apply]
    unfold Matrix.mulVec dotProduct
    rw [Fintype.sum_eq_single (Sum.inr (q, j))]
    · simp [boundary1Matrix, weightReducedData]
    · intro target hne
      simp [Pi.single_apply, hne]
  unfold weightReductionHomotopy0
    ClassicalWeightReduction.linearMapOfBasisImages
    fiberBoundaryHomotopyZero
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single q]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [hboundary, if_pos rfl]
  · intro q' hne
    apply Finset.sum_eq_zero
    intro i _hi
    rw [hboundary, if_neg hne, zero_smul]
theorem degreeTwoLiftAt_apply
    (j k : fiberOne)
    (x : Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R))
    (q : ClassicalWeightReduction.WeightReducedBit R) :
    degreeTwoLiftAt D j x (q, k) = if k = j then x q else 0 := by
  classical
  unfold degreeTwoLiftAt
    ClassicalWeightReduction.linearMapOfBasisImages reducedC2BasisWord
  change (∑ q', x q' • Pi.single (q', j) 1) (q, k) = _
  rw [Finset.sum_apply, Fintype.sum_eq_single q]
  · simp [Pi.single_apply, Prod.ext_iff, mul_comm]
  · intro q' hne
    simp [Pi.single_apply, Ne.symm hne]
theorem auxiliaryDegreeTwoLiftAt_apply
    (j k : fiberOne)
    (x : Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R))
    (a : ClassicalWeightReduction.AuxiliaryBit R) :
    auxiliaryDegreeTwoLiftAt D j x (Sum.inr a, k) =
      if k = j then x a else 0 := by
  classical
  unfold auxiliaryDegreeTwoLiftAt
    ClassicalWeightReduction.linearMapOfBasisImages reducedC2BasisWord
  change (∑ a', x a' • Pi.single (Sum.inr a', j) 1)
      (Sum.inr a, k) = _
  rw [Finset.sum_apply, Fintype.sum_eq_single a]
  · simp [Pi.single_apply, Prod.ext_iff, mul_comm]
  · intro a' hne
    simp [Pi.single_apply, Ne.symm hne]
theorem auxiliaryHorizontalLiftAt_apply
    (k i : fiberZero)
    (x : Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R))
    (a : ClassicalWeightReduction.AuxiliaryBit R) :
    auxiliaryHorizontalLiftAt D k x (Sum.inl (Sum.inr a, i)) =
      if i = k then x a else 0 := by
  classical
  unfold auxiliaryHorizontalLiftAt
    ClassicalWeightReduction.linearMapOfBasisImages reducedQubitBasisWord
  change (∑ a', x a' • Pi.single (Sum.inl (Sum.inr a', k)) 1)
      (Sum.inl (Sum.inr a, i)) = _
  rw [Finset.sum_apply, Fintype.sum_eq_single a]
  · simp [Pi.single_apply, Prod.ext_iff, mul_comm]
  · intro a' hne
    simp [Pi.single_apply, Ne.symm hne]
theorem boundary2_degreeTwoLiftAt_apply_horizontal
    (j : fiberOne)
    (x : Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R))
    (q : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    boundary2 (weightReducedData D) (degreeTwoLiftAt D j x)
        (Sum.inl (q, i)) = D.fiberBoundary i j * x q := by
  rw [boundary2_apply_inl_word]
  simp only [weightReducedData_fiberBoundary, degreeTwoLiftAt_apply]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro j' hne
    rw [if_neg hne, mul_zero]
theorem boundary2_auxiliaryDegreeTwoLiftAt_apply_horizontal
    (P : FiberAutomorphism fiberZero fiberOne D.fiberBoundary)
    (j : fiberOne)
    (x : Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R))
    (a : ClassicalWeightReduction.AuxiliaryBit R) (i : fiberZero) :
    boundary2 (weightReducedData D)
        (auxiliaryDegreeTwoLiftAt D (P.onOne j) x)
        (Sum.inl (Sum.inr a, i)) =
      ∑ k : fiberZero,
        D.fiberBoundary k j *
          auxiliaryHorizontalLiftAt D (P.onZero k) x
            (Sum.inl (Sum.inr a, i)) := by
  rw [boundary2_apply_inl_word]
  simp only [weightReducedData_fiberBoundary,
    auxiliaryDegreeTwoLiftAt_apply, auxiliaryHorizontalLiftAt_apply]
  rw [Fintype.sum_eq_single (P.onOne j)]
  · rw [if_pos rfl]
    exact (sum_fiberBoundary_transport_single D P (x a) i j).symm
  · intro j' hne
    rw [if_neg hne, mul_zero]
theorem boundary2_degreeTwoLiftAt_fiber_naturality
    (j : fiberOne)
    (x : Word (ZMod 2) (ClassicalWeightReduction.WeightReducedBit R))
    (target : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    boundary2 (weightReducedData D) (degreeTwoLiftAt D j x)
        (Sum.inl target) =
      ∑ k : fiberZero,
        D.fiberBoundary k j *
          horizontalLiftAt D k x (Sum.inl target) := by
  rcases target with ⟨q, i⟩
  rw [boundary2_degreeTwoLiftAt_apply_horizontal]
  simp only [horizontalLiftAt_apply_inl]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro k hne
    rw [if_neg (Ne.symm hne), mul_zero]
theorem boundary2_auxiliaryDegreeTwoLiftAt_fiber_naturality
    (P : FiberAutomorphism fiberZero fiberOne D.fiberBoundary)
    (j : fiberOne)
    (x : Word (ZMod 2) (ClassicalWeightReduction.AuxiliaryBit R))
    (target : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    boundary2 (weightReducedData D)
        (auxiliaryDegreeTwoLiftAt D (P.onOne j) x)
        (Sum.inl target) =
      ∑ k : fiberZero,
        D.fiberBoundary k j *
          auxiliaryHorizontalLiftAt D (P.onZero k) x
            (Sum.inl target) := by
  rcases target with ⟨q, i⟩
  cases q with
  | inl e =>
      rw [boundary2_apply_inl_word]
      simp [auxiliaryDegreeTwoLiftAt, auxiliaryHorizontalLiftAt,
        ClassicalWeightReduction.linearMapOfBasisImages,
        reducedC2BasisWord, reducedQubitBasisWord, Pi.single_apply]
  | inr a =>
      exact boundary2_auxiliaryDegreeTwoLiftAt_apply_horizontal
        D P j x a i
theorem boundary2_weightReductionHomotopy1Basis_vertical_primary_apply_horizontal
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    boundary2 (weightReducedData D)
        (weightReductionHomotopy1Basis D (Sum.inr (Sum.inl e, j)))
        (Sum.inl target) =
      fiberBoundaryHomotopyZero D (Sum.inl e) j (Sum.inl target) := by
  rw [weightReductionHomotopy1Basis_vertical_primary]
  unfold fiberBoundaryHomotopyZero
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [weightReductionHomotopy0Basis_primary]
  simpa [FiberAutomorphism.id] using
    boundary2_auxiliaryDegreeTwoLiftAt_fiber_naturality D
      (FiberAutomorphism.id D.fiberBoundary) j
      (ClassicalWeightReduction.checkPathPrefixWord
        (F := ZMod 2) R e.1.1
        (ClassicalWeightReduction.checkPosition R e)) target
theorem boundary2_weightReductionHomotopy1Basis_vertical_auxiliary_apply_horizontal
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    boundary2 (weightReducedData D)
        (weightReductionHomotopy1Basis D
          (Sum.inr
            (Sum.inr
              (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R), j)))
        (Sum.inl target) =
      fiberBoundaryHomotopyZero D
        (Sum.inr
          (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R)) j
        (Sum.inl target) := by
  classical
  rw [weightReductionHomotopy1Basis_vertical_auxiliary]
  rw [map_add, map_sum]
  simp only [map_smul, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [boundary2_degreeTwoLiftAt_fiber_naturality]
  simp_rw [boundary2_auxiliaryDegreeTwoLiftAt_fiber_naturality]
  unfold fiberBoundaryHomotopyZero
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [weightReductionHomotopy0Basis_auxiliary]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  congr 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro i _hi
  ring
theorem boundary2_weightReductionHomotopy1Basis_vertical_apply_horizontal
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    boundary2 (weightReducedData D)
        (weightReductionHomotopy1Basis D (Sum.inr (q, j)))
        (Sum.inl target) =
      fiberBoundaryHomotopyZero D q j (Sum.inl target) := by
  cases q with
  | inl e =>
      exact
        boundary2_weightReductionHomotopy1Basis_vertical_primary_apply_horizontal
          D e j target
  | inr a =>
      rcases a with ⟨b, k⟩
      exact
        boundary2_weightReductionHomotopy1Basis_vertical_auxiliary_apply_horizontal
          D b k j target
theorem weightReduction_vertical_fiber_terms_cancel_apply_horizontal
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    (boundary2 (weightReducedData D)
          (weightReductionHomotopy1 D
            (reducedQubitBasisWord D (Sum.inr (q, j)))) +
        weightReductionHomotopy0 D
          (boundary1 (weightReducedData D)
            (reducedQubitBasisWord D (Sum.inr (q, j)))))
        (Sum.inl target) = 0 := by
  rw [weightReductionHomotopy1_single]
  rw [weightReductionHomotopy0_boundary1_vertical_basis]
  simp only [Pi.add_apply]
  rw [boundary2_weightReductionHomotopy1Basis_vertical_apply_horizontal]
  exact ClassicalWeightReduction.add_self_eq_zero_of_char_two
    (F := ZMod 2) _
def verticalQubitProjection :
    Word (ZMod 2)
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberOne) where
  toFun w qj := w (Sum.inr qj)
  map_add' x y := by rfl
  map_smul' coefficient x := by rfl
noncomputable def primaryCheckVerticalLiftAt (j : fiberOne) :
    Word (ZMod 2) (ClassicalWeightReduction.Incidence R) →ₗ[ZMod 2]
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :=
  ClassicalWeightReduction.linearMapOfBasisImages
    (fun e => Pi.single (Sum.inl e, j) 1)
@[simp]
theorem primaryCheckVerticalLiftAt_single
    (j : fiberOne) (e : ClassicalWeightReduction.Incidence R) :
    primaryCheckVerticalLiftAt D j (Pi.single e 1) =
      Pi.single (Sum.inl e, j) 1 := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
theorem verticalQubitProjection_boundary2_auxiliaryDegreeTwoLiftAt_single
    (j : fiberOne) (a : ClassicalWeightReduction.AuxiliaryBit R) :
    verticalQubitProjection D
        (boundary2 (weightReducedData D)
          (auxiliaryDegreeTwoLiftAt D j (Pi.single a 1))) =
      primaryCheckVerticalLiftAt D j
        (ClassicalWeightReduction.bitSplitAuxiliaryBoundary
          (F := ZMod 2) R a) := by
  classical
  rw [auxiliaryDegreeTwoLiftAt_single]
  ext target
  rcases target with ⟨q, j'⟩
  change boundary2 (weightReducedData D)
      (reducedC2BasisWord D (Sum.inr a) j) (Sum.inr (q, j')) =
    primaryCheckVerticalLiftAt D j
      (ClassicalWeightReduction.bitSplitAuxiliaryBoundary
        (F := ZMod 2) R a) (q, j')
  rw [boundary2_reducedC2BasisWord_apply_inr]
  unfold primaryCheckVerticalLiftAt
    ClassicalWeightReduction.linearMapOfBasisImages
  cases q with
  | inl e =>
      simp [weightReducedConnection,
        ClassicalWeightReduction.basisBoundary,
        ClassicalWeightReduction.auxiliaryBitBoundary,
        ClassicalWeightReduction.bitSplitAuxiliaryBoundary,
        Pi.single_apply, Prod.ext_iff]
      rw [Fintype.sum_eq_single e]
      · simp [FiberAutomorphism.id] <;> rfl
      · intro e' hne
        rw [if_neg (fun h => hne h.1.symm)]
  | inr c =>
      simp [weightReducedConnection,
        ClassicalWeightReduction.basisBoundary,
        ClassicalWeightReduction.auxiliaryBitBoundary,
        ClassicalWeightReduction.bitSplitAuxiliaryBoundary,
        Pi.single_apply]
theorem verticalQubitProjection_boundary2_comp_auxiliaryDegreeTwoLiftAt
    (j : fiberOne) :
    (verticalQubitProjection D).comp
        ((boundary2 (weightReducedData D)).comp
          (auxiliaryDegreeTwoLiftAt D j)) =
      (primaryCheckVerticalLiftAt D j).comp (auxiliaryPathBoundary D) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro a
  simp only [LinearMap.comp_apply]
  rw [auxiliaryPathBoundary_single]
  exact verticalQubitProjection_boundary2_auxiliaryDegreeTwoLiftAt_single
    D j a
theorem verticalQubitProjection_boundary2_auxiliaryCheckPathPrefix
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (j : fiberOne) (e : ClassicalWeightReduction.Incidence R) :
    verticalQubitProjection D
        (boundary2 (weightReducedData D)
          (auxiliaryDegreeTwoLiftAt D j
            (ClassicalWeightReduction.checkPathPrefixWord
              (F := ZMod 2) R e.1.1
              (ClassicalWeightReduction.checkPosition R e)))) =
      primaryCheckVerticalLiftAt D j
        (Pi.single
            (ClassicalWeightReduction.checkIncidenceAt R e.1.1
              (ClassicalWeightReduction.checkRootPosition R h e.1.1)) 1 +
          Pi.single e 1) := by
  have hchain := LinearMap.congr_fun
    (verticalQubitProjection_boundary2_comp_auxiliaryDegreeTwoLiftAt D j)
    (ClassicalWeightReduction.checkPathPrefixWord
      (F := ZMod 2) R e.1.1
      (ClassicalWeightReduction.checkPosition R e))
  simp only [LinearMap.comp_apply] at hchain
  rw [hchain]
  congr 1
  rw [auxiliaryPathBoundary_eq_bitSplitBoundary_embed D]
  rw [← ClassicalWeightReduction.checkPathAuxiliaryPrefix_eq_embed]
  rw [ClassicalWeightReduction.bitSplitBoundary_checkPathAuxiliaryPrefix
    (F := ZMod 2) R h]
  rw [ClassicalWeightReduction.checkIncidenceAt_checkPosition]
theorem weightReductionInverseForwardMap1_vertical_primary_basis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    weightReductionInverseMap1 D h
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D (Sum.inr (Sum.inl e, j)))) =
      reducedQubitBasisWord D
        (Sum.inr
          (Sum.inl
            (ClassicalWeightReduction.checkIncidenceAt R e.1.1
              (ClassicalWeightReduction.checkRootPosition R h e.1.1)), j)) := by
  classical
  rw [weightReductionForwardMap1_reducedQubitBasisWord_inr]
  have hforward :
      (fun target : QubitIndex baseZero baseOne fiberZero fiberOne =>
        match target with
        | Sum.inl _ => 0
        | Sum.inr target' =>
            weightReductionForwardBaseZeroOneBasis D (Sum.inl e) j target') =
        Pi.single (Sum.inr (e.1.1, j)) 1 := by
    ext target
    cases target with
    | inl bi =>
        simp [weightReductionForwardBaseZeroOneBasis, Pi.single_apply]
    | inr aj =>
        simp [weightReductionForwardBaseZeroOneBasis, Pi.single_apply]
  rw [hforward, weightReductionInverseMap1_single_inr]
  ext target
  cases target <;>
    simp [weightReductionInverseBaseZeroOneBasis,
      reducedQubitBasisWord, Pi.single_apply]
theorem weightReduction_vertical_primary_rooted_discrepancy
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (e : ClassicalWeightReduction.Incidence R) (j : fiberOne) :
    verticalQubitProjection D
        (weightReductionInverseMap1 D h
            (weightReductionForwardMap1 D h
              (reducedQubitBasisWord D (Sum.inr (Sum.inl e, j)))) -
          reducedQubitBasisWord D (Sum.inr (Sum.inl e, j))) =
      verticalQubitProjection D
        (boundary2 (weightReducedData D)
          (weightReductionHomotopy1 D
            (reducedQubitBasisWord D (Sum.inr (Sum.inl e, j))))) := by
  rw [weightReductionInverseForwardMap1_vertical_primary_basis D h]
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  rw [weightReductionHomotopy1_single,
    weightReductionHomotopy1Basis_vertical_primary]
  rw [verticalQubitProjection_boundary2_auxiliaryCheckPathPrefix D h]
  simp only [map_add]
  rw [primaryCheckVerticalLiftAt_single,
    primaryCheckVerticalLiftAt_single]
  ext target
  simp [verticalQubitProjection, reducedQubitBasisWord, Pi.single_apply]
noncomputable def transportedBitCheckSuffixOne
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :=
  ∑ e : ClassicalWeightReduction.Incidence R,
    ClassicalWeightReduction.bitCheckSuffix (F := ZMod 2) R b k e •
      Pi.single
        (Sum.inl e, (D.connection e.1.2 e.1.1).onOne j) 1
noncomputable def rootedBitCheckSuffixOne
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :=
  ∑ e : ClassicalWeightReduction.Incidence R,
    ClassicalWeightReduction.bitCheckSuffix (F := ZMod 2) R b k e •
      weightReductionInverseBaseZeroOneBasis D h e.1.1
        ((D.connection e.1.2 e.1.1).onOne j)
theorem inverseCheckTransportOne_combineInverse_bitCheckSuffix
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    inverseCheckTransportOne D b j
        (ClassicalWeightReduction.combineInverseMap0 (F := ZMod 2) R
          (ClassicalWeightReduction.bitCheckSuffix
            (F := ZMod 2) R b k)) =
      transportedBitCheckSuffixOne D b k j := by
  classical
  unfold ClassicalWeightReduction.combineInverseMap0
    inverseCheckTransportOne transportedBitCheckSuffixOne
    ClassicalWeightReduction.linearMapOfBasisImages
  change inverseCheckTransportOne D b j
      (∑ e : ClassicalWeightReduction.Incidence R,
        ClassicalWeightReduction.bitCheckSuffix
            (F := ZMod 2) R b k e • Pi.single (Sum.inl e) 1) = _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heb : e.1.2 = b
  · congr 1
    unfold inverseCheckTransportOne
    rw [ClassicalWeightReduction.linearMapOfBasisImages_single]
    subst b
    rfl
  · have hcoeff :
        ClassicalWeightReduction.bitCheckSuffix
            (F := ZMod 2) R b k e = 0 := by
      simp [ClassicalWeightReduction.bitCheckSuffix, heb]
    simp [hcoeff]
@[simp]
theorem inverseCheckTransportOne_single_auxiliary
    (b : baseOne) (j : fiberOne)
    (a : ClassicalWeightReduction.AuxiliaryCheck R) :
    inverseCheckTransportOne D b j (Pi.single (Sum.inr a) 1) =
      Pi.single (Sum.inr a, j) 1 := by
  classical
  unfold inverseCheckTransportOne
  exact ClassicalWeightReduction.linearMapOfBasisImages_single _ _
theorem degreeTwoLiftAt_primaryBitSuffix_eq_inverseTransportOne
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    degreeTwoLiftAt D j
        (ClassicalWeightReduction.primaryBitSuffix
          (F := ZMod 2) R b k) =
      inverseBitTransportOne D b j
        (ClassicalWeightReduction.primaryBitSuffix
          (F := ZMod 2) R b k) := by
  ext target
  rcases target with ⟨q, j'⟩
  cases q <;>
    simp [degreeTwoLiftAt, inverseBitTransportOne,
      ClassicalWeightReduction.primaryBitSuffix,
      ClassicalWeightReduction.linearMapOfBasisImages,
      reducedC2BasisWord, Pi.single_apply]
theorem inverseTransportOne_primaryBitSuffix_boundary_apply
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :
    boundary2 (weightReducedData D)
        (inverseBitTransportOne D b j
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k)) (Sum.inr target) =
      inverseCheckTransportOne D b j
        (ClassicalWeightReduction.boundary (F := ZMod 2) R
          (ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k)) target := by
  classical
  unfold inverseBitTransportOne
    ClassicalWeightReduction.boundary
    ClassicalWeightReduction.linearMapOfBasisImages
  change boundary2 (weightReducedData D)
      (∑ q : ClassicalWeightReduction.WeightReducedBit R,
        ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k q •
          match q with
          | Sum.inl e => Pi.single (Sum.inl e, j) 1
          | Sum.inr a =>
              Pi.single (Sum.inr a, (D.connection b a.1).onOne j) 1)
      (Sum.inr target) =
    inverseCheckTransportOne D b j
      (∑ q : ClassicalWeightReduction.WeightReducedBit R,
        ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k q •
          ClassicalWeightReduction.basisBoundary (F := ZMod 2) R q)
      target
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [ClassicalWeightReduction.primaryBitSuffix_auxiliary,
    zero_smul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heb : e.1.2 = b
  · congr 1
    simpa [reducedC2BasisWord,
      ClassicalWeightReduction.boundary_single] using
      inverseTransportOne_primary_boundary_apply D b j e heb target
  · have hcoeff :
        ClassicalWeightReduction.primaryBitSuffix
            (F := ZMod 2) R b k (Sum.inl e) = 0 := by
      simp [ClassicalWeightReduction.primaryBitSuffix,
        ClassicalWeightReduction.bitFiberSuffix,
        ClassicalWeightReduction.incidenceBitPosition, heb]
    simp [hcoeff]
theorem verticalQubitProjection_boundary2_degreeTwoLiftAt_primaryBitSuffix
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    verticalQubitProjection D
        (boundary2 (weightReducedData D)
          (degreeTwoLiftAt D j
            (ClassicalWeightReduction.primaryBitSuffix
              (F := ZMod 2) R b k))) =
      transportedBitCheckSuffixOne D b k j +
        Pi.single
          ((Sum.inr (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R) :
              ClassicalWeightReduction.WeightReducedCheck R), j) 1 := by
  rw [degreeTwoLiftAt_primaryBitSuffix_eq_inverseTransportOne]
  ext target
  change boundary2 (weightReducedData D)
      (inverseBitTransportOne D b j
        (ClassicalWeightReduction.primaryBitSuffix
          (F := ZMod 2) R b k)) (Sum.inr target) = _
  rw [inverseTransportOne_primaryBitSuffix_boundary_apply]
  rw [ClassicalWeightReduction.boundary_primaryBitSuffix]
  rw [map_add, inverseCheckTransportOne_combineInverse_bitCheckSuffix]
  rw [inverseCheckTransportOne_single_auxiliary]
theorem verticalQubitProjection_boundary2_auxiliaryCollapseSuffix
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    verticalQubitProjection D
        (boundary2 (weightReducedData D)
          (∑ e : ClassicalWeightReduction.Incidence R,
            ClassicalWeightReduction.bitCheckSuffix
                (F := ZMod 2) R b k e •
              auxiliaryDegreeTwoLiftAt D
                ((D.connection e.1.2 e.1.1).onOne j)
                (ClassicalWeightReduction.checkPathPrefixWord
                  (F := ZMod 2) R e.1.1
                  (ClassicalWeightReduction.checkPosition R e)))) =
      rootedBitCheckSuffixOne D h b k j +
        transportedBitCheckSuffixOne D b k j := by
  classical
  simp only [map_sum, map_smul]
  unfold rootedBitCheckSuffixOne transportedBitCheckSuffixOne
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  rw [verticalQubitProjection_boundary2_auxiliaryCheckPathPrefix D h]
  simp only [map_add]
  rw [primaryCheckVerticalLiftAt_single,
    primaryCheckVerticalLiftAt_single, smul_add]
  rfl
theorem weightReductionInverseForwardMap1_vertical_auxiliary_basis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    weightReductionInverseMap1 D h
        (weightReductionForwardMap1 D h
          (reducedQubitBasisWord D
            (Sum.inr
              (Sum.inr
                (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R), j)))) =
      fun target =>
        match target with
        | Sum.inl _ => 0
        | Sum.inr target' => rootedBitCheckSuffixOne D h b k j target' := by
  classical
  rw [weightReductionForwardMap1_reducedQubitBasisWord_inr]
  have hforward :
      (fun target : QubitIndex baseZero baseOne fiberZero fiberOne =>
        match target with
        | Sum.inl _ => 0
        | Sum.inr target' =>
            weightReductionForwardBaseZeroOneBasis D
              (Sum.inr
                (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R))
              j target') =
        ∑ e : ClassicalWeightReduction.Incidence R,
          ClassicalWeightReduction.bitCheckSuffix (F := ZMod 2) R b k e •
            Pi.single
              (Sum.inr (e.1.1, (D.connection e.1.2 e.1.1).onOne j)) 1 := by
    ext target
    cases target with
    | inl bi =>
        simp [weightReductionForwardBaseZeroOneBasis,
          ClassicalWeightReduction.combineForwardMap0Basis,
          Pi.single_apply]
    | inr aj =>
        simp [weightReductionForwardBaseZeroOneBasis,
          ClassicalWeightReduction.combineForwardMap0Basis,
          Pi.single_apply]
  rw [hforward]
  simp only [map_sum, map_smul]
  unfold rootedBitCheckSuffixOne
  ext target
  cases target with
  | inl qi =>
      simp [weightReductionInverseMap1_single_inr]
  | inr qj =>
      simp only [Finset.sum_apply, Pi.smul_apply]
      apply Finset.sum_congr rfl
      intro e _he
      rw [weightReductionInverseMap1_single_inr]
@[simp]
theorem verticalQubitProjection_reducedQubitBasisWord_inr
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    verticalQubitProjection D
        (reducedQubitBasisWord D (Sum.inr (q, j))) =
      Pi.single (q, j) 1 := by
  ext target
  simp [verticalQubitProjection, reducedQubitBasisWord, Pi.single_apply]
@[simp]
theorem verticalQubitProjection_verticalWord
    (w : Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedCheck R × fiberOne)) :
    verticalQubitProjection D
        (fun target =>
          match target with
          | Sum.inl _ => 0
          | Sum.inr target' => w target') = w := by
  rfl
theorem weightReduction_vertical_auxiliary_rooted_discrepancy
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (k : Fin (Fintype.card (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    verticalQubitProjection D
        (weightReductionInverseMap1 D h
            (weightReductionForwardMap1 D h
              (reducedQubitBasisWord D
                (Sum.inr
                  (Sum.inr
                    (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R),
                    j)))) -
          reducedQubitBasisWord D
            (Sum.inr
              (Sum.inr
                (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R), j))) =
      verticalQubitProjection D
        (boundary2 (weightReducedData D)
          (weightReductionHomotopy1 D
            (reducedQubitBasisWord D
              (Sum.inr
                (Sum.inr
                  (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R),
                  j))))) := by
  classical
  rw [weightReductionInverseForwardMap1_vertical_auxiliary_basis D h]
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  rw [weightReductionHomotopy1_single,
    weightReductionHomotopy1Basis_vertical_auxiliary]
  simp only [map_add]
  rw [verticalQubitProjection_boundary2_degreeTwoLiftAt_primaryBitSuffix,
    verticalQubitProjection_boundary2_auxiliaryCollapseSuffix D h]
  rw [verticalQubitProjection_verticalWord,
    verticalQubitProjection_reducedQubitBasisWord_inr]
  let transported := transportedBitCheckSuffixOne D b k j
  let rooted := rootedBitCheckSuffixOne D h b k j
  let auxiliary :
      Word (ZMod 2)
        (ClassicalWeightReduction.WeightReducedCheck R × fiberOne) :=
    Pi.single
      ((Sum.inr (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R) :
          ClassicalWeightReduction.WeightReducedCheck R), j) 1
  change rooted + auxiliary =
    (transported + auxiliary) + (rooted + transported)
  calc
    rooted + auxiliary =
        (rooted + auxiliary) + (transported + transported) := by
      rw [ClassicalWeightReduction.word_add_self_eq_zero_of_char_two,
        add_zero]
    _ = (transported + auxiliary) + (rooted + transported) := by
      ac_rfl
theorem weightReduction_vertical_rooted_discrepancy
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    verticalQubitProjection D
        (weightReductionInverseMap1 D h
            (weightReductionForwardMap1 D h
              (reducedQubitBasisWord D (Sum.inr (q, j)))) -
          reducedQubitBasisWord D (Sum.inr (q, j))) =
      verticalQubitProjection D
        (boundary2 (weightReducedData D)
          (weightReductionHomotopy1 D
            (reducedQubitBasisWord D (Sum.inr (q, j))))) := by
  cases q with
  | inl e =>
      exact weightReduction_vertical_primary_rooted_discrepancy D h e j
  | inr a =>
      rcases a with ⟨b, k⟩
      exact weightReduction_vertical_auxiliary_rooted_discrepancy
        D h b k j
theorem verticalQubitProjection_weightReductionHomotopy0Basis
    (q : ClassicalWeightReduction.WeightReducedCheck R) (i : fiberZero) :
    verticalQubitProjection D (weightReductionHomotopy0Basis D q i) = 0 := by
  classical
  cases q with
  | inl e =>
      rw [weightReductionHomotopy0Basis_primary]
      ext target
      simp [verticalQubitProjection, auxiliaryHorizontalLiftAt,
        ClassicalWeightReduction.linearMapOfBasisImages,
        reducedQubitBasisWord, Pi.single_apply]
  | inr a =>
      rcases a with ⟨b, k⟩
      rw [weightReductionHomotopy0Basis_auxiliary]
      ext target
      simp [verticalQubitProjection, horizontalLiftAt,
        auxiliaryHorizontalLiftAt,
        ClassicalWeightReduction.linearMapOfBasisImages,
        reducedQubitBasisWord, Pi.single_apply]
theorem verticalQubitProjection_weightReductionHomotopy0
    (x : Word (ZMod 2)
      (ClassicalWeightReduction.WeightReducedCheck R × fiberZero)) :
    verticalQubitProjection D (weightReductionHomotopy0 D x) = 0 := by
  classical
  unfold weightReductionHomotopy0
    ClassicalWeightReduction.linearMapOfBasisImages
  change verticalQubitProjection D
      (∑ qi, x qi • weightReductionHomotopy0Basis D qi.1 qi.2) = 0
  simp [map_sum, map_smul,
    verticalQubitProjection_weightReductionHomotopy0Basis]
theorem weightReductionInverseForwardMap1_vertical_basis_apply_horizontal
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne)
    (target : ClassicalWeightReduction.WeightReducedBit R × fiberZero) :
    (weightReductionInverseMap1 D h
          (weightReductionForwardMap1 D h
            (reducedQubitBasisWord D (Sum.inr (q, j)))) -
        reducedQubitBasisWord D (Sum.inr (q, j)))
      (Sum.inl target) = 0 := by
  rw [ClassicalWeightReduction.word_sub_eq_add_of_char_two]
  cases q with
  | inl e =>
      rw [weightReductionInverseForwardMap1_vertical_primary_basis D h]
      simp [reducedQubitBasisWord, Pi.single_apply]
  | inr a =>
      rcases a with ⟨b, k⟩
      rw [weightReductionInverseForwardMap1_vertical_auxiliary_basis D h]
      simp [reducedQubitBasisWord, Pi.single_apply]
theorem weightReduction_homotopy_degree1_vertical_basis
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : ClassicalWeightReduction.WeightReducedCheck R) (j : fiberOne) :
    weightReductionInverseMap1 D h
          (weightReductionForwardMap1 D h
            (reducedQubitBasisWord D (Sum.inr (q, j)))) -
        reducedQubitBasisWord D (Sum.inr (q, j)) =
      boundary2 (weightReducedData D)
          (weightReductionHomotopy1 D
            (reducedQubitBasisWord D (Sum.inr (q, j)))) +
        weightReductionHomotopy0 D
          (boundary1 (weightReducedData D)
            (reducedQubitBasisWord D (Sum.inr (q, j)))) := by
  ext target
  cases target with
  | inl qi =>
      rw [weightReductionInverseForwardMap1_vertical_basis_apply_horizontal]
      exact
        (weightReduction_vertical_fiber_terms_cancel_apply_horizontal
          D q j qi).symm
  | inr qj =>
      have hroot := congrFun
        (weightReduction_vertical_rooted_discrepancy D h q j) qj
      have hzero := congrFun
        (verticalQubitProjection_weightReductionHomotopy0 D
          (boundary1 (weightReducedData D)
            (reducedQubitBasisWord D (Sum.inr (q, j))))) qj
      change weightReductionHomotopy0 D
          (boundary1 (weightReducedData D)
            (reducedQubitBasisWord D (Sum.inr (q, j))))
          (Sum.inr qj) = 0 at hzero
      change
        (weightReductionInverseMap1 D h
              (weightReductionForwardMap1 D h
                (reducedQubitBasisWord D (Sum.inr (q, j)))) -
            reducedQubitBasisWord D (Sum.inr (q, j))) (Sum.inr qj) =
          boundary2 (weightReducedData D)
              (weightReductionHomotopy1 D
                (reducedQubitBasisWord D (Sum.inr (q, j))))
              (Sum.inr qj) +
            weightReductionHomotopy0 D
              (boundary1 (weightReducedData D)
                (reducedQubitBasisWord D (Sum.inr (q, j))))
              (Sum.inr qj)
      rw [hzero, add_zero]
      exact hroot
theorem weightReduction_homotopy_degree1
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    (weightReductionInverseMap1 D h).comp
          (weightReductionForwardMap1 D h) - LinearMap.id =
      (boundary2 (weightReducedData D)).comp
          (weightReductionHomotopy1 D) +
        (weightReductionHomotopy0 D).comp
          (boundary1 (weightReducedData D)) := by
  classical
  apply ClassicalWeightReduction.linearMap_eq_of_single_one_eq
  intro qi
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, LinearMap.add_apply]
  cases qi with
  | inl qi =>
      rcases qi with ⟨q, i⟩
      have hH1 :
          weightReductionHomotopy1 D
              (Pi.single (Sum.inl (q, i)) 1) = 0 := by
        change weightReductionHomotopy1 D
            (reducedQubitBasisWord D (Sum.inl (q, i))) = 0
        rw [weightReductionHomotopy1_single,
          weightReductionHomotopy1Basis_horizontal]
      rw [hH1, map_zero, zero_add]
      simpa [reducedQubitBasisWord] using
        weightReduction_homotopy_degree1_horizontal D h q i
  | inr qj =>
      exact weightReduction_homotopy_degree1_vertical_basis
        D h qj.1 qj.2
noncomputable def weightReductionInverseForwardHomotopy
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    ThreeTermChainHomotopy
      ((weightReductionInverseChainMap D h).comp
        (weightReductionForwardChainMap D h))
      (ThreeTermChainMap.id (chainComplex (weightReducedData D))) where
  homotopy0 := weightReductionHomotopy0 D
  homotopy1 := weightReductionHomotopy1 D
  degree0 := by
    exact weightReduction_homotopy_degree0 D h
  degree1 := by
    simp only [ThreeTermChainMap.comp_map1,
      ThreeTermChainMap.id_map1]
    change (weightReductionInverseMap1 D h).comp
          (weightReductionForwardMap1 D h) - LinearMap.id =
      (weightReductionHomotopy0 D).comp
          (boundary1 (weightReducedData D)) +
        (boundary2 (weightReducedData D)).comp
          (weightReductionHomotopy1 D)
    rw [add_comm]
    exact weightReduction_homotopy_degree1 D h
  degree2 := by
    exact weightReduction_homotopy_degree2 D h
noncomputable def weightReductionForwardInverseHomotopy
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    ThreeTermChainHomotopy
      ((weightReductionForwardChainMap D h).comp
        (weightReductionInverseChainMap D h))
      (ThreeTermChainMap.id (chainComplex D)) where
  homotopy0 := 0
  homotopy1 := 0
  degree0 := by
    simp only [ThreeTermChainMap.comp_map0, ThreeTermChainMap.id_map0]
    change (weightReductionForwardMap0 D).comp
        (weightReductionInverseMap0 D h) - LinearMap.id = _
    rw [weightReductionForwardMap0_comp_inverseMap0 D h]
    simp
  degree1 := by
    simp only [ThreeTermChainMap.comp_map1, ThreeTermChainMap.id_map1]
    change (weightReductionForwardMap1 D h).comp
        (weightReductionInverseMap1 D h) - LinearMap.id = _
    rw [weightReductionForwardMap1_comp_inverseMap1 D h]
    simp
  degree2 := by
    simp only [ThreeTermChainMap.comp_map2, ThreeTermChainMap.id_map2]
    change (weightReductionForwardMap2 D h).comp
        (weightReductionInverseMap2 D) - LinearMap.id = _
    rw [weightReductionForwardMap2_comp_inverseMap2 D h]
    simp
noncomputable def weightReductionHomotopyEquiv
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    ThreeTermChainHomotopyEquiv
      (chainComplex (weightReducedData D)) (chainComplex D) where
  forward := weightReductionForwardChainMap D h
  inverse := weightReductionInverseChainMap D h
  inverse_forward := weightReductionInverseForwardHomotopy D h
  forward_inverse := weightReductionForwardInverseHomotopy D h
end TwistedInverse
namespace RandomBase
def incidenceRelation {r : Nat} (sample : Sample r)
    (a : Fin (3 * r)) (b : Fin (4 * r)) : Prop :=
  sample (a, b) = true
instance {r : Nat} (sample : Sample r) :
    DecidableRel (incidenceRelation sample) :=
  fun a b => Bool.decEq (sample (a, b)) true
end RandomBase
end QEC.Coding.FiberBundle


