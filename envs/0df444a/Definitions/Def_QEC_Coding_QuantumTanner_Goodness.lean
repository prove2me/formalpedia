-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_Goodness
-- name    : QEC_Coding_QuantumTanner_Goodness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:19:20.691547+00:00
-- url     : https://prove2.me/theorems/b5214a79-6080-4d41-9464-ee4c220ddd8f
-- title:
--   Goodness
-- statement:
--   Definitions and structural lemmas for Goodness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Theorems.Thm_QEC_Coding_ChainComplexData_binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_fixed_of_generatedStabilizer
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowChecks_generate_stabilizerGroup
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
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
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
def binaryEntropy (delta : ℝ) : ℝ :=
  -delta * Real.logb 2 delta - (1 - delta) * Real.logb 2 (1 - delta)
def randomRowCount (rho : ℝ) (Delta : Nat) : Nat :=
  Nat.floor (rho * Delta)
def IsLZ22AdmissibleDegree (Delta : Nat) : Prop :=
  ∃ q : Nat, IsPrimePow q ∧ Odd q ∧ Delta = q + 1
section RobustnessAsymptotics
open Filter
end RobustnessAsymptotics
section RobustnessIndexBounds
open Filter
end RobustnessIndexBounds
def HasPositiveUniformProbability {Ω : Type u} [Fintype Ω]
    (event : Ω → Prop) [DecidablePred event] : Prop :=
  0 < (eventFinset event).card
noncomputable def tensorWordEquiv
    (F : Type u) (A B : Type v) [Field F] [Fintype B] :
    (Word F A ⊗[F] Word F B) ≃ₗ[F] Word F (A × B) := by
  letI := Classical.decEq B
  exact (TensorProduct.piScalarRight F F (Word F A) B).trans
    ((LinearEquiv.curry F F B A).symm.trans
      (LinearEquiv.funCongrLeft F F (Equiv.prodComm A B)))
@[simp]
theorem tensorWordEquiv_tmul_apply
    {F : Type u} {A B : Type v} [Field F] [Fintype B]
    (x : Word F A) (y : Word F B) (a : A) (b : B) :
    tensorWordEquiv F A B (x ⊗ₜ[F] y) (a, b) = x a * y b := by
  letI := Classical.decEq B
  simp [tensorWordEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, mul_comm]
noncomputable def tensorCodeTensorMap
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    CA.carrier ⊗[F] CB.carrier →ₗ[F] (tensorCode CA CB).carrier :=
  LinearMap.codRestrict (tensorCode CA CB).carrier
    ((tensorWordEquiv F A B).toLinearMap.comp
      (TensorProduct.mapIncl CA.carrier CB.carrier)) fun z => by
        induction z with
        | zero => simpa only [map_zero] using (tensorCode CA CB).carrier.zero_mem
        | add x y hx hy =>
            simpa only [map_add] using (tensorCode CA CB).carrier.add_mem hx hy
        | tmul x y =>
            simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
              Submodule.coe_subtype]
            rw [mem_tensorCode]
            constructor
            · intro b
              change (fun a => tensorWordEquiv F A B
                ((x : Word F A) ⊗ₜ[F] (y : Word F B)) (a, b)) ∈ CA.carrier
              simp only [tensorWordEquiv_tmul_apply]
              rw [show (fun a => (x : Word F A) a * (y : Word F B) b) =
                  (y.1 b) • (x : Word F A) by
                funext a
                simp only [Pi.smul_apply, smul_eq_mul, mul_comm]]
              exact CA.carrier.smul_mem (y.1 b) x.2
            · intro a
              change (fun b => tensorWordEquiv F A B
                ((x : Word F A) ⊗ₜ[F] (y : Word F B)) (a, b)) ∈ CB.carrier
              simp only [tensorWordEquiv_tmul_apply]
              rw [show (fun b => (x : Word F A) a * (y : Word F B) b) =
                  (x.1 a) • (y : Word F B) by
                funext b
                simp only [Pi.smul_apply, smul_eq_mul]]
              exact CB.carrier.smul_mem (x.1 a) y.2
theorem tensorCodeTensorMap_injective
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    Function.Injective (tensorCodeTensorMap CA CB) := by
  intro x y hxy
  have hxy' := congrArg Subtype.val hxy
  change tensorWordEquiv F A B
      (TensorProduct.mapIncl CA.carrier CB.carrier x) =
    tensorWordEquiv F A B
      (TensorProduct.mapIncl CA.carrier CB.carrier y) at hxy'
  apply TensorProduct.map_injective_of_flat_flat
      CA.carrier.subtype CB.carrier.subtype
      CA.carrier.injective_subtype CB.carrier.injective_subtype
  exact (tensorWordEquiv F A B).injective hxy'
theorem tensorWordEquiv_rTensor_apply
    {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (C : Submodule F (Word F A)) (z : C ⊗[F] Word F B) (a : A) (b : B) :
    tensorWordEquiv F A B (C.subtype.rTensor (Word F B) z) (a, b) =
      ((TensorProduct.piScalarRight F F C B z b : C) : Word F A) a := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp [LinearMap.rTensor_tmul, tensorWordEquiv_tmul_apply,
        TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, Pi.smul_apply,
        smul_eq_mul, mul_comm]
theorem tensorWordEquiv_lTensor_apply
    {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (C : Submodule F (Word F B)) (z : Word F A ⊗[F] C) (a : A) (b : B) :
    tensorWordEquiv F A B (C.subtype.lTensor (Word F A) z) (a, b) =
      ((TensorProduct.piScalarRight F F C A
          (TensorProduct.comm F (Word F A) C z) a : C) : Word F B) b := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp [LinearMap.lTensor_tmul, tensorWordEquiv_tmul_apply,
        TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, Pi.smul_apply,
        smul_eq_mul]
theorem mem_range_rTensor_of_columns
    {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (C : Submodule F (Word F A)) (x : Word F (A × B))
    (hx : ∀ b, columnRestriction b x ∈ C) :
    (tensorWordEquiv F A B).symm x ∈
      LinearMap.range (C.subtype.rTensor (Word F B)) := by
  let columns : B → C := fun b ↦ ⟨columnRestriction b x, hx b⟩
  let z := (TensorProduct.piScalarRight F F C B).symm columns
  refine ⟨z, ?_⟩
  apply (tensorWordEquiv F A B).injective
  ext ab
  rcases ab with ⟨a, b⟩
  rw [tensorWordEquiv_rTensor_apply]
  simp only [z, LinearEquiv.apply_symm_apply]
  rfl
theorem mem_range_lTensor_of_rows
    {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (C : Submodule F (Word F B)) (x : Word F (A × B))
    (hx : ∀ a, rowRestriction a x ∈ C) :
    (tensorWordEquiv F A B).symm x ∈
      LinearMap.range (C.subtype.lTensor (Word F A)) := by
  let rows : A → C := fun a ↦ ⟨rowRestriction a x, hx a⟩
  let z₀ := (TensorProduct.piScalarRight F F C A).symm rows
  let z := TensorProduct.comm F C (Word F A) z₀
  refine ⟨z, ?_⟩
  apply (tensorWordEquiv F A B).injective
  ext ab
  rcases ab with ⟨a, b⟩
  rw [tensorWordEquiv_lTensor_apply]
  simp only [z, z₀, TensorProduct.comm_comm,
    LinearEquiv.apply_symm_apply]
  rfl
theorem tensorCodeTensorMap_surjective
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    Function.Surjective (tensorCodeTensorMap CA CB) := by
  intro x
  have hx := (mem_tensorCode CA CB x.1).mp x.2
  let xt := (tensorWordEquiv F A B).symm x.1
  have hColumn : xt ∈ LinearMap.range
      (CA.carrier.subtype.rTensor (Word F B)) :=
    mem_range_rTensor_of_columns CA.carrier x.1 hx.1
  have hRow : xt ∈ LinearMap.range
      (CB.carrier.subtype.lTensor (Word F A)) :=
    mem_range_lTensor_of_rows CB.carrier x.1 hx.2
  obtain ⟨y, hy⟩ := hColumn
  have hRowZero : CB.carrier.mkQ.lTensor (Word F A) xt = 0 := by
    rw [← LinearMap.mem_ker, lTensor_mkQ]
    exact hRow
  have hMapZero : TensorProduct.map CA.carrier.subtype CB.carrier.mkQ y = 0 := by
    rw [← LinearMap.lTensor_comp_rTensor]
    simp only [LinearMap.comp_apply, hy, hRowZero]
  have hQuotientZero : CB.carrier.mkQ.lTensor CA.carrier y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap
        CA.carrier.subtype CA.carrier.injective_subtype
    simp only [map_zero]
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
    exact hMapZero
  have hyRange : y ∈ LinearMap.range
      (CB.carrier.subtype.lTensor CA.carrier) := by
    rw [← lTensor_mkQ]
    exact LinearMap.mem_ker.mpr hQuotientZero
  obtain ⟨z, hz⟩ := hyRange
  refine ⟨z, Subtype.ext ?_⟩
  change tensorWordEquiv F A B
      (TensorProduct.mapIncl CA.carrier CB.carrier z) = x.1
  have hambient : TensorProduct.mapIncl CA.carrier CB.carrier z = xt := by
    change TensorProduct.map CA.carrier.subtype CB.carrier.subtype z = xt
    rw [← LinearMap.rTensor_comp_lTensor]
    simp only [LinearMap.comp_apply, hz, hy]
  rw [hambient]
  exact (tensorWordEquiv F A B).apply_symm_apply x.1
noncomputable def tensorCodeTensorEquiv
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    CA.carrier ⊗[F] CB.carrier ≃ₗ[F] (tensorCode CA CB).carrier :=
  LinearEquiv.ofBijective (tensorCodeTensorMap CA CB)
    ⟨tensorCodeTensorMap_injective CA CB,
      tensorCodeTensorMap_surjective CA CB⟩
def HasMinimumDistanceAtLeast
    {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] (code : LinearCode F ι) (distance : Nat) : Prop :=
  ∀ word, word ∈ code.carrier → word ≠ 0 → distance ≤ HammingWeight word
theorem binary_eq_one_of_ne_zero
    (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  apply ZMod.val_injective 2
  rw [ZMod.val_one]
  have hxval : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
  have hxlt : x.val < 2 := x.val_lt
  omega
def binarySupportWord
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (support : Finset ι) : Word (ZMod 2) ι :=
  fun i => if i ∈ support then 1 else 0
@[simp]
theorem hammingSupport_binarySupportWord
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (support : Finset ι) :
    hammingSupport (binarySupportWord support) = support := by
  ext i
  simp [hammingSupport, binarySupportWord]
@[simp]
theorem binarySupportWord_hammingSupport
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (word : Word (ZMod 2) ι) :
    binarySupportWord (hammingSupport word) = word := by
  funext i
  by_cases hi : word i = 0
  · simp [binarySupportWord, hammingSupport, hi]
  · rw [binary_eq_one_of_ne_zero (word i) hi]
    simp only [binarySupportWord, hammingSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, if_pos hi]
abbrev BinaryLowWeightWords
    (ι : Type v) [Fintype ι] (distance : Nat) :=
  {word : Word (ZMod 2) ι // HammingWeight word < distance}
def binaryLowWeightWordsEquivSupports
    (ι : Type v) [Fintype ι] [DecidableEq ι] (distance : Nat) :
    BinaryLowWeightWords ι distance ≃
      Σ weight : Fin distance, Set.powersetCard ι weight.1 where
  toFun word :=
    ⟨⟨HammingWeight word.1, word.2⟩,
      ⟨hammingSupport word.1,
        HammingWeight_eq_card_hammingSupport word.1⟩⟩
  invFun support :=
    ⟨binarySupportWord support.2.1, by
      simp [HammingWeight_eq_card_hammingSupport, support.1.2]⟩
  left_inv word := by
    apply Subtype.ext
    exact binarySupportWord_hammingSupport word.1
  right_inv support := by
    apply Sigma.subtype_ext
    · simp [HammingWeight_eq_card_hammingSupport]
    · exact hammingSupport_binarySupportWord support.2.1
def RandomLocalCodeSample.HasFullRowRank
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Function.Surjective (Matrix.toLin' sample.1) ∧
    Function.Surjective (Matrix.toLin' sample.2)
def fixedRowCombinationMap
    {row col : Type v} [Fintype row]
    (coefficients : row → ZMod 2) :
    Matrix row col (ZMod 2) →ₗ[ZMod 2] Word (ZMod 2) col where
  toFun M := Matrix.vecMul coefficients M
  map_add' M N := Matrix.vecMul_add M N coefficients
  map_smul' scalar M := Matrix.vecMul_smul coefficients scalar M
def linearFiberEquivKer
    {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) (base : V) :
    {x : V // f x = f base} ≃ LinearMap.ker f where
  toFun x := ⟨x.1 - base, by simp [x.2]⟩
  invFun z := ⟨z.1 + base, by simp⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp
def firstRowCombinationFiberEventEquiv
    {row A B : Type v} [Fintype row]
    (coefficients : row → ZMod 2) (target : Word (ZMod 2) A) :
    {sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2) //
        Matrix.vecMul coefficients sample.1 = target} ≃
      {matrix : Matrix row A (ZMod 2) //
        Matrix.vecMul coefficients matrix = target} ×
        Matrix row B (ZMod 2) where
  toFun sample := ⟨⟨sample.1.1, sample.2⟩, sample.1.2⟩
  invFun sample := ⟨⟨sample.1.1, sample.2⟩, sample.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def secondRowCombinationFiberEventEquiv
    {row A B : Type v} [Fintype row]
    (coefficients : row → ZMod 2) (target : Word (ZMod 2) B) :
    {sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2) //
        Matrix.vecMul coefficients sample.2 = target} ≃
      Matrix row A (ZMod 2) ×
        {matrix : Matrix row B (ZMod 2) //
          Matrix.vecMul coefficients matrix = target} where
  toFun sample := ⟨sample.1.1, ⟨sample.1.2, sample.2⟩⟩
  invFun sample := ⟨⟨sample.1, sample.2.1⟩, sample.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def firstDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0})
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Matrix.vecMul index.1.1 sample.1 = index.2.1.1
def firstDistanceBadEventEquiv
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index :
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0}) :
    {sample : RandomLocalCodeSample r A B // firstDistanceBad index sample} ≃
      {matrix : Matrix (ULift.{v} (Fin r)) A (ZMod 2) //
        Matrix.vecMul index.1.1 matrix = index.2.1.1} ×
        Matrix (ULift.{v} (Fin r)) B (ZMod 2) where
  toFun sample := ⟨⟨sample.1.1, sample.2⟩, sample.1.2⟩
  invFun sample := ⟨⟨sample.1.1, sample.2⟩, sample.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def fixedRowDependencyEventEquiv
    {row col : Type v} [Fintype row]
    (coefficients : row → ZMod 2) :
    {M : Matrix row col (ZMod 2) // Matrix.vecMul coefficients M = 0} ≃
      LinearMap.ker (fixedRowCombinationMap (col := col) coefficients) where
  toFun M := ⟨M.1, by
    change Matrix.vecMul coefficients M.1 = 0
    exact M.2⟩
  invFun M := ⟨M.1, by
    exact (show fixedRowCombinationMap coefficients M.1 = 0 from M.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def firstRankDependencyEventEquiv
    {row A B : Type v} [Fintype row]
    (coefficients : row → ZMod 2) :
    {sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2) //
        Matrix.vecMul coefficients sample.1 = 0} ≃
      LinearMap.ker (fixedRowCombinationMap (col := A) coefficients) ×
        Matrix row B (ZMod 2) where
  toFun sample := ⟨⟨sample.1.1, by
    change Matrix.vecMul coefficients sample.1.1 = 0
    exact sample.2⟩, sample.1.2⟩
  invFun sample := ⟨⟨sample.1.1, sample.2⟩, by
    change Matrix.vecMul coefficients sample.1.1 = 0
    exact (show fixedRowCombinationMap coefficients sample.1.1 = 0
      from sample.1.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def secondRankDependencyEventEquiv
    {row A B : Type v} [Fintype row]
    (coefficients : row → ZMod 2) :
    {sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2) //
        Matrix.vecMul coefficients sample.2 = 0} ≃
      Matrix row A (ZMod 2) ×
        LinearMap.ker (fixedRowCombinationMap (col := B) coefficients) where
  toFun sample := ⟨sample.1.1, ⟨sample.1.2, by
    change Matrix.vecMul coefficients sample.1.2 = 0
    exact sample.2⟩⟩
  invFun sample := ⟨⟨sample.1, sample.2.1⟩, by
    change Matrix.vecMul coefficients sample.2.1 = 0
    exact (show fixedRowCombinationMap coefficients sample.2.1 = 0
      from sample.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def rankDependencyBad
    {row A B : Type v} [Fintype row]
    (index : Bool ×
      {coefficients : row → ZMod 2 // coefficients ≠ 0})
    (sample : Matrix row A (ZMod 2) × Matrix row B (ZMod 2)) : Prop :=
  if index.1 then Matrix.vecMul index.2.1 sample.2 = 0
  else Matrix.vecMul index.2.1 sample.1 = 0
def fixedColumnCombinationMap
    {row col : Type v} [Fintype col]
    (target : col → ZMod 2) :
    Matrix row col (ZMod 2) →ₗ[ZMod 2] Word (ZMod 2) row where
  toFun M := Matrix.mulVec M target
  map_add' M N := Matrix.add_mulVec M N target
  map_smul' scalar M := Matrix.smul_mulVec scalar M target
def secondDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0})
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Matrix.mulVec sample.2 index.1.1 = 0
def secondDistanceBadEventEquiv
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : {target : BinaryLowWeightWords B distance // target.1 ≠ 0}) :
    {sample : RandomLocalCodeSample r A B //
      secondDistanceBad (A := A) index sample} ≃
      Matrix (ULift.{v} (Fin r)) A (ZMod 2) ×
        LinearMap.ker
          (fixedColumnCombinationMap
            (row := ULift.{v} (Fin r)) index.1.1) where
  toFun sample := ⟨sample.1.1, ⟨sample.1.2, sample.2⟩⟩
  invFun sample := ⟨⟨sample.1, sample.2.1⟩, sample.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def swapRandomLocalCodeSample
    (r : Nat) (A B : Type v) :
    RandomLocalCodeSample r A B ≃ RandomLocalCodeSample r B A :=
  Equiv.prodComm _ _
abbrev SimultaneousDistanceBadIndex
    (r distance : Nat) (A B : Type v) [Fintype A] [Fintype B] :=
  Sum
    (Bool ×
      {coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0})
    (Sum
      ({coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
        {target : BinaryLowWeightWords A distance // target.1 ≠ 0})
      (Sum
        {target : BinaryLowWeightWords B distance // target.1 ≠ 0}
        (Sum
          {target : BinaryLowWeightWords A distance // target.1 ≠ 0}
          ({coefficients : ULift.{v} (Fin r) → ZMod 2 // coefficients ≠ 0} ×
            {target : BinaryLowWeightWords B distance // target.1 ≠ 0}))))
def simultaneousDistanceBad
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (index : SimultaneousDistanceBadIndex r distance A B)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  match index with
  | Sum.inl rankIndex =>
      rankDependencyBad rankIndex sample
  | Sum.inr (Sum.inl firstIndex) =>
      firstDistanceBad (B := B) firstIndex sample
  | Sum.inr (Sum.inr (Sum.inl secondIndex)) =>
      secondDistanceBad (r := r) (A := A) secondIndex sample
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl firstDualIndex))) =>
      secondDistanceBad (r := r) (A := B) firstDualIndex
        (swapRandomLocalCodeSample r A B sample)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr secondDualIndex))) =>
      firstDistanceBad (B := A) secondDualIndex
        (swapRandomLocalCodeSample r A B sample)
def lightRows
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (cutoff : Nat) : Finset A := by
  classical
  exact Finset.univ.filter fun a =>
    ∃ b : B,
      b ∉ (Finset.univ.filter fun b : B =>
        cutoff < HammingWeight (columnRestriction b x)) ∧
      x (a, b) ≠ 0
def lowWeightColumnMatricesEquiv
    (A B : Type v) [Fintype A] [Fintype B] (distance : Nat) :
    {x : Word (ZMod 2) (A × B) //
      ∀ b : B, HammingWeight (columnRestriction b x) < distance} ≃
      (B → BinaryLowWeightWords A distance) where
  toFun x b := ⟨columnRestriction b x.1, x.2 b⟩
  invFun columns := ⟨fun i => (columns i.2).1 i.1, by
    intro b
    exact (columns b).2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    obtain ⟨a, b⟩ := i
    rfl
  right_inv columns := by
    funext b
    apply Subtype.ext
    funext a
    rfl
abbrev PuncturedLowWeightMatrixFamily
    (A B : Type v) [Fintype A] [Fintype B]
    (p distance : Nat) :=
  Σ removed : (Finset.univ : Finset B).powersetCard p,
    {x : Word (ZMod 2) (A × KeptCoordinate removed.1) //
      ∀ b : KeptCoordinate removed.1,
        HammingWeight (columnRestriction b x) < distance}
def restrictCheckMap
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col)) :
    (Word (ZMod 2) col →ₗ[ZMod 2] Word (ZMod 2) row) →ₗ[ZMod 2]
      (testSpace →ₗ[ZMod 2] Word (ZMod 2) row) where
  toFun check := check.comp testSpace.subtype
  map_add' _ _ := by ext word coordinate; rfl
  map_smul' _ _ := by ext word coordinate; rfl
def matrixRestrictCheckKernelEquiv
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col)) :
    {matrix : Matrix row col (ZMod 2) //
      restrictCheckMap testSpace (Matrix.toLin' matrix) = 0} ≃
      LinearMap.ker (restrictCheckMap (row := row) testSpace) where
  toFun matrix := ⟨Matrix.toLin' matrix.1, matrix.2⟩
  invFun check := ⟨Matrix.toLin'.symm check.1, by
    simpa only [LinearEquiv.apply_symm_apply, LinearMap.mem_ker] using check.2⟩
  left_inv matrix := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply Matrix.toLin' matrix.1
  right_inv check := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply Matrix.toLin' check.1
def quotientCheckRestriction
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row)) :
    Matrix row col (ZMod 2) →ₗ[ZMod 2]
      (testSpace →ₗ[ZMod 2] (Word (ZMod 2) row ⧸ deletedSyndromes)) where
  toFun matrix :=
    (deletedSyndromes.mkQ.comp (Matrix.toLin' matrix)).comp testSpace.subtype
  map_add' matrix₁ matrix₂ := by
    ext word
    simp
  map_smul' scalar matrix := by
    ext word
    simp
theorem quotientCheckRestriction_eq_zero_iff
    {row col : Type v} [Fintype row] [Fintype col]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) col))
    (deletedSyndromes : Submodule (ZMod 2) (Word (ZMod 2) row))
    (matrix : Matrix row col (ZMod 2)) :
    quotientCheckRestriction testSpace deletedSyndromes matrix = 0 ↔
      ∀ word : testSpace, Matrix.mulVec matrix word.1 ∈ deletedSyndromes := by
  rw [LinearMap.ext_iff]
  change (∀ word : testSpace,
    deletedSyndromes.mkQ (Matrix.toLin' matrix word.1) = 0) ↔ _
  simp only [Matrix.toLin'_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
def splitPunctureCheckEventEquiv
    {row deleted kept : Type v}
    [Fintype row] [Fintype deleted] [Fintype kept]
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) kept)) :
    {sample : Matrix row deleted (ZMod 2) × Matrix row kept (ZMod 2) //
      ∀ word : testSpace, Matrix.mulVec sample.2 word.1 ∈
        LinearMap.range (Matrix.toLin' sample.1)} ≃
      Σ deletedMatrix : Matrix row deleted (ZMod 2),
        LinearMap.ker (quotientCheckRestriction testSpace
          (LinearMap.range (Matrix.toLin' deletedMatrix))) where
  toFun sample := ⟨sample.1.1, ⟨sample.1.2,
    (quotientCheckRestriction_eq_zero_iff testSpace
      (LinearMap.range (Matrix.toLin' sample.1.1)) sample.1.2).mpr sample.2⟩⟩
  invFun sample := ⟨⟨sample.1, sample.2.1⟩,
    (quotientCheckRestriction_eq_zero_iff testSpace
      (LinearMap.range (Matrix.toLin' sample.1)) sample.2.1).mp sample.2.2⟩
  left_inv sample := by
    apply Subtype.ext
    rfl
  right_inv sample := by
    cases sample
    rfl
theorem mulVec_deleted_add_kept
    {row col : Type v} [Fintype row] [Fintype col]
    (matrix : Matrix row col (ZMod 2)) (removed : Finset col)
    (word : Word (ZMod 2) col) :
    Matrix.mulVec matrix word =
      Matrix.mulVec (matrix.submatrix id (fun i : {i // i ∈ removed} => i.1))
        (fun i => word i.1) +
      Matrix.mulVec (matrix.submatrix id (fun i : {i // i ∉ removed} => i.1))
        (fun i => word i.1) := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.submatrix_apply, id_eq]
  calc
    _ = (∑ i ∈ removed, matrix r i * word i) +
        (∑ i ∈ removedᶜ, matrix r i * word i) :=
      (Finset.sum_add_sum_compl removed (fun i => matrix r i * word i)).symm
    _ = _ := congrArg₂ (· + ·)
      (Finset.sum_subtype removed (by simp) (fun i => matrix r i * word i))
      (Finset.sum_subtype removedᶜ (by simp) (fun i => matrix r i * word i))
theorem retained_word_exists_zero_syndrome_iff
    {row col : Type v} [Fintype row] [Fintype col]
    (matrix : Matrix row col (ZMod 2)) (removed : Finset col)
    (word : Word (ZMod 2) {i // i ∉ removed}) :
    (∃ fullWord : Word (ZMod 2) col, Matrix.mulVec matrix fullWord = 0 ∧
      (fun i : {i // i ∉ removed} => fullWord i.1) = word) ↔
    Matrix.mulVec (matrix.submatrix id (fun i : {i // i ∉ removed} => i.1)) word ∈
      LinearMap.range (Matrix.toLin'
        (matrix.submatrix id (fun i : {i // i ∈ removed} => i.1))) := by
  constructor
  · rintro ⟨fullWord, hZero, hKept⟩
    rw [mulVec_deleted_add_kept matrix removed, hKept] at hZero
    refine ⟨-(fun i : {i // i ∈ removed} => fullWord i.1), ?_⟩
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_neg] using
      (eq_neg_of_add_eq_zero_right hZero).symm
  · rintro ⟨deletedWord, hDeleted⟩
    let fullWord : Word (ZMod 2) col := fun i =>
      if hi : i ∈ removed then -deletedWord ⟨i, hi⟩ else word ⟨i, hi⟩
    have hKept : (fun i : {i // i ∉ removed} => fullWord i.1) = word := by
      funext i
      simp [fullWord, i.2]
    have hRemoved : (fun i : {i // i ∈ removed} => fullWord i.1) = -deletedWord := by
      funext i
      simp [fullWord, i.2]
    refine ⟨fullWord, ?_, hKept⟩
    rw [mulVec_deleted_add_kept matrix removed, hKept, hRemoved, Matrix.mulVec_neg]
    change -Matrix.toLin' _ deletedWord + _ = 0
    rw [hDeleted, neg_add_cancel]
theorem mem_punctured_parityCheckKernelCode_iff
    {row col : Type v} [Fintype row] [Fintype col]
    (matrix : Matrix row col (ZMod 2)) (removed : Finset col)
    (word : Word (ZMod 2) (KeptCoordinate removed)) :
    word ∈ (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier ↔
      Matrix.mulVec (matrix.submatrix id (fun i : KeptCoordinate removed => i.1)) word ∈
        LinearMap.range (Matrix.toLin'
          (matrix.submatrix id (fun i : {i // i ∈ removed} => i.1))) := by
  rw [mem_puncturedCode]
  change (∃ fullWord : Word (ZMod 2) col, Matrix.mulVec matrix fullWord = 0 ∧
    (fun i : KeptCoordinate removed => fullWord i.1) = word) ↔ _
  exact retained_word_exists_zero_syndrome_iff matrix removed word
def splitCheckMatrixEquiv
    {row col : Type v} [Fintype row] [Fintype col] (removed : Finset col) :
    Matrix row col (ZMod 2) ≃
      Matrix row {i // i ∈ removed} (ZMod 2) ×
        Matrix row (KeptCoordinate removed) (ZMod 2) where
  toFun matrix := ⟨matrix.submatrix id (fun i => i.1),
    matrix.submatrix id (fun i => i.1)⟩
  invFun blocks r i :=
    if hi : i ∈ removed then blocks.1 r ⟨i, hi⟩ else blocks.2 r ⟨i, hi⟩
  left_inv matrix := by
    funext r i
    by_cases hi : i ∈ removed <;> simp [hi, Matrix.submatrix]
  right_inv blocks := by
    apply Prod.ext
    · funext r i
      simp [Matrix.submatrix, i.2]
    · funext r i
      simp [Matrix.submatrix, i.2]
def puncturedCheckMatrixEventEquiv
    {row col : Type v} [Fintype row] [Fintype col]
    (removed : Finset col)
    (testSpace : Submodule (ZMod 2) (Word (ZMod 2) (KeptCoordinate removed))) :
    {matrix : Matrix row col (ZMod 2) // ∀ word : testSpace,
      word.1 ∈ (puncturedCode
        (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} ≃
    {sample : Matrix row {i // i ∈ removed} (ZMod 2) ×
        Matrix row (KeptCoordinate removed) (ZMod 2) //
      ∀ word : testSpace, Matrix.mulVec sample.2 word.1 ∈
        LinearMap.range (Matrix.toLin' sample.1)} := by
  refine (splitCheckMatrixEquiv removed).subtypeEquiv ?_
  intro matrix
  exact forall_congr' fun word => mem_punctured_parityCheckKernelCode_iff matrix removed word.1
def supportedWordSpace
    {A : Type v} [Fintype A] (support : Finset A) :
    Submodule (ZMod 2) (Word (ZMod 2) A) where
  carrier := {word | ∀ a, a ∉ support → word a = 0}
  zero_mem' := by intro a _; rfl
  add_mem' := by
    intro x y hx hy a ha
    simp only [Pi.add_apply, hx a ha, hy a ha, zero_add]
  smul_mem' := by
    intro scalar x hx a ha
    simp only [Pi.smul_apply, hx a ha, smul_zero]
def activeRowSet
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) : Finset A :=
  Finset.univ.filter fun a => rowRestriction a x ≠ 0
def activeColumnSet
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) : Finset B :=
  Finset.univ.filter fun b => columnRestriction b x ≠ 0
def retainedMatrixEventEquiv
    {row col : Type v} [Fintype row] [Fintype col] (removed : Finset col)
    (event : Matrix row (KeptCoordinate removed) (ZMod 2) → Prop) :
    {matrix : Matrix row col (ZMod 2) //
      event (matrix.submatrix id (fun i : KeptCoordinate removed => i.1))} ≃
      Matrix row {i // i ∈ removed} (ZMod 2) ×
        {retained : Matrix row (KeptCoordinate removed) (ZMod 2) // event retained} where
  toFun matrix := ⟨(splitCheckMatrixEquiv removed matrix.1).1,
    ⟨(splitCheckMatrixEquiv removed matrix.1).2, matrix.2⟩⟩
  invFun blocks := ⟨(splitCheckMatrixEquiv removed).symm (blocks.1, blocks.2.1), by
    change event ((splitCheckMatrixEquiv removed)
      ((splitCheckMatrixEquiv removed).symm (blocks.1, blocks.2.1))).2
    rw [Equiv.apply_symm_apply]
    exact blocks.2.2⟩
  left_inv matrix := by
    apply Subtype.ext
    exact (splitCheckMatrixEquiv removed).symm_apply_apply matrix.1
  right_inv blocks := by
    apply Prod.ext
    · change ((splitCheckMatrixEquiv removed)
        ((splitCheckMatrixEquiv removed).symm (blocks.1, blocks.2.1))).1 = blocks.1
      exact congrArg Prod.fst
        ((splitCheckMatrixEquiv removed).apply_symm_apply (blocks.1, blocks.2.1))
    · apply Subtype.ext
      change ((splitCheckMatrixEquiv removed)
        ((splitCheckMatrixEquiv removed).symm (blocks.1, blocks.2.1))).2 = blocks.2.1
      exact congrArg Prod.snd
        ((splitCheckMatrixEquiv removed).apply_symm_apply (blocks.1, blocks.2.1))
theorem rows_mem_iff_span_contained
    {R B : Type v} [Fintype B]
    (rows : R → Word (ZMod 2) B) (code : Submodule (ZMod 2) (Word (ZMod 2) B)) :
    (∀ r, rows r ∈ code) ↔
      ∀ word : Submodule.span (ZMod 2) (Set.range rows), word.1 ∈ code := by
  constructor
  · intro hRows word
    apply (Submodule.span_le.mpr ?_) word.2
    rintro _ ⟨r, rfl⟩
    exact hRows r
  · intro hSpan r
    exact hSpan ⟨rows r, Submodule.subset_span (Set.mem_range_self r)⟩
def puncturedCheckRowsEventEquiv
    {R B T : Type v} [Fintype B] [Fintype T]
    (removed : Finset B) (rows : R → Word (ZMod 2) (KeptCoordinate removed)) :
    {matrix : Matrix T B (ZMod 2) // ∀ r, rows r ∈
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} ≃
    {matrix : Matrix T B (ZMod 2) //
      ∀ word : Submodule.span (ZMod 2) (Set.range rows), word.1 ∈
        (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed).carrier} := by
  refine (Equiv.refl (Matrix T B (ZMod 2))).subtypeEquiv ?_
  intro matrix
  exact rows_mem_iff_span_contained rows _
def combinedPuncture {B : Type v} [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed)) : Finset B :=
  removed ∪ more.image Subtype.val
theorem mem_combinedPuncture_iff
    {B : Type v} [Fintype B] (removed : Finset B)
    (more : Finset (KeptCoordinate removed)) (b : KeptCoordinate removed) :
    b.1 ∈ combinedPuncture removed more ↔ b ∈ more := by
  classical
  simp only [combinedPuncture, Finset.mem_union, b.2, false_or]
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨c, hc, hcb⟩
    have hEq : c = b := Subtype.ext hcb
    simpa only [hEq] using hc
  · intro h
    exact Finset.mem_image.mpr ⟨b, h, rfl⟩
def nestedKeptCoordinateEquiv
    {B : Type v} [Fintype B] (removed : Finset B)
    (more : Finset (KeptCoordinate removed)) :
    KeptCoordinate more ≃ KeptCoordinate (combinedPuncture removed more) where
  toFun b := ⟨b.1.1, by
    intro h
    exact b.2 ((mem_combinedPuncture_iff removed more b.1).mp h)⟩
  invFun b := ⟨⟨b.1, by
    intro h
    exact b.2 (Finset.mem_union_left _ h)⟩, by
    intro h
    apply b.2
    exact (mem_combinedPuncture_iff removed more _).mpr h⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    rfl
def canonicalNestedRetainedWord
    {A B : Type v} [Fintype A] [Fintype B]
    (removed : Finset B) (more : Finset (KeptCoordinate removed))
    (retained : Word (ZMod 2) (A × KeptCoordinate more)) :
    Word (ZMod 2) (A × KeptCoordinate (combinedPuncture removed more)) :=
  fun ab => retained (ab.1, (nestedKeptCoordinateEquiv removed more).symm ab.2)
abbrev AllPuncturedLightMatrixFamily
    (A B : Type v) [Fintype A] [Fintype B] (cutoff : Nat) :=
  Σ removed : Finset B, {x : Word (ZMod 2) (A × KeptCoordinate removed) //
    ∀ b : KeptCoordinate removed, HammingWeight (columnRestriction b x) < cutoff + 1}
abbrev LightRetainedCompletionEvent
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (cutoff : Nat)
    (i : AllPuncturedLightMatrixFamily A B cutoff) (matrix : Matrix T B (ZMod 2)) : Prop :=
  ∃ x : Word (ZMod 2) (A × B),
    x ∈ (dualTensorCode CA (parityCheckKernelCode (Matrix.toLin' matrix))).carrier ∧
    (fun ab : A × KeptCoordinate i.1 => x (ab.1, ab.2.1)) = i.2.1
abbrev ValidLightRetainedIndex
    {A B : Type v} [Fintype A] [Fintype B] (cutoff p rank : Nat)
    (i : AllPuncturedLightMatrixFamily A B cutoff) : Prop :=
  i.1.card ≤ p ∧ rank ≤ Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2)
      ((Finset.univ.image fun b : KeptCoordinate i.1 => columnRestriction b i.2.1) :
        Set (Word (ZMod 2) A)))
structure NestedLightRetainedIndex
    (A B : Type v) [Fintype A] [Fintype B] (removed : Finset B) (cutoff : Nat) where
  more : Finset (KeptCoordinate removed)
  retained : Word (ZMod 2) (A × KeptCoordinate more)
  light : ∀ b : KeptCoordinate more, HammingWeight (columnRestriction b retained) < cutoff + 1
def nestedLightRetainedIndexEquiv
    (A B : Type v) [Fintype A] [Fintype B] (removed : Finset B) (cutoff : Nat) :
    NestedLightRetainedIndex A B removed cutoff ≃
      AllPuncturedLightMatrixFamily A (KeptCoordinate removed) cutoff where
  toFun i := ⟨i.more, i.retained, i.light⟩
  invFun i := ⟨i.1, i.2.1, i.2.2⟩
  left_inv i := by cases i; rfl
  right_inv i := by rcases i with ⟨more, retained, light⟩; rfl
instance nestedLightRetainedIndexFinite
    (A B : Type v) [Fintype A] [Fintype B] (removed : Finset B) (cutoff : Nat) :
    Finite (NestedLightRetainedIndex A B removed cutoff) :=
  Finite.of_equiv _ (nestedLightRetainedIndexEquiv A B removed cutoff).symm
abbrev ValidNestedLightRetainedIndex
    {A B : Type v} [Fintype A] [Fintype B] (removed : Finset B) (cutoff p rank : Nat)
    (i : NestedLightRetainedIndex A B removed cutoff) : Prop :=
  i.more.card ≤ p ∧ rank ≤ Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2)
      ((Finset.univ.image fun b : KeptCoordinate i.more => columnRestriction b i.retained) :
        Set (Word (ZMod 2) A)))
abbrev PuncturedLightRetainedCompletionEvent
    {A B T : Type v} [Fintype A] [Fintype B] [Fintype T]
    (CA : LinearCode (ZMod 2) A) (removed : Finset B) (cutoff : Nat)
    (i : NestedLightRetainedIndex A B removed cutoff)
    (matrix : Matrix T B (ZMod 2)) : Prop :=
  ∃ x : Word (ZMod 2) (A × KeptCoordinate removed),
    x ∈ (dualTensorCode CA
      (puncturedCode (parityCheckKernelCode (Matrix.toLin' matrix)) removed)).carrier ∧
    (fun ab : A × KeptCoordinate i.more => x (ab.1, ab.2.1)) = i.retained
abbrev MatchingPunctureIndex
    (A B : Type v) [Fintype A] [Fintype B] (q : Nat) :=
  Σ size : Fin (q + 1),
    {removedA : Finset A // removedA.card = size.1} ×
      {removedB : Finset B // removedB.card = size.1}
def productEventFiberEquiv
    {α β : Type v} (event : α × β → Prop) :
    {sample : α × β // event sample} ≃
      Σ first : α, {second : β // event (first, second)} where
  toFun sample := ⟨sample.1.1, sample.1.2, sample.2⟩
  invFun sample := ⟨(sample.1, sample.2.1), sample.2.2⟩
  left_inv sample := by
    apply Subtype.ext
    rfl
  right_inv sample := by
    cases sample
    rfl
def transposeTensorWord
    {A B : Type v} (x : Word (ZMod 2) (A × B)) : Word (ZMod 2) (B × A) :=
  fun coordinate => x (coordinate.2, coordinate.1)
theorem transposeTensorWord_involutive
    {A B : Type v} (x : Word (ZMod 2) (A × B)) :
    transposeTensorWord (transposeTensorWord x) = x := rfl
theorem hammingWeight_transposeTensorWord
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) :
    HammingWeight (transposeTensorWord x) = HammingWeight x := by
  classical
  unfold HammingWeight
  apply Finset.card_bij (fun coordinate _ => (coordinate.2, coordinate.1))
  · intro coordinate hCoordinate
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hCoordinate).2⟩
  · intro first hFirst second hSecond hEqual
    exact Prod.ext (congrArg Prod.snd hEqual) (congrArg Prod.fst hEqual)
  · intro coordinate hCoordinate
    exact ⟨(coordinate.2, coordinate.1),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hCoordinate).2⟩, rfl⟩
theorem mem_dualTensorCode_transposeTensorWord
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    {x : Word (ZMod 2) (A × B)} (hx : x ∈ (dualTensorCode CA CB).carrier) :
    transposeTensorWord x ∈ (dualTensorCode CB CA).carrier := by
  rcases Submodule.mem_sup.mp hx with ⟨columnPart, hColumn, rowPart, hRow, hSum⟩
  apply Submodule.mem_sup.mpr
  refine ⟨transposeTensorWord rowPart, ?_, transposeTensorWord columnPart, ?_, ?_⟩
  · change ∀ a, columnRestriction a (transposeTensorWord rowPart) ∈ CB.carrier
    intro a
    exact hRow a
  · change ∀ b, rowRestriction b (transposeTensorWord columnPart) ∈ CA.carrier
    intro b
    exact hColumn b
  · ext coordinate
    simpa [transposeTensorWord, add_comm] using
      congrArg (fun z : Word (ZMod 2) (A × B) => z (coordinate.2, coordinate.1)) hSum
theorem supportCovered_transposeTensorWord
    {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (rows : Finset A) (columns : Finset B)
    (hCover : SupportCovered x rows columns) :
    SupportCovered (transposeTensorWord x) columns rows := by
  intro coordinate hCoordinate
  have hOriginal : (coordinate.2, coordinate.1) ∈ hammingSupport x := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hCoordinate).2⟩
  have hCovered := hCover hOriginal
  rcases Finset.mem_union.mp hCovered with hRows | hColumns
  · exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_product.mpr ⟨Finset.mem_univ _, (Finset.mem_product.mp hRows).1⟩))
  · exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_product.mpr ⟨(Finset.mem_product.mp hColumns).2, Finset.mem_univ _⟩))
theorem isRobust_swap
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (w : Nat)
    (hRobust : IsRobust CA CB w) : IsRobust CB CA w := by
  intro distanceB distanceA hB hA x hx hWeight
  have hTransposed := mem_dualTensorCode_transposeTensorWord CB CA hx
  have hTransposedWeight := hammingWeight_transposeTensorWord x
  obtain ⟨rows, columns, hCover, hRows, hColumns⟩ :=
    hRobust distanceA distanceB hA hB (transposeTensorWord x) hTransposed
      (by simpa only [hTransposedWeight] using hWeight)
  refine ⟨columns, rows, ?_, ?_, ?_⟩
  · simpa only [transposeTensorWord_involutive] using
      supportCovered_transposeTensorWord (transposeTensorWord x) rows columns hCover
  · simpa only [hTransposedWeight] using hColumns
  · simpa only [hTransposedWeight] using hRows
theorem isRobustWithPunctureResistance_swap
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (w q : Nat)
    (hRobust : IsRobustWithPunctureResistance CA CB w q) :
    IsRobustWithPunctureResistance CB CA w q := by
  intro removedB removedA hMatching hCard
  exact isRobust_swap (puncturedCode CA removedA) (puncturedCode CB removedB) w
    (hRobust removedA removedB hMatching.symm (by omega))
def robustFailureSwapEquiv
    {α β : Type u} {A B : Type v} [Fintype A] [Fintype B]
    (CA : α → LinearCode (ZMod 2) A) (CB : β → LinearCode (ZMod 2) B)
    (distanceA distanceB w q : Nat) :
    {sample : α × β //
      HasMinimumDistanceAtLeast (CA sample.1) distanceA ∧
      HasMinimumDistanceAtLeast (CB sample.2) distanceB ∧
      ¬ IsRobustWithPunctureResistance (CA sample.1) (CB sample.2) w q} ≃
    {sample : β × α //
      HasMinimumDistanceAtLeast (CB sample.1) distanceB ∧
      HasMinimumDistanceAtLeast (CA sample.2) distanceA ∧
      ¬ IsRobustWithPunctureResistance (CB sample.1) (CA sample.2) w q} where
  toFun sample := ⟨(sample.1.2, sample.1.1),
    sample.2.2.1, sample.2.1, fun hRobust =>
      sample.2.2.2 (isRobustWithPunctureResistance_swap _ _ w q hRobust)⟩
  invFun sample := ⟨(sample.1.2, sample.1.1),
    sample.2.2.1, sample.2.1, fun hRobust =>
      sample.2.2.2 (isRobustWithPunctureResistance_swap _ _ w q hRobust)⟩
  left_inv sample := by
    apply Subtype.ext
    rfl
  right_inv sample := by
    apply Subtype.ext
    rfl
def distanceGoodPunctureFailure
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (distance w q : Nat) (dualSide : Bool) (sample : RandomLocalCodeSample r A B) : Prop :=
  HasMinimumDistanceAtLeast sample.codeA distance ∧
    HasMinimumDistanceAtLeast sample.codeB distance ∧
    HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
    HasMinimumDistanceAtLeast sample.codeB.dual distance ∧
    match dualSide with
    | false => ¬ IsRobustWithPunctureResistance sample.codeA sample.codeB w q
    | true => ¬ IsRobustWithPunctureResistance sample.codeA.dual sample.codeB.dual w q
def GoodLocalCodeEvent
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (dimensionA dimensionB distanceThreshold robustness punctures : Nat)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Dimension sample.codeA = dimensionA ∧
    Dimension sample.codeB = dimensionB ∧
    HasMinimumDistanceAtLeast sample.codeA distanceThreshold ∧
    HasMinimumDistanceAtLeast sample.codeB distanceThreshold ∧
    HasMinimumDistanceAtLeast sample.codeA.dual distanceThreshold ∧
    HasMinimumDistanceAtLeast sample.codeB.dual distanceThreshold ∧
    IsRobustWithPunctureResistance
      sample.codeA sample.codeB robustness punctures ∧
    IsRobustWithPunctureResistance
      sample.codeA.dual sample.codeB.dual robustness punctures
def goodLocalCodeBad
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (distanceThreshold robustness punctures : Nat)
    (index : Sum (SimultaneousDistanceBadIndex r distanceThreshold A B) Bool)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  match index with
  | .inl i => simultaneousDistanceBad i sample
  | .inr dualSide =>
      distanceGoodPunctureFailure distanceThreshold robustness punctures dualSide sample
def distanceFailureCountBound (r Delta distance : Nat) : Nat :=
  2 * (2 ^ r - 1) * (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
    2 * (((2 ^ r - 1) * (∑ weight ∈ Finset.range distance,
      Nat.choose Delta weight)) * (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
    2 * ((∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
      (2 ^ (r * Delta) * 2 ^ (r * Delta - r)))
def HasRealMinimumDistanceAtLeast
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I) (distance : ℝ) : Prop :=
  ∀ x, x ∈ C.carrier → x ≠ 0 → distance ≤ (HammingWeight x : ℝ)
def IsRealRobust
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (weight : ℝ) : Prop :=
  ∀ dA dB, MinimumDistance CA dA → MinimumDistance CB dB →
    ∀ x, x ∈ (dualTensorCode CA CB).carrier → (HammingWeight x : ℝ) ≤ weight →
      ∃ rows : Finset A, ∃ columns : Finset B,
        SupportCovered x rows columns ∧
          rows.card ≤ HammingWeight x / dB ∧
          columns.card ≤ HammingWeight x / dA
def IsRealRobustWithPunctureResistance
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (weight punctures : ℝ) : Prop :=
  ∀ removedA : Finset A, ∀ removedB : Finset B,
    removedA.card = removedB.card → (removedA.card : ℝ) ≤ punctures →
      IsRealRobust (puncturedCode CA removedA) (puncturedCode CB removedB) weight
def SourceRealLocalCodeEvent
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho : ℝ) (n : Nat) (distance weight punctures : ℝ)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  0 < Dimension sample.codeA ∧
    (Dimension sample.codeA : ℝ) ≤ rho * n ∧
    Dimension sample.codeB = n - Dimension sample.codeA ∧
    HasRealMinimumDistanceAtLeast sample.codeA distance ∧
    HasRealMinimumDistanceAtLeast sample.codeB distance ∧
    HasRealMinimumDistanceAtLeast sample.codeA.dual distance ∧
    HasRealMinimumDistanceAtLeast sample.codeB.dual distance ∧
    IsRealRobustWithPunctureResistance sample.codeA sample.codeB weight punctures ∧
    IsRealRobustWithPunctureResistance sample.codeA.dual sample.codeB.dual weight punctures
def square {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g : G) (side : Bool) (a : A) (b : B) :
    Finset (G × Bool) :=
  {(g, side), (L a * g, !side), (g * R b, !side), (L a * g * R b, side)}
theorem square_opposite_vertex {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g h : G) (a : A) (b : B) :
    (h, true) ∈ square L R g false a b ↔ h = L a * g ∨ h = g * R b := by
  simp [square]
theorem square_base_vertex {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g h : G) (a : A) (b : B) :
    (g, false) ∈ square L R h true a b ↔ g = L a * h ∨ g = h * R b := by
  simp [square]
theorem square_opposite_vertex_general {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g h : G) (side : Bool) (a : A) (b : B) :
    (h, !side) ∈ square L R g side a b ↔ h = L a * g ∨ h = g * R b := by
  cases side <;> simp [square]
theorem square_link_injective {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (side : Bool) :
    Function.Injective (fun ab : A × B => square L R g side ab.1 ab.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hs
  change square L R g side a b = square L R g side c d at hs
  have ha : (L a * g, !side) ∈ square L R g side c d := by
    rw [← hs]
    exact (square_opposite_vertex_general L R g (L a * g) side a b).2 (Or.inl rfl)
  have hb : (g * R b, !side) ∈ square L R g side c d := by
    rw [← hs]
    exact (square_opposite_vertex_general L R g (g * R b) side a b).2 (Or.inr rfl)
  have hac : a = c := by
    rcases (square_opposite_vertex_general L R g (L a * g) side c d).1 ha with h | h
    · exact hL (mul_right_cancel h)
    · exact (hTNC g a d h).elim
  have hbd : b = d := by
    rcases (square_opposite_vertex_general L R g (g * R b) side c d).1 hb with h | h
    · exact (hTNC g c b h.symm).elim
    · exact hR (mul_left_cancel h)
  exact Prod.ext hac hbd
theorem square_rebase_left {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (g : G) (side : Bool) (a : A) (b : B) :
    square L R g side a b = square L R (L a * g) (!side) (invA a) b := by
  ext vertex
  cases side <;>
    simp only [square, hLA, inv_mul_cancel_left, Bool.not_false, Bool.not_true,
      Finset.mem_insert, Finset.mem_singleton] <;> tauto
theorem square_rebase_right {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (invB : Equiv.Perm B)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (g : G) (side : Bool) (a : A) (b : B) :
    square L R g side a b = square L R (g * R b) (!side) a (invB b) := by
  ext vertex
  cases side <;>
    simp only [square, hRB, mul_assoc, mul_inv_cancel, mul_one,
      Bool.not_false, Bool.not_true, Finset.mem_insert, Finset.mem_singleton] <;> tauto
theorem square_same_side_vertices {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g : G) (side : Bool) (a : A) (b : B) :
    (square L R g side a b).filter (fun vertex => vertex.2 = side) =
      {(g, side), (L a * g * R b, side)} := by
  ext ⟨h, t⟩
  cases side <;> cases t <;> simp [square]
theorem square_opposite_side_vertices {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (g : G) (side : Bool) (a : A) (b : B) :
    (square L R g side a b).filter (fun vertex => vertex.2 = !side) =
      {(L a * g, !side), (g * R b, !side)} := by
  ext ⟨h, t⟩
  cases side <;> cases t <;> simp [square]
theorem square_each_side_card {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (invB : Equiv.Perm B)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (side t : Bool) (a : A) (b : B) :
    ((square L R g side a b).filter (fun vertex => vertex.2 = t)).card = 2 := by
  have hdiag : g ≠ L a * g * R b := by
    intro heq
    apply hTNC g a (invB b)
    rw [hRB]
    calc
      L a * g = (L a * g * R b) * (R b)⁻¹ := by simp [mul_assoc]
      _ = g * (R b)⁻¹ := by rw [← heq]
  have hsame : ((square L R g side a b).filter (fun vertex => vertex.2 = side)).card = 2 := by
    rw [square_same_side_vertices]
    apply Finset.card_pair
    intro heq
    exact hdiag (congrArg Prod.fst heq)
  have hopposite : ((square L R g side a b).filter (fun vertex => vertex.2 = !side)).card = 2 := by
    rw [square_opposite_side_vertices]
    apply Finset.card_pair
    intro heq
    exact hTNC g a b (congrArg Prod.fst heq)
  cases side <;> cases t
  · exact hsame
  · exact hopposite
  · exact hopposite
  · exact hsame
theorem square_overlap_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g h : G) (a c : A) (b d : B) :
    square L R g false a b = square L R h true c d ↔
      (h = L a * g ∧ c = invA a ∧ d = b) ∨
      (h = g * R b ∧ c = a ∧ d = invB b) := by
  constructor
  · intro hs
    have hh : (h, true) ∈ square L R g false a b := by
      rw [hs]
      simp [square]
    have hg : (g, false) ∈ square L R h true c d := by
      rw [← hs]
      simp [square]
    rcases (square_opposite_vertex L R g h a b).mp hh with ha | hb
    · subst h
      have hcg : g = L c * (L a * g) := by
        rcases (square_base_vertex L R g (L a * g) c d).mp hg with hc | hd
        · exact hc
        · have hbad : L a * g = g * R (invB d) := by
            rw [hRB]
            calc
              L a * g = ((L a * g) * R d) * (R d)⁻¹ := by simp [mul_assoc]
              _ = g * (R d)⁻¹ := by rw [← hd]
          exact (hTNC g a (invB d) hbad).elim
      have hc : c = invA a := by
        apply hL
        rw [hLA]
        calc
          L c = (L c * (L a * g)) * g⁻¹ * (L a)⁻¹ := by simp [mul_assoc]
          _ = (L a)⁻¹ := by rw [← hcg]; simp
      have hgb : (g * R b, true) ∈ square L R (L a * g) true c d := by
        rw [← hs]
        simp [square]
      have hbd : g * R b = g * R d := by
        have hmem := hgb
        rw [hc] at hmem
        simp only [square, hLA, inv_mul_cancel_left, Bool.not_true,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
          Bool.true_eq_false, and_false, false_or, and_true] at hmem
        rcases hmem with hbad | heq
        · exact (hTNC g a b hbad.symm).elim
        · exact heq
      exact Or.inl ⟨rfl, hc, (hR (mul_left_cancel hbd)).symm⟩
    · subst h
      have hgd : g = (g * R b) * R d := by
        rcases (square_base_vertex L R g (g * R b) c d).mp hg with hc | hd
        · have hbad : L c * g = g * R (invB b) := by
            rw [hRB]
            calc
              L c * g = (L c * (g * R b)) * (R b)⁻¹ := by simp [mul_assoc]
              _ = g * (R b)⁻¹ := by rw [← hc]
          exact (hTNC g c (invB b) hbad).elim
        · exact hd
      have hd : d = invB b := by
        apply hR
        rw [hRB]
        calc
          R d = (R b)⁻¹ * g⁻¹ * ((g * R b) * R d) := by simp [mul_assoc]
          _ = (R b)⁻¹ := by rw [← hgd]; simp [mul_assoc]
      have hag : (L a * g, true) ∈ square L R (g * R b) true c d := by
        rw [← hs]
        simp [square]
      have hac : L a * g = L c * g := by
        have hmem := hag
        rw [hd] at hmem
        simp only [square, hRB, mul_assoc, mul_inv_cancel, mul_one, Bool.not_true,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
          Bool.true_eq_false, and_false, false_or, and_true] at hmem
        rcases hmem with hbad | heq
        · exact (hTNC g a b hbad).elim
        · exact heq
      exact Or.inr ⟨rfl, (hL (mul_right_cancel hac)).symm, hd⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · ext vertex
      simp only [square, hLA, inv_mul_cancel_left, Bool.not_false, Bool.not_true,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    · ext vertex
      simp only [square, hRB, mul_assoc, mul_inv_cancel, mul_one,
        Bool.not_false, Bool.not_true, Finset.mem_insert, Finset.mem_singleton]
      tauto
abbrev CanonicalSquare {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) :=
  {q : Finset (G × Bool) // ∃ g side a b, q = square L R g side a b}
noncomputable instance cayleySquareFintype {G A B : Type v} [Group G] [Fintype G]
    (L : A → G) (R : B → G) : Fintype (CanonicalSquare L R) := by
  classical
  infer_instance
def canonicalLink {G A B : Type v} [Group G]
    (L : A → G) (R : B → G) (vertex : G × Bool) (ab : A × B) :
    CanonicalSquare L R :=
  ⟨square L R vertex.1 vertex.2 ab.1 ab.2,
    ⟨vertex.1, vertex.2, ab.1, ab.2, rfl⟩⟩
theorem canonicalLink_injective {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) (vertex : G × Bool) :
    Function.Injective (canonicalLink L R vertex) := by
  intro ab cd h
  exact square_link_injective L R hL hR hTNC vertex.1 vertex.2
    (congrArg Subtype.val h)
theorem canonicalLink_incident_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (vertex : G × Bool) (q : CanonicalSquare L R) :
    (∃ ab, canonicalLink L R vertex ab = q) ↔ vertex ∈ q.val := by
  constructor
  · rintro ⟨ab, rfl⟩
    simp [canonicalLink, square]
  · obtain ⟨g, side, a, b, hq⟩ := q.property
    rw [hq]
    intro hv
    simp only [square, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv | hv
    · subst vertex
      refine ⟨(a, b), Subtype.ext ?_⟩
      exact hq.symm
    · subst vertex
      refine ⟨(invA a, b), Subtype.ext ?_⟩
      exact (square_rebase_left L R invA hLA g side a b).symm.trans hq.symm
    · subst vertex
      refine ⟨(a, invB b), Subtype.ext ?_⟩
      exact (square_rebase_right L R invB hRB g side a b).symm.trans hq.symm
    · subst vertex
      refine ⟨(invA a, invB b), Subtype.ext ?_⟩
      have hreb := (square_rebase_left L R invA hLA g side a b).trans
        (square_rebase_right L R invB hRB (L a * g) (!side) (invA a) b)
      simpa only [Bool.not_not, canonicalLink] using hreb.symm.trans hq.symm
theorem canonicalLink_side_degree {G A B : Type v} [Group G] [Fintype G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (q : CanonicalSquare L R) (side : Bool) :
    (Finset.univ.filter fun g => ∃ ab, canonicalLink L R (g, side) ab = q).card = 2 := by
  let vertices := Finset.univ.filter fun g => ∃ ab, canonicalLink L R (g, side) ab = q
  have himage : vertices.image (fun g => (g, side)) =
      q.val.filter (fun vertex => vertex.2 = side) := by
    ext ⟨g, t⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      vertices, Prod.mk.injEq]
    constructor
    · rintro ⟨h, hi, rfl, rfl⟩
      exact ⟨(canonicalLink_incident_iff L R invA invB hLA hRB _ q).1 hi, rfl⟩
    · rintro ⟨hi, rfl⟩
      exact ⟨g, (canonicalLink_incident_iff L R invA invB hLA hRB _ q).2 hi,
        rfl, rfl⟩
  have hinj : Function.Injective (fun g : G => (g, side)) :=
    fun _ _ h => congrArg Prod.fst h
  have hcard := Finset.card_image_of_injective vertices hinj
  rw [himage] at hcard
  obtain ⟨g, t, a, b, hq⟩ := q.property
  rw [← hcard, hq]
  exact square_each_side_card L R invB hRB hTNC g t side a b
def canonicalSquareComplex {G A B : Type v} [Group G]
    [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) :
    LeftRightCayleySquareComplex G A B (CanonicalSquare L R) where
  leftGenerator := L
  rightGenerator := R
  leftInverse := invA
  rightInverse := invB
  leftGenerator_inverse := hLA
  rightGenerator_inverse := hRB
  noConjugacy := hTNC
  link := canonicalLink L R
  link_injective := canonicalLink_injective L R hL hR hTNC
  square_side_degree := by
    intro q side
    have hcard := canonicalLink_side_degree L R invA invB hLA hRB hTNC q side
    convert hcard using 1
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
abbrev CayleySquare {G A B : Type v} [Group G] (L : A → G) (R : B → G) :=
  CanonicalSquare L R
def cayleySquareComplex {G A B : Type v} [Group G]
    [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) :
    LeftRightCayleySquareComplex G A B (CayleySquare L R) :=
  canonicalSquareComplex L R invA invB hL hR hLA hRB hTNC
theorem canonicalLink_overlap_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g h : G) (a c : A) (b d : B) :
    canonicalLink L R (g, false) (a, b) = canonicalLink L R (h, true) (c, d) ↔
      (h = L a * g ∧ c = invA a ∧ d = b) ∨
      (h = g * R b ∧ c = a ∧ d = invB b) := by
  rw [Subtype.ext_iff]
  exact square_overlap_iff L R invA invB hL hR hLA hRB hTNC g h a c b d
theorem canonicalLink_left_overlap_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (a₀ a c : A) (b d : B) :
    canonicalLink L R (g, false) (a, b) =
      canonicalLink L R (L a₀ * g, true) (c, d) ↔
      a = a₀ ∧ c = invA a₀ ∧ d = b := by
  rw [canonicalLink_overlap_iff L R invA invB hL hR hLA hRB hTNC]
  constructor
  · rintro (⟨h, hc, hd⟩ | ⟨h, _, _⟩)
    · have ha : a = a₀ := (hL (mul_right_cancel h)).symm
      subst a
      exact ⟨rfl, hc, hd⟩
    · exact (hTNC g a₀ b h).elim
  · rintro ⟨rfl, hc, hd⟩
    exact Or.inl ⟨rfl, hc, hd⟩
theorem canonicalLink_right_overlap_iff {G A B : Type v} [Group G]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (g : G) (b₀ b d : B) (a c : A) :
    canonicalLink L R (g, false) (a, b) =
      canonicalLink L R (g * R b₀, true) (c, d) ↔
      b = b₀ ∧ c = a ∧ d = invB b₀ := by
  rw [canonicalLink_overlap_iff L R invA invB hL hR hLA hRB hTNC]
  constructor
  · rintro (⟨h, _, _⟩ | ⟨h, hc, hd⟩)
    · exact (hTNC g a b₀ h.symm).elim
    · have hb : b = b₀ := (hR (mul_left_cancel h)).symm
      subst b
      exact ⟨rfl, hc, hd⟩
  · rintro ⟨rfl, hc, hd⟩
    exact Or.inr ⟨rfl, hc, hd⟩
def localExtensionWord {F : Type u} {I Q : Type v} [Semiring F] [Fintype I]
    (link : I → Q) (x : I → F) : Q → F :=
  ∑ i : I, x i • Pi.single (link i) 1
theorem localExtensionWord_pairing {F : Type u} {I J Q : Type v}
    [CommSemiring F] [Fintype I] [Fintype J] [Fintype Q]
    (link₁ : I → Q) (link₂ : J → Q) (z : I → F) (x : J → F) :
    dotProduct (localExtensionWord link₁ z) (localExtensionWord link₂ x) =
      ∑ i : I, ∑ j : J, if link₁ i = link₂ j then z i * x j else 0 := by
  unfold localExtensionWord
  simp_rw [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : link₁ i = link₂ j
  · simp [h]
  · simp [h, Ne.symm h]
theorem canonicalLocalChecks_orthogonal {G A B : Type v} {F : Type u}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Field F] [Fintype F]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (CA : LinearCode F A) (CB : LinearCode F B)
    (g h : G) (z x : Word F (A × B))
    (hz : z ∈ (tensorCode CA CB).carrier)
    (hx : x ∈ (tensorCode CA.dual CB.dual).carrier) :
    wordPairing (localExtensionWord (canonicalLink L R (g, false)) z)
      (localExtensionWord (canonicalLink L R (h, true)) x) = 0 := by
  rw [wordPairing_apply, localExtensionWord_pairing]
  have hz' := (mem_tensorCode CA CB z).1 hz
  have hx' := (mem_tensorCode CA.dual CB.dual x).1 hx
  by_cases hleft : ∃ a, h = L a * g
  · obtain ⟨a₀, rfl⟩ := hleft
    have ho := CB.dual_orthogonal (hz'.2 a₀) (hx'.2 (invA a₀))
    change (∑ b : B, z (a₀, b) * x (invA a₀, b)) = 0 at ho
    simp only [Fintype.sum_prod_type]
    simp_rw [canonicalLink_left_overlap_iff L R invA invB hL hR hLA hRB hTNC]
    simp [ite_and]
    exact ho
  · by_cases hright : ∃ b, h = g * R b
    · obtain ⟨b₀, rfl⟩ := hright
      have ho := CA.dual_orthogonal (hz'.1 b₀) (hx'.1 (invB b₀))
      change (∑ a : A, z (a, b₀) * x (a, invB b₀)) = 0 at ho
      simp only [Fintype.sum_prod_type]
      simp_rw [canonicalLink_right_overlap_iff L R invA invB hL hR hLA hRB hTNC]
      simp [ite_and]
      exact ho
    · apply Finset.sum_eq_zero
      intro ab _
      apply Finset.sum_eq_zero
      intro cd _
      have hne : canonicalLink L R (g, false) ab ≠ canonicalLink L R (h, true) cd := by
        intro heq
        rcases (canonicalLink_overlap_iff L R invA invB hL hR hLA hRB hTNC
          g h ab.1 cd.1 ab.2 cd.2).1 heq with ⟨ha, _, _⟩ | ⟨hb, _, _⟩
        · exact hleft ⟨ab.1, ha⟩
        · exact hright ⟨ab.2, hb⟩
      exact if_neg hne
theorem linearMapOfGenerators_single {F : Type u} {ι κ : Type v}
    [Field F] [Fintype ι] [Fintype κ] (generator : κ → Word F ι) (i : κ) :
    linearMapOfGenerators generator (Pi.single i 1) = generator i := by
  simp [linearMapOfGenerators]
theorem transposeGenerators_apply {F : Type u} {ι κ : Type v}
    [Field F] [Fintype F] [Fintype ι] [Fintype κ]
    (generator : κ → Word F ι) (y : Word F ι) (i : κ) :
    wordLinearMapTranspose (linearMapOfGenerators generator) y i =
      dotProduct y (generator i) := by
  change (∑ q : ι, y q * (linearMapOfGenerators generator (Pi.single i 1)) q) =
    dotProduct y (generator i)
  rw [linearMapOfGenerators_single]
  rfl
theorem generators_comp_zero {F : Type u} {ι κ ζ : Type v}
    [Field F] [Fintype F] [Fintype ι] [Fintype κ] [Fintype ζ]
    (gx : κ → Word F ι) (gz : ζ → Word F ι)
    (hOrth : ∀ i j, dotProduct (gz j) (gx i) = 0) :
    (wordLinearMapTranspose (linearMapOfGenerators gx)).comp
      (linearMapOfGenerators gz) = 0 := by
  apply LinearMap.ext
  intro c
  funext i
  change wordLinearMapTranspose (linearMapOfGenerators gx)
    (linearMapOfGenerators gz c) i = 0
  rw [transposeGenerators_apply]
  change dotProduct (∑ j : ζ, c j • gz j) (gx i) = 0
  simp_rw [sum_dotProduct, smul_dotProduct, hOrth]
  simp
def canonicalRawData {G A B XBasis ZBasis : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype XBasis] [Fintype ZBasis]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (xb : Module.Basis XBasis (ZMod 2) (tensorCode CA.dual CB.dual).carrier)
    (zb : Module.Basis ZBasis (ZMod 2) (tensorCode CA CB).carrier) :
    RawData G A B (CanonicalSquare L R) XBasis ZBasis where
  complex := canonicalSquareComplex L R invA invB hL hR hLA hRB hTNC
  codeA := CA
  codeB := CB
  xBasis := xb
  zBasis := zb
theorem canonicalRawData_boundary_squared {G A B XBasis ZBasis : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype XBasis] [Fintype ZBasis]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (xb : Module.Basis XBasis (ZMod 2) (tensorCode CA.dual CB.dual).carrier)
    (zb : Module.Basis ZBasis (ZMod 2) (tensorCode CA CB).carrier) :
    let D := canonicalRawData L R invA invB hL hR hLA hRB hTNC CA CB xb zb
    D.boundary1.comp D.boundary2 = 0 := by
  dsimp only
  apply generators_comp_zero
  intro i j
  change dotProduct
    (localExtensionWord (canonicalLink L R (j.1, false)) (zb j.2).1)
    (localExtensionWord (canonicalLink L R (i.1, true)) (xb i.2).1) = 0
  exact canonicalLocalChecks_orthogonal L R invA invB hL hR hLA hRB hTNC
    CA CB j.1 i.1 (zb j.2).1 (xb i.2).1 (zb j.2).2 (xb i.2).2
def canonicalData {G A B XBasis ZBasis : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype XBasis] [Fintype ZBasis]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (xb : Module.Basis XBasis (ZMod 2) (tensorCode CA.dual CB.dual).carrier)
    (zb : Module.Basis ZBasis (ZMod 2) (tensorCode CA CB).carrier) :
    Data G A B (CanonicalSquare L R) XBasis ZBasis where
  toRawData := canonicalRawData L R invA invB hL hR hLA hRB hTNC CA CB xb zb
  boundary_squared :=
    canonicalRawData_boundary_squared L R invA invB hL hR hLA hRB hTNC CA CB xb zb
abbrev TensorBasisIndex
    {A : Type v} [Fintype A] (C : LinearCode (ZMod 2) A) :=
  ULift.{v} (Fin (Dimension C))
noncomputable def finiteLocalCodeBasis
    {A : Type v} [Fintype A] (C : LinearCode (ZMod 2) A) :
    Module.Basis (TensorBasisIndex C) (ZMod 2) C.carrier :=
  (Module.finBasis (ZMod 2) C.carrier).reindex Equiv.ulift.symm
noncomputable def rawDataOfLocalCodeSample
    {r : Nat} {G A B Square : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
    (X : LeftRightCayleySquareComplex G A B Square)
    (sample : RandomLocalCodeSample r A B) :
    RawData G A B Square
      (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
      (TensorBasisIndex (tensorCode sample.codeA sample.codeB)) where
  complex := X
  codeA := sample.codeA
  codeB := sample.codeB
  xBasis := finiteLocalCodeBasis (tensorCode sample.codeA.dual sample.codeB.dual)
  zBasis := finiteLocalCodeBasis (tensorCode sample.codeA sample.codeB)
def canonicalDataOfLocalCodeSample
    {r : Nat} {G A B : Type v}
    [Group G] [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b)
    (sample : RandomLocalCodeSample r A B) :
    Data G A B (CanonicalSquare L R)
      (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
      (TensorBasisIndex (tensorCode sample.codeA sample.codeB)) :=
  canonicalData L R invA invB hL hR hLA hRB hTNC sample.codeA sample.codeB
    (finiteLocalCodeBasis (tensorCode sample.codeA.dual sample.codeB.dual))
    (finiteLocalCodeBasis (tensorCode sample.codeA sample.codeB))
def wordSupportSubsystem
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) : Semantics.FiniteSubsystem iota :=
  ⟨hammingSupport word⟩
def restrictWordToSubsystem
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (S : Semantics.FiniteSubsystem iota) (word : Word (ZMod 2) iota) :
    Word (ZMod 2) S.SelectedCoordinates :=
  fun i => word i
theorem embedSelectedWord_restrictWordToSubsystem
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (S : Semantics.FiniteSubsystem iota) (word : Word (ZMod 2) iota)
    (hsupport : hammingSupport word ⊆ S.selected) :
    QEC.Locality.embedSelectedWord S (restrictWordToSubsystem S word) = word := by
  funext i
  by_cases hi : i ∈ S.selected
  · simp [QEC.Locality.embedSelectedWord, restrictWordToSubsystem, hi]
  · have hzero : word i = 0 := by
      by_contra hnonzero
      exact hi (hsupport (by simp [hammingSupport, hnonzero]))
    simp [QEC.Locality.embedSelectedWord, hi, hzero]
noncomputable def cssXFiniteQuditCheck
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) : QEC.QLDPC.FiniteQuditCheck iota 2 := by
  let S := wordSupportSubsystem word
  exact
    { region := QEC.Locality.quditSubsystemOfFinite S
      localOperator := PauliSymplectic.toQubitOperator
        (QEC.Locality.wordBinaryPauli S
          (restrictWordToSubsystem S word, 0)) }
noncomputable def cssZFiniteQuditCheck
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) : QEC.QLDPC.FiniteQuditCheck iota 2 := by
  let S := wordSupportSubsystem word
  exact
    { region := QEC.Locality.quditSubsystemOfFinite S
      localOperator := PauliSymplectic.toQubitOperator
        (QEC.Locality.wordBinaryPauli S
          (0, restrictWordToSubsystem S word)) }
theorem cssXFiniteQuditCheck_globalOperator
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) :
    (cssXFiniteQuditCheck word).globalOperator =
      PauliSymplectic.toQubitOperator (PauliSymplectic.cssXCheck word) := by
  let S := wordSupportSubsystem word
  have hembed : QEC.Locality.embedSelectedWord S
      (restrictWordToSubsystem S word) = word :=
    embedSelectedWord_restrictWordToSubsystem S word (by rfl)
  have hzero : QEC.Locality.embedSelectedWord S
      (0 : Word (ZMod 2) S.SelectedCoordinates) = 0 := by
    funext i
    simp [QEC.Locality.embedSelectedWord]
  rw [show (cssXFiniteQuditCheck word).globalOperator =
      S.extendLocalToRegister
        (PauliSymplectic.toQubitOperator
          (QEC.Locality.wordBinaryPauli S
            (restrictWordToSubsystem S word, 0))) by rfl]
  rw [← QEC.Locality.toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]
  congr 1
  apply (PauliSymplectic.binaryEquivPhaseXPartZPart (ι := iota)).injective <;>
    simp [QEC.Locality.embeddedLocalPauli, hembed, hzero]
theorem cssZFiniteQuditCheck_globalOperator
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) :
    (cssZFiniteQuditCheck word).globalOperator =
      PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck word) := by
  let S := wordSupportSubsystem word
  have hembed : QEC.Locality.embedSelectedWord S
      (restrictWordToSubsystem S word) = word :=
    embedSelectedWord_restrictWordToSubsystem S word (by rfl)
  have hzero : QEC.Locality.embedSelectedWord S
      (0 : Word (ZMod 2) S.SelectedCoordinates) = 0 := by
    funext i
    simp [QEC.Locality.embedSelectedWord]
  rw [show (cssZFiniteQuditCheck word).globalOperator =
      S.extendLocalToRegister
        (PauliSymplectic.toQubitOperator
          (QEC.Locality.wordBinaryPauli S
            (0, restrictWordToSubsystem S word))) by rfl]
  rw [← QEC.Locality.toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]
  congr 1
  apply (PauliSymplectic.binaryEquivPhaseXPartZPart (ι := iota)).injective <;>
    simp [QEC.Locality.embeddedLocalPauli, hembed, hzero]
@[simp]
theorem cssXFiniteQuditCheck_region_selected
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) :
    (cssXFiniteQuditCheck word).region.selected = hammingSupport word :=
  rfl
@[simp]
theorem cssZFiniteQuditCheck_region_selected
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (word : Word (ZMod 2) iota) :
    (cssZFiniteQuditCheck word).region.selected = hammingSupport word :=
  rfl
namespace ChainComplexData
noncomputable def finiteQuditRowCheck
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda)) :
    Sum kappa lambda → QEC.QLDPC.FiniteQuditCheck iota 2
  | Sum.inl k => cssXFiniteQuditCheck
      (wordLinearMapTranspose K.boundary1
        (canonicalBasisWord (F := ZMod 2) k))
  | Sum.inr l => cssZFiniteQuditCheck
      (K.boundary2 (canonicalBasisWord (F := ZMod 2) l))
theorem finiteQuditRowCheck_globalOperator
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (c : Sum kappa lambda) :
    (finiteQuditRowCheck K c).globalOperator =
      PauliSymplectic.toQubitOperator
        (QEC.QLDPC.chainComplexCSSRowCheck K c) := by
  cases c with
  | inl k =>
      simpa [finiteQuditRowCheck, QEC.QLDPC.chainComplexCSSRowCheck] using
        cssXFiniteQuditCheck_globalOperator
          (wordLinearMapTranspose K.boundary1
            (canonicalBasisWord (F := ZMod 2) k))
  | inr l =>
      simpa [finiteQuditRowCheck, QEC.QLDPC.chainComplexCSSRowCheck] using
        cssZFiniteQuditCheck_globalOperator
          (K.boundary2 (canonicalBasisWord (F := ZMod 2) l))
noncomputable def finiteQuditCheckPresentation
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (encodedQudits : Nat)
    (hdimension :
      Module.finrank Complex (K.binaryCSSCode).stabilizer.code.carrier =
        2 ^ encodedQudits) :
    QEC.QLDPC.FiniteQuditCheckPresentation iota (Sum kappa lambda) where
  alphabetSize := 2
  alphabetSize_ge_two := by decide
  code := (K.binaryCSSCode).stabilizer.code
  checks := finiteQuditRowCheck K
  carrier_iff_fixed := by
    intro psi
    have hsource := K.binaryCSSCode_stabilizer_isSourceValidBinary.2 psi
    have hgenerate :=
      QEC.QLDPC.chainComplexCSSRowChecks_generate_stabilizerGroup K
    rw [QEC.QLDPC.FinsetGenerates] at hgenerate
    constructor
    · intro hpsi c
      rw [finiteQuditRowCheck_globalOperator]
      apply (hsource.mp hpsi)
      have hrow : QEC.QLDPC.chainComplexCSSRowCheck K c ∈
          QEC.QLDPC.chainComplexCSSRowChecks K :=
        (QEC.QLDPC.mem_chainComplexCSSRowChecks K _).2 ⟨c, rfl⟩
      have hgenerated : PauliSymplectic.GeneratedStabilizer
          (fun g : {P : PauliSymplectic.Binary iota //
            P ∈ QEC.QLDPC.chainComplexCSSRowChecks K} => g.1)
          (QEC.QLDPC.chainComplexCSSRowCheck K c) :=
        PauliSymplectic.GeneratedStabilizer.generator
          (⟨QEC.QLDPC.chainComplexCSSRowCheck K c, hrow⟩ :
            {P : PauliSymplectic.Binary iota //
              P ∈ QEC.QLDPC.chainComplexCSSRowChecks K})
      rw [← hgenerate]
      exact hgenerated
    · intro hfixed
      apply hsource.mpr
      intro P hP
      have hgenerated : P ∈ PauliSymplectic.generatedStabilizerSet
          (fun g : {Q : PauliSymplectic.Binary iota //
            Q ∈ QEC.QLDPC.chainComplexCSSRowChecks K} => g.1) := by
        rw [hgenerate]
        exact hP
      change PauliSymplectic.GeneratedStabilizer
        (fun g : {Q : PauliSymplectic.Binary iota //
          Q ∈ QEC.QLDPC.chainComplexCSSRowChecks K} => g.1) P at hgenerated
      apply PauliSymplectic.toQubitOperator_fixed_of_generatedStabilizer
        _ _ hgenerated
      intro g
      rcases (QEC.QLDPC.mem_chainComplexCSSRowChecks K g.1).1 g.2 with
        ⟨c, hc⟩
      rw [← hc, ← finiteQuditRowCheck_globalOperator]
      exact hfixed c
  encodedQudits := encodedQudits
  dimension_eq := by
    change Module.finrank Complex
      (K.binaryCSSCode).stabilizer.code.carrier = 2 ^ encodedQudits
    exact hdimension
end ChainComplexData
namespace LeftRightCayleySquareComplex
end LeftRightCayleySquareComplex
namespace RawData
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
@[simp]
theorem linearMapOfGenerators_canonicalBasis
    {F : Type u} {ι κ : Type v} [Field F] [Fintype ι] [Fintype κ]
    (generator : κ → Word F ι) (k : κ) :
    linearMapOfGenerators generator (canonicalBasisWord k) = generator k := by
  classical
  funext i
  unfold linearMapOfGenerators canonicalBasisWord
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro k' hne
    simp [hne]
end RawData
namespace Data
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
variable [DecidableEq Square]
theorem finrank_binaryCSSCode_carrier_eq_pow_encodedDimension
    (D : Data G A B Square XBasis ZBasis) :
    Module.finrank Complex (D.chainComplex.binaryCSSCode).stabilizer.code.carrier =
      2 ^ D.encodedDimension := by
  simpa [Data.encodedDimension] using
    D.chainComplex.binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology
noncomputable def finiteQuditCheckPresentation
    (D : Data G A B Square XBasis ZBasis) :
    QEC.QLDPC.FiniteQuditCheckPresentation Square
      (Sum (G × XBasis) (G × ZBasis)) :=
  ChainComplexData.finiteQuditCheckPresentation
    D.chainComplex D.encodedDimension
      D.finrank_binaryCSSCode_carrier_eq_pow_encodedDimension
@[simp]
theorem finiteQuditCheckPresentation_blockLength
    (D : Data G A B Square XBasis ZBasis) :
    D.finiteQuditCheckPresentation.blockLength = D.blockLength :=
  rfl
@[simp]
theorem finiteQuditCheckPresentation_encodedQudits
    (D : Data G A B Square XBasis ZBasis) :
    D.finiteQuditCheckPresentation.encodedQudits = D.encodedDimension :=
  rfl
end Data
namespace Family
variable {Index : Type u}
variable {G A B Square XBasis ZBasis : Index → Type v}
variable [∀ i, Group (G i)] [∀ i, Fintype (G i)]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable [∀ i, Fintype (Square i)] [∀ i, DecidableEq (Square i)]
variable [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]
noncomputable def ofData
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength) :
    QEC.QLDPC.QuantumCodeFamily Index Square
      (fun i => Sum (G i × XBasis i) (G i × ZBasis i)) where
  presentation i := (family i).finiteQuditCheckPresentation
  cofinal_blockLength N := by
    obtain ⟨i, hi⟩ := hcofinal N
    exact ⟨i, by simpa using hi⟩
end Family
end QEC.Coding.QuantumTanner


