-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerCode
-- name    : QEC_Coding_QuantumTanner_LiftedProductTannerCode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T05:36:33.466397+00:00
-- url     : https://prove2.me/theorems/50fcdc13-a622-407e-a1f9-dd39ac2475d4
-- title:
--   Lifted Product Tanner Code
-- statement:
--   Definitions and structural lemmas for Lifted Product Tanner Code, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerCode.lean

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_chartExtension_eq_sum_single
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_chartLink_eq_iff
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_chartLink_injective
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selected_lifted_product_eq_quantum_tanner
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_localExtension_mem_range_xGeneratorMap
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_localExtension_mem_range_zGeneratorMap
import Theorems.Thm_QEC_Coding_QuantumTanner_generator_mem_range_linearMapOfGenerators
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_blockLength
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_encodedDimension
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
namespace QEC.Coding.QuantumTanner.LiftedProductTannerCode
open Classical LiftedProductTannerBridge LiftedProductTensorBridge
open LiftedProductActionBridge LiftedProductRestriction
abbrev Flag := Multiplicative (ZMod 2)
abbrev VertexGroup (G : Type) := G × Flag
def oddFlag : Flag := Multiplicative.ofAdd 1
def leftFlag (k : Flag) : Bool := decide (k = oddFlag)
def rightFlag (k : Flag) (side : Bool) : Bool :=
  if side then leftFlag k else !(leftFlag k)
@[simp] theorem leftFlag_one : leftFlag 1 = false := by decide
@[simp] theorem leftFlag_odd : leftFlag oddFlag = true := by decide
theorem flag_cases (k : Flag) : k = 1 ∨ k = oddFlag := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
    intro z
    fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
  have h := hz k.toAdd
  rcases h with h | h
  · exact Or.inl (congrArg Multiplicative.ofAdd h)
  · exact Or.inr (congrArg Multiplicative.ofAdd h)
variable {G A B : Type} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
def coverLink (a : A → G) (b : B → G) (vertex : VertexGroup G × Bool) :
    A × B → A × B × G :=
  chartLink a b (leftFlag vertex.1.2) (rightFlag vertex.1.2 vertex.2) vertex.1.1
theorem coverLink_incident_iff (a : A → G) (b : B → G)
    (u : G) (k : Flag) (side : Bool) (i : A) (j : B) (g : G) :
    (∃ ij, coverLink a b ((u, k), side) ij = (i, j, g)) ↔
      u = chartVertex a b (leftFlag k) (rightFlag k side) i j g := by
  constructor
  · rintro ⟨ij, he⟩
    have hij : ij = (i, j) := by
      apply Prod.ext
      · exact congrArg (fun q : A × B × G => q.1) he
      · exact congrArg (fun q : A × B × G => q.2.1) he
    subst ij
    exact (chartLink_eq_iff _ _ _ _ _ _ _ _).1 he
  · intro h
    exact ⟨(i, j), (chartLink_eq_iff _ _ _ _ _ _ _ _).2 h⟩
def incidentFlagEquiv (a : A → G) (b : B → G) (side : Bool) (q : A × B × G) :
    {v : VertexGroup G // ∃ ij, coverLink a b (v, side) ij = q} ≃ Flag where
  toFun v := v.val.2
  invFun k := ⟨(chartVertex a b (leftFlag k) (rightFlag k side) q.1 q.2.1 q.2.2, k),
    (coverLink_incident_iff a b _ k side q.1 q.2.1 q.2.2).2 rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · exact ((coverLink_incident_iff a b v.val.1 v.val.2 side q.1 q.2.1 q.2.2).1
        v.property).symm
    · rfl
  right_inv k := rfl
def coverComplex (a : A → G) (b : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹) :
    LeftRightCayleySquareComplex (VertexGroup G) A B (A × B × G) where
  leftGenerator i := (a i, oddFlag)
  rightGenerator j := (b j, 1)
  leftInverse := invA
  rightInverse := invB
  leftGenerator_inverse i := by
    apply Prod.ext
    · exact hA i
    · change oddFlag = oddFlag⁻¹
      decide
  rightGenerator_inverse j := by
    apply Prod.ext
    · exact hB j
    · simp
  noConjugacy g i j := by
    intro he
    have hf := congrArg (fun v : VertexGroup G => v.2) he
    have hn : oddFlag ≠ (1 : Flag) := by decide
    apply hn
    apply mul_right_cancel (b := g.2)
    simpa using hf
  link := coverLink a b
  link_injective v := chartLink_injective a b _ _ _
  square_side_degree q side := by
    rw [← Fintype.card_subtype, Fintype.card_congr (incidentFlagEquiv a b side q)]
    decide
theorem coverComplex_localExtension (a : A → G) (b : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹)
    (v : VertexGroup G × Bool) (x : Word (ZMod 2) (A × B)) :
    (coverComplex a b invA invB hA hB).localExtension v x =
      chartExtension a b (leftFlag v.1.2) (rightFlag v.1.2 v.2) v.1.1 x := by
  rw [chartExtension_eq_sum_single]
  ext q
  simp [LeftRightCayleySquareComplex.localExtension, coverComplex, coverLink,
    Pi.single_apply]
def coverRawData (a : A → G) (b : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) :
    RawData (VertexGroup G) A B (A × B × G)
      (Fin (Dimension (tensorCode CA.dual CB.dual)))
      (Fin (Dimension (tensorCode CA CB))) where
  complex := coverComplex a b invA invB hA hB
  codeA := CA
  codeB := CB
  xBasis := Module.finBasis (ZMod 2) (tensorCode CA.dual CB.dual).carrier
  zBasis := Module.finBasis (ZMod 2) (tensorCode CA CB).carrier
theorem coverRawData_z_range (a : A → G) (b : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) :
    LinearMap.range (coverRawData a b invA invB hA hB CA CB).zGeneratorMap =
      tannerZChecks a b (tensorCode CA CB) := by
  let D := coverRawData a b invA invB hA hB CA CB
  have hComplex : D.complex = coverComplex a b invA invB hA hB := rfl
  apply le_antisymm
  · rintro x ⟨r, rfl⟩
    change (∑ check, r check • D.zGenerator check) ∈ _
    apply Submodule.sum_mem
    intro check _
    apply Submodule.smul_mem
    change D.complex.localExtension (check.1, false) (D.zBasis check.2).val ∈ _
    rw [hComplex, coverComplex_localExtension]
    rcases flag_cases check.1.2 with hk | hk
    · rw [hk]
      exact Submodule.subset_span (Or.inl ⟨(check.1.1, D.zBasis check.2), rfl⟩)
    · rw [hk]
      exact Submodule.subset_span (Or.inr ⟨(check.1.1, D.zBasis check.2), rfl⟩)
  · apply Submodule.span_le.2
    rintro x (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩)
    · have h := D.localExtension_mem_range_zGeneratorMap (u, 1) w.val w.property
      rw [hComplex, coverComplex_localExtension] at h
      simpa [rightFlag] using h
    · have h := D.localExtension_mem_range_zGeneratorMap (u, oddFlag) w.val w.property
      rw [hComplex, coverComplex_localExtension] at h
      simpa [rightFlag] using h
theorem coverRawData_x_range (a : A → G) (b : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) :
    LinearMap.range (coverRawData a b invA invB hA hB CA CB).xGeneratorMap =
      tannerXChecks a b (tensorCode CA.dual CB.dual) := by
  let D := coverRawData a b invA invB hA hB CA CB
  have hComplex : D.complex = coverComplex a b invA invB hA hB := rfl
  apply le_antisymm
  · rintro x ⟨r, rfl⟩
    change (∑ check, r check • D.xGenerator check) ∈ _
    apply Submodule.sum_mem
    intro check _
    apply Submodule.smul_mem
    change D.complex.localExtension (check.1, true) (D.xBasis check.2).val ∈ _
    rw [hComplex, coverComplex_localExtension]
    rcases flag_cases check.1.2 with hk | hk
    · rw [hk]
      exact Submodule.subset_span (Or.inl ⟨(check.1.1, D.xBasis check.2), rfl⟩)
    · rw [hk]
      exact Submodule.subset_span (Or.inr ⟨(check.1.1, D.xBasis check.2), rfl⟩)
  · apply Submodule.span_le.2
    rintro x (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩)
    · have h := D.localExtension_mem_range_xGeneratorMap (u, 1) w.val w.property
      rw [hComplex, coverComplex_localExtension] at h
      simpa [rightFlag] using h
    · have h := D.localExtension_mem_range_xGeneratorMap (u, oddFlag) w.val w.property
      rw [hComplex, coverComplex_localExtension] at h
      simpa [rightFlag] using h
theorem generators_comp_zero {Q X Z : Type}
    [Fintype Q] [Fintype X] [Fintype Z]
    (gx : X → Word (ZMod 2) Q) (gz : Z → Word (ZMod 2) Q)
    (hOrth : ∀ i j, dotProduct (gz j) (gx i) = 0) :
    (wordLinearMapTranspose (linearMapOfGenerators gx)).comp
      (linearMapOfGenerators gz) = 0 := by
  apply LinearMap.ext
  intro c
  funext i
  change (∑ q, (linearMapOfGenerators gz c) q *
    (linearMapOfGenerators gx (Pi.single i 1)) q) = 0
  have hsingle : linearMapOfGenerators gx (Pi.single i 1) = gx i := by
    simp [linearMapOfGenerators, Pi.single_apply]
  rw [hsingle]
  change dotProduct (∑ j, c j • gz j) (gx i) = 0
  simp_rw [sum_dotProduct, smul_dotProduct, hOrth]
  simp
variable {C D C' D' : Type} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']
theorem coverRawData_boundary_squared
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hInvA : ∀ i, a (invA i) = (a i)⁻¹) (hInvB : ∀ j, b (invB j) = (b j)⁻¹)
    (hDualA : parityCheckKernelCode (Matrix.toLin' gA) =
      (parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : parityCheckKernelCode (Matrix.toLin' gB) =
      (parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    let T := coverRawData a b invA invB hInvA hInvB
      (parityCheckKernelCode (Matrix.toLin' gA)) (parityCheckKernelCode (Matrix.toLin' hB))
    T.boundary1.comp T.boundary2 = 0 := by
  dsimp only
  let T := coverRawData a b invA invB hInvA hInvB
    (parityCheckKernelCode (Matrix.toLin' gA)) (parityCheckKernelCode (Matrix.toLin' hB))
  have hSpaces := selected_lifted_product_eq_quantum_tanner hA hB gA gB a b hDualA hDualB
  have hZ : Set.range (selectedZWord hA hB gB a b) = (LinearMap.range T.zGeneratorMap).carrier := by
    rw [coverRawData_z_range]
    exact hSpaces.1
  have hX : Set.range (selectedXWord hA hB gA a b) = (LinearMap.range T.xGeneratorMap).carrier := by
    rw [coverRawData_x_range]
    exact hSpaces.2.1
  apply generators_comp_zero T.xGenerator T.zGenerator
  intro i j
  have hz := generator_mem_range_linearMapOfGenerators T.zGenerator j
  have hx := generator_mem_range_linearMapOfGenerators T.xGenerator i
  change T.zGenerator j ∈ (LinearMap.range T.zGeneratorMap).carrier at hz
  change T.xGenerator i ∈ (LinearMap.range T.xGeneratorMap).carrier at hx
  rw [← hZ] at hz
  rw [← hX] at hx
  obtain ⟨U, hU⟩ := hz
  obtain ⟨V, hV⟩ := hx
  rw [← hU, ← hV]
  have hSum := hSpaces.2.2 U V
  rw [Finset.sum_comm] at hSum
  simpa only [dotProduct, Fintype.sum_prod_type] using hSum
def selectedData
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hInvA : ∀ i, a (invA i) = (a i)⁻¹) (hInvB : ∀ j, b (invB j) = (b j)⁻¹)
    (hDualA : parityCheckKernelCode (Matrix.toLin' gA) =
      (parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : parityCheckKernelCode (Matrix.toLin' gB) =
      (parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    Data (VertexGroup G) A B (A × B × G)
      (Fin (Dimension (tensorCode (parityCheckKernelCode (Matrix.toLin' gA)).dual
        (parityCheckKernelCode (Matrix.toLin' hB)).dual)))
      (Fin (Dimension (tensorCode (parityCheckKernelCode (Matrix.toLin' gA))
        (parityCheckKernelCode (Matrix.toLin' hB))))) where
  toRawData := coverRawData a b invA invB hInvA hInvB
    (parityCheckKernelCode (Matrix.toLin' gA)) (parityCheckKernelCode (Matrix.toLin' hB))
  boundary_squared := coverRawData_boundary_squared hA hB gA gB a b invA invB
    hInvA hInvB hDualA hDualB
end QEC.Coding.QuantumTanner.LiftedProductTannerCode


