-- Prove2me | Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
-- name    : QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T14:04:43.784922+00:00
-- url     : https://prove2.me/theorems/e3e7f2a0-0c2d-4116-99c1-86f043add961
-- title:
--   Weighted Triorthogonal CSS
-- statement:
--   Definitions and structural lemmas for Weighted Triorthogonal CSS, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_additiveCharacter_add
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
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
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
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
namespace QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Coding QEC.Semantics
open scoped BigOperators
abbrev Why24Word (Site : Type) := QEC.Coding.Word F1024 Site
def seventhPairing {Site : Type} [Fintype Site]
    (x y z : Why24Word Site) : F1024 :=
  ∑ site : Site, x site ^ 4 * y site ^ 2 * z site
def weightedPairing {Site : Type} [Fintype Site]
    (sigma x y : Why24Word Site) : F1024 :=
  ∑ site : Site, sigma site * x site * y site
def seventhExponent {Index : Type} [Fintype Index]
    (label : Why24Word Index) : F1024 :=
  ∑ index : Index, label index ^ 7
def seventhTarget {Logical Stabilizer : Type} [DecidableEq Logical]
    (a b c : Logical ⊕ Stabilizer) : F1024 :=
  match a, b, c with
  | Sum.inl i, Sum.inl j, Sum.inl k => if i = j ∧ j = k then 1 else 0
  | _, _, _ => 0
def weightedTarget {Logical Stabilizer : Type} [DecidableEq Logical]
    (tau : Logical → F1024) (a b : Logical ⊕ Stabilizer) : F1024 :=
  match a, b with
  | Sum.inl i, Sum.inl j => if i = j then tau i else 0
  | _, _ => 0
structure WeightedTriorthogonalMatrix
    (Logical Stabilizer Site : Type)
    [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site] where
  /-- Rows which label the encoded logical computational basis. -/
  logicalRow : Logical → Why24Word Site
  /-- Rows whose actual span is the X-stabilizer code `G₀`. -/
  stabilizerRow : Stabilizer → Why24Word Site
  /-- Nonzero coordinate weights in the source bilinear equation. -/
  sigma : Why24Word Site
  /-- Nonzero logical diagonal values in the source bilinear equation. -/
  tau : Logical → F1024
  sigma_ne_zero : ∀ site, sigma site ≠ 0
  tau_ne_zero : ∀ logical, tau logical ≠ 0
  seventh_condition : ∀ a b c : Logical ⊕ Stabilizer,
    seventhPairing (Sum.elim logicalRow stabilizerRow a)
      (Sum.elim logicalRow stabilizerRow b)
      (Sum.elim logicalRow stabilizerRow c) = seventhTarget a b c
  weighted_condition : ∀ a b : Logical ⊕ Stabilizer,
    weightedPairing sigma (Sum.elim logicalRow stabilizerRow a)
      (Sum.elim logicalRow stabilizerRow b) = weightedTarget tau a b
namespace WeightedTriorthogonalMatrix
variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]
def row (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Logical ⊕ Stabilizer → Why24Word Site :=
  Sum.elim R.logicalRow R.stabilizerRow
@[simp]
theorem row_inl (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) (a : Logical) :
    R.row (Sum.inl a) = R.logicalRow a :=
  rfl
@[simp]
theorem row_inr (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) (s : Stabilizer) :
    R.row (Sum.inr s) = R.stabilizerRow s :=
  rfl
def logicalCode (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    LinearCode F1024 Site where
  carrier := Submodule.span F1024 (Set.range R.logicalRow)
def stabilizerCode (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    LinearCode F1024 Site where
  carrier := Submodule.span F1024 (Set.range R.stabilizerRow)
def rowCode (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    LinearCode F1024 Site where
  carrier := Submodule.span F1024 (Set.range R.row)
def logicalWord (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) : Why24Word Site :=
  ∑ a : Logical, u a • R.logicalRow a
def combinedWord (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (q : Logical ⊕ Stabilizer → F1024) : Why24Word Site :=
  ∑ r : Logical ⊕ Stabilizer, q r • R.row r
theorem weightedPairing_add_left (sigma x y z : Why24Word Site) :
    weightedPairing sigma (x + y) z =
      weightedPairing sigma x z + weightedPairing sigma y z := by
  unfold weightedPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro site _
  simp only [Pi.add_apply]
  ring
theorem weightedPairing_smul_left (sigma x y : Why24Word Site) (c : F1024) :
    weightedPairing sigma (c • x) y = c * weightedPairing sigma x y := by
  unfold weightedPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro site _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
def weightedPairingLeftLinearMap (sigma y : Why24Word Site) :
    Why24Word Site →ₗ[F1024] F1024 where
  toFun x := weightedPairing sigma x y
  map_add' x z := weightedPairing_add_left sigma x z y
  map_smul' c x := by
    change weightedPairing sigma (c • x) y = c • weightedPairing sigma x y
    rw [weightedPairing_smul_left]
    rfl
@[simp]
theorem weightedPairingLeftLinearMap_apply
    (sigma x y : Why24Word Site) :
    weightedPairingLeftLinearMap sigma y x = weightedPairing sigma x y :=
  rfl
theorem weightedPairing_logicalWord_logicalRow
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (a : Logical) :
    weightedPairing R.sigma (R.logicalWord u) (R.logicalRow a) =
      u a * R.tau a := by
  classical
  unfold logicalWord
  change weightedPairingLeftLinearMap R.sigma (R.logicalRow a)
      (∑ b, u b • R.logicalRow b) = _
  rw [map_sum]
  simp only [map_smul, weightedPairingLeftLinearMap_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · have h := R.weighted_condition (Sum.inl a) (Sum.inl a)
    simpa [weightedTarget] using congrArg (fun z => u a * z) h
  · intro b _ hba
    have h := R.weighted_condition (Sum.inl b) (Sum.inl a)
    have hzero : weightedPairing R.sigma (R.logicalRow b) (R.logicalRow a) = 0 := by
      simpa [weightedTarget, hba] using h
    rw [hzero, mul_zero]
  · simp
theorem weightedPairing_stabilizerCode_logicalRow
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.stabilizerCode.carrier) (a : Logical) :
    weightedPairing R.sigma x (R.logicalRow a) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨s, rfl⟩
      have h := R.weighted_condition (Sum.inr s) (Sum.inl a)
      simpa [weightedTarget] using h
  | zero => simp [weightedPairing]
  | add x y _ _ hx hy =>
      rw [weightedPairing_add_left, hx, hy, add_zero]
  | smul c x _ hx =>
      rw [weightedPairing_smul_left, hx, mul_zero]
theorem eq_zero_of_mem_logicalCode_of_weightedPairing_eq_zero
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.logicalCode.carrier)
    (hpair : ∀ a, weightedPairing R.sigma x (R.logicalRow a) = 0) :
    x = 0 := by
  classical
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun F1024).mp hx
  change R.logicalWord u = x at hu
  have hu0 : u = 0 := by
    funext a
    have h := hpair a
    rw [← hu, R.weightedPairing_logicalWord_logicalRow] at h
    exact (mul_eq_zero.mp h).resolve_right (R.tau_ne_zero a)
  rw [← hu, hu0]
  simp [logicalWord]
theorem logicalRows_linearIndependent
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    LinearIndependent F1024 R.logicalRow := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro u hu a
  have hpair := congrArg
    (fun x => weightedPairing R.sigma x (R.logicalRow a)) hu
  have hzero : weightedPairing R.sigma (R.logicalWord u) (R.logicalRow a) = 0 := by
    change weightedPairing R.sigma (∑ i, u i • R.logicalRow i) (R.logicalRow a) = 0
    simpa [weightedPairing] using hpair
  rw [R.weightedPairing_logicalWord_logicalRow] at hzero
  exact (mul_eq_zero.mp hzero).resolve_right (R.tau_ne_zero a)
theorem stabilizerCode_disjoint_logicalCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.stabilizerCode.carrier ⊓ R.logicalCode.carrier = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxStabilizer : x ∈ R.stabilizerCode.carrier := hx.1
    have hxLogical : x ∈ R.logicalCode.carrier := hx.2
    have hx0 : x = 0 := R.eq_zero_of_mem_logicalCode_of_weightedPairing_eq_zero
      hxLogical (fun a => R.weightedPairing_stabilizerCode_logicalRow hxStabilizer a)
    simpa [hx0]
  · exact bot_le
noncomputable def sigmaEquiv
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Why24Word Site ≃ₗ[F1024] Why24Word Site where
  toFun x := fun site => R.sigma site * x site
  invFun x := fun site => (R.sigma site)⁻¹ * x site
  left_inv x := by
    funext site
    field_simp [R.sigma_ne_zero site]
  right_inv x := by
    funext site
    field_simp [R.sigma_ne_zero site]
  map_add' x y := by
    funext site
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext site
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
@[simp]
theorem sigmaEquiv_apply
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (x : Why24Word Site) (site : Site) :
    R.sigmaEquiv x site = R.sigma site * x site :=
  rfl
noncomputable def cssXDistance
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) : WithTop Nat := by
  classical
  exact HypergraphProduct.finitePredicateMinimum
    (fun x : Why24Word Site => x ∈ R.rowCode.carrier ∧ x ∉ R.stabilizerCode.carrier)
    HammingWeight
noncomputable def cssZDistance
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) : WithTop Nat := by
  classical
  exact HypergraphProduct.finitePredicateMinimum
    (fun x : Why24Word Site =>
      x ∈ R.stabilizerCode.dual.carrier ∧ x ∉ R.rowCode.dual.carrier)
    HammingWeight
def dualLogicalRow
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) : Why24Word Site :=
  (R.tau a)⁻¹ • R.sigmaEquiv (R.logicalRow a)
theorem logicalWord_sub
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024) :
    R.logicalWord (u - v) = R.logicalWord u - R.logicalWord v := by
  classical
  ext site
  simp only [logicalWord, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
    sub_smul, smul_eq_mul]
  rw [Finset.sum_sub_distrib]
theorem logicalWord_mem_logicalCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.logicalWord u ∈ R.logicalCode.carrier := by
  exact Submodule.sum_mem R.logicalCode.carrier
    (fun a _ => R.logicalCode.carrier.smul_mem _
      (Submodule.subset_span ⟨a, rfl⟩))
theorem logicalWord_eq_zero_iff
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.logicalWord u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext a
    exact (Fintype.linearIndependent_iff.mp R.logicalRows_linearIndependent) u h a
  · intro h
    rw [h]
    simp [logicalWord]
def cosetLabel
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (h : R.stabilizerCode.carrier) : Why24Word Site :=
  R.logicalWord u + (h : Why24Word Site)
theorem cosetLabel_injective
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) : Function.Injective (R.cosetLabel u) := by
  intro h k heq
  apply Subtype.ext
  exact add_left_cancel heq
theorem cosetLabel_eq_implies_logical_eq
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024)
    (h k : R.stabilizerCode.carrier)
    (heq : R.cosetLabel u h = R.cosetLabel v k) : u = v := by
  have hdifference :
      R.logicalWord (u - v) = (k : Why24Word Site) - (h : Why24Word Site) := by
    rw [R.logicalWord_sub]
    unfold cosetLabel at heq
    ext site
    have hsite := congrFun heq site
    change R.logicalWord u site + h.1 site =
      R.logicalWord v site + k.1 site at hsite
    change R.logicalWord u site - R.logicalWord v site = k.1 site - h.1 site
    linear_combination hsite
  have hlogical : R.logicalWord (u - v) ∈ R.logicalCode.carrier :=
    R.logicalWord_mem_logicalCode (u - v)
  have hstabilizer : R.logicalWord (u - v) ∈ R.stabilizerCode.carrier := by
    rw [hdifference]
    exact R.stabilizerCode.carrier.sub_mem k.property h.property
  have hzero : R.logicalWord (u - v) = 0 := by
    have hintersection : R.logicalWord (u - v) ∈
        R.stabilizerCode.carrier ⊓ R.logicalCode.carrier :=
      ⟨hstabilizer, hlogical⟩
    rw [R.stabilizerCode_disjoint_logicalCode] at hintersection
    simpa using hintersection
  have huv : u - v = 0 := (R.logicalWord_eq_zero_iff (u - v)).mp hzero
  exact sub_eq_zero.mp huv
abbrev StabilizerCarrier
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :=
  R.stabilizerCode.carrier
noncomputable instance stabilizerCarrierFintype
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Fintype R.StabilizerCarrier :=
  Fintype.ofFinite _
def cosetNormalization
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) : Complex :=
  (Real.sqrt (Nat.card R.StabilizerCarrier : Real) : Complex)⁻¹
def cosetKet
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) : ComputationalBasisRegister F1024 Site :=
  R.cosetNormalization •
    ∑ h : R.StabilizerCarrier, registerBasisKet (R.cosetLabel u h)
theorem uniformCosetSum_inner
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024) :
    inner Complex
        (∑ h : R.StabilizerCarrier, registerBasisKet (R.cosetLabel u h))
        (∑ k : R.StabilizerCarrier, registerBasisKet (R.cosetLabel v k)) =
      if u = v then (Nat.card R.StabilizerCarrier : Complex) else 0 := by
  classical
  rw [inner_sum]
  simp_rw [sum_inner]
  by_cases huv : u = v
  · subst v
    have hinner (h k : R.StabilizerCarrier) :
        inner Complex (registerBasisKet (R.cosetLabel u h))
          (registerBasisKet (R.cosetLabel u k)) = if h = k then 1 else 0 := by
      simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
      rw [EuclideanSpace.inner_single_left]
      simp [PiLp.single_apply, (R.cosetLabel_injective u).eq_iff]
    simp_rw [hinner]
    simp [Nat.card_eq_fintype_card]
  · rw [if_neg huv]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    have hlabel : R.cosetLabel u k ≠ R.cosetLabel v h :=
      fun heq => huv (R.cosetLabel_eq_implies_logical_eq u v k h heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel]
theorem cosetNormalization_conj_mul_card
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    starRingEnd Complex R.cosetNormalization * R.cosetNormalization *
        (Nat.card R.StabilizerCarrier : Complex) = 1 := by
  have hpos : (0 : Real) < Nat.card R.StabilizerCarrier := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card R.StabilizerCarrier)
  have hsqrt :
      (Real.sqrt (Nat.card R.StabilizerCarrier : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  unfold cosetNormalization
  rw [map_inv₀, Complex.conj_ofReal]
  field_simp
  norm_cast
  exact (Real.sq_sqrt hpos.le).symm
theorem cosetKet_inner
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024) :
    inner Complex (R.cosetKet u) (R.cosetKet v) = if u = v then 1 else 0 := by
  unfold cosetKet
  rw [inner_smul_left, inner_smul_right, uniformCosetSum_inner]
  by_cases huv : u = v
  · subst v
    simp only [ite_true]
    rw [← mul_assoc]
    exact R.cosetNormalization_conj_mul_card
  · simp [huv]
theorem cosetKet_orthonormal
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Orthonormal Complex R.cosetKet := by
  rw [orthonormal_iff_ite]
  intro u v
  exact R.cosetKet_inner u v
noncomputable def encodingLinearMap
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    ComputationalBasisRegister F1024 Logical →ₗ[Complex]
      ComputationalBasisRegister F1024 Site where
  toFun psi := ∑ u : Logical → F1024, psi u • R.cosetKet u
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]
theorem encodingLinearMap_map_inner
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (psi chi : ComputationalBasisRegister F1024 Logical) :
    inner Complex (R.encodingLinearMap psi) (R.encodingLinearMap chi) =
      inner Complex psi chi := by
  change inner Complex
      (∑ u : Logical → F1024, psi u • R.cosetKet u)
      (∑ u : Logical → F1024, chi u • R.cosetKet u) = inner Complex psi chi
  rw [R.cosetKet_orthonormal.inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]
noncomputable def encodingIsometry
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    ComputationalBasisRegister F1024 Logical →ₗᵢ[Complex]
      ComputationalBasisRegister F1024 Site :=
  R.encodingLinearMap.isometryOfInner R.encodingLinearMap_map_inner
noncomputable def encodedCarrier
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Submodule Complex (ComputationalBasisRegister F1024 Site) :=
  R.encodingIsometry.toLinearMap.range
noncomputable def quantumCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    QuantumCode (ComputationalBasisRegister F1024 Site) where
  carrier := R.encodedCarrier
noncomputable def encodedCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    EncodedCode (ComputationalBasisRegister F1024 Logical)
      (ComputationalBasisRegister F1024 Site) where
  code := R.quantumCode
  encoding := LinearIsometry.equivRange R.encodingIsometry
theorem encodingLinearMap_apply_logical_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.encodingLinearMap (registerBasisKet u) = R.cosetKet u := by
  change (∑ v : Logical → F1024, registerBasisKet u v • R.cosetKet v) = R.cosetKet u
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]
theorem encodedCode_apply_logical_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.encodedCode.encode (registerBasisKet u) = R.cosetKet u :=
  R.encodingLinearMap_apply_logical_basis u
theorem encodedCode_encode_eq_encodingLinearMap
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (psi : ComputationalBasisRegister F1024 Logical) :
    R.encodedCode.encode psi = R.encodingLinearMap psi :=
  rfl
noncomputable def wordXOperator {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index) :
    Operator (ComputationalBasisRegister F1024 Index) where
  toFun psi := WithLp.toLp 2 fun label => psi (label + word)
  map_add' psi chi := by
    ext label
    simp
  map_smul' c psi := by
    ext label
    simp [smul_eq_mul]
@[simp]
theorem wordXOperator_apply {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi : ComputationalBasisRegister F1024 Index)
    (label : ComputationalBasisRegisterLabel F1024 Index) :
    wordXOperator word psi label = psi (label + word) :=
  rfl
theorem add_word_add_word {Index : Type}
    (label word : Why24Word Index) :
    (label + word) + word = label := by
  funext site
  simp only [Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
theorem wordXOperator_map_inner {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi chi : ComputationalBasisRegister F1024 Index) :
    inner Complex (wordXOperator word psi) (wordXOperator word chi) =
      inner Complex psi chi := by
  simp only [PiLp.inner_apply, wordXOperator_apply, RCLike.inner_apply']
  exact Fintype.sum_equiv (Equiv.addRight word)
    (fun label => star (psi (label + word)) * chi (label + word))
    (fun label => star (psi label) * chi label) (fun _ => rfl)
noncomputable def wordXTransport {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index) :
    UnitaryTransport (ComputationalBasisRegister F1024 Index)
      (ComputationalBasisRegister F1024 Index) where
  toLinearEquiv :=
    { toFun := wordXOperator word
      invFun := wordXOperator word
      left_inv := by
        intro psi
        ext label
        simp only [wordXOperator_apply]
        rw [add_word_add_word]
      right_inv := by
        intro psi
        ext label
        simp only [wordXOperator_apply]
        rw [add_word_add_word]
      map_add' := (wordXOperator word).map_add
      map_smul' := (wordXOperator word).map_smul }
  map_inner := wordXOperator_map_inner word
@[simp]
theorem wordXTransport_apply {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi : ComputationalBasisRegister F1024 Index)
    (label : ComputationalBasisRegisterLabel F1024 Index) :
    wordXTransport word psi label = psi (label + word) :=
  rfl
def tracePhase (x : F1024) : Complex :=
  additiveCharacter x
theorem tracePhase_add (x y : F1024) :
    tracePhase (x + y) = tracePhase x * tracePhase y :=
  additiveCharacter_add x y
theorem tracePhase_square (x : F1024) :
    tracePhase x * tracePhase x = 1 :=
  additiveCharacter_square x
theorem tracePhase_conj (x : F1024) :
    starRingEnd Complex (tracePhase x) = tracePhase x :=
  additiveCharacter_conj x
def wordZAmplitude {Index : Type} [Fintype Index]
    (word label : Why24Word Index) : Complex :=
  tracePhase (wordPairing word label)
noncomputable def wordZOperator {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index) :
    Operator (ComputationalBasisRegister F1024 Index) where
  toFun psi := WithLp.toLp 2 fun label => wordZAmplitude word label * psi label
  map_add' psi chi := by
    ext label
    change wordZAmplitude word label * (psi label + chi label) =
      wordZAmplitude word label * psi label + wordZAmplitude word label * chi label
    ring
  map_smul' c psi := by
    ext label
    change wordZAmplitude word label * (c * psi label) =
      c * (wordZAmplitude word label * psi label)
    ring
@[simp]
theorem wordZOperator_apply {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi : ComputationalBasisRegister F1024 Index)
    (label : ComputationalBasisRegisterLabel F1024 Index) :
    wordZOperator word psi label = wordZAmplitude word label * psi label :=
  rfl
theorem wordZOperator_map_inner {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi chi : ComputationalBasisRegister F1024 Index) :
    inner Complex (wordZOperator word psi) (wordZOperator word chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [wordZOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (wordZAmplitude word label * chi label) *
        (starRingEnd Complex (wordZAmplitude word label) *
          starRingEnd Complex (psi label)) =
      (wordZAmplitude word label * starRingEnd Complex (wordZAmplitude word label)) *
        (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      unfold wordZAmplitude
      rw [tracePhase_conj, tracePhase_square, one_mul]
noncomputable def wordZTransport {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index) :
    UnitaryTransport (ComputationalBasisRegister F1024 Index)
      (ComputationalBasisRegister F1024 Index) where
  toLinearEquiv :=
    { toFun := wordZOperator word
      invFun := wordZOperator word
      left_inv := by
        intro psi
        ext label
        simp only [wordZOperator_apply]
        rw [← mul_assoc]
        unfold wordZAmplitude
        rw [tracePhase_square, one_mul]
      right_inv := by
        intro psi
        ext label
        simp only [wordZOperator_apply]
        rw [← mul_assoc]
        unfold wordZAmplitude
        rw [tracePhase_square, one_mul]
      map_add' := (wordZOperator word).map_add
      map_smul' := (wordZOperator word).map_smul }
  map_inner := wordZOperator_map_inner word
@[simp]
theorem wordZTransport_apply {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi : ComputationalBasisRegister F1024 Index)
    (label : ComputationalBasisRegisterLabel F1024 Index) :
    wordZTransport word psi label = wordZAmplitude word label * psi label :=
  rfl
def logicalBasisWord (a : Logical) (value : F1024) : Why24Word Logical :=
  Pi.single a value
noncomputable def logicalXPhysical
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) :
    UnitaryTransport (ComputationalBasisRegister F1024 Site)
      (ComputationalBasisRegister F1024 Site) :=
  wordXTransport (beta • R.logicalRow a)
noncomputable def logicalXLogical
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) :
    UnitaryTransport (ComputationalBasisRegister F1024 Logical)
      (ComputationalBasisRegister F1024 Logical) :=
  wordXTransport (logicalBasisWord a beta)
noncomputable def logicalZPhysical
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) :
    UnitaryTransport (ComputationalBasisRegister F1024 Site)
      (ComputationalBasisRegister F1024 Site) :=
  wordZTransport (gamma • R.dualLogicalRow a)
noncomputable def logicalZLogical
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) :
    UnitaryTransport (ComputationalBasisRegister F1024 Logical)
      (ComputationalBasisRegister F1024 Logical) :=
  wordZTransport (logicalBasisWord a gamma)
theorem seventhExponent_eq_seventhPairing {Index : Type} [Fintype Index]
    (label : Why24Word Index) :
    seventhExponent label = seventhPairing label label label := by
  unfold seventhExponent seventhPairing
  apply Finset.sum_congr rfl
  intro index _
  ring
theorem fintype_sum_pow_two {Index : Type} [Fintype Index]
    (value : Index → F1024) :
    (∑ index : Index, value index) ^ 2 =
      ∑ index : Index, value index ^ 2 := by
  simpa using
    (sum_pow_char (R := F1024) (p := 2)
      (Finset.univ : Finset Index) value)
theorem fintype_sum_pow_four {Index : Type} [Fintype Index]
    (value : Index → F1024) :
    (∑ index : Index, value index) ^ 4 =
      ∑ index : Index, value index ^ 4 := by
  calc
    (∑ index : Index, value index) ^ 4 =
        ((∑ index : Index, value index) ^ 2) ^ 2 := by ring
    _ = (∑ index : Index, value index ^ 2) ^ 2 := by
      rw [fintype_sum_pow_two]
    _ = ∑ index : Index, (value index ^ 2) ^ 2 := by
      rw [fintype_sum_pow_two]
    _ = ∑ index : Index, value index ^ 4 := by
      apply Finset.sum_congr rfl
      intro index _
      ring
theorem fintype_sum_mul_sum_mul_sum {Index : Type} [Fintype Index]
    (first second third : Index → F1024) :
    (∑ index : Index, first index) * (∑ index : Index, second index) *
        (∑ index : Index, third index) =
      ∑ i : Index, ∑ j : Index, ∑ k : Index,
        first i * second j * third k := by
  calc
    (∑ index : Index, first index) * (∑ index : Index, second index) *
        (∑ index : Index, third index) =
        (∑ i : Index, ∑ j : Index, first i * second j) *
          (∑ index : Index, third index) := by
            congr 1
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ i : Index, (∑ j : Index, first i * second j) *
          (∑ index : Index, third index) := by rw [Finset.sum_mul]
    _ = ∑ i : Index, ∑ j : Index, ∑ k : Index,
          first i * second j * third k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
theorem fintype_sum_rotate_four
    {First Second Third Fourth : Type}
    [Fintype First] [Fintype Second] [Fintype Third] [Fintype Fourth]
    (value : First → Second → Third → Fourth → F1024) :
    (∑ fourth : Fourth, ∑ first : First, ∑ second : Second, ∑ third : Third,
        value first second third fourth) =
      ∑ first : First, ∑ second : Second, ∑ third : Third, ∑ fourth : Fourth,
        value first second third fourth := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second _
  rw [Finset.sum_comm]
theorem seventhPairing_sum_smul
    {RowIndex SiteIndex : Type} [Fintype RowIndex] [Fintype SiteIndex]
    (coefficient : RowIndex → F1024) (rowFamily : RowIndex → Why24Word SiteIndex) :
    seventhPairing
        (∑ row : RowIndex, coefficient row • rowFamily row)
        (∑ row : RowIndex, coefficient row • rowFamily row)
        (∑ row : RowIndex, coefficient row • rowFamily row) =
      ∑ first : RowIndex, ∑ second : RowIndex, ∑ third : RowIndex,
        coefficient first ^ 4 * coefficient second ^ 2 * coefficient third *
          seventhPairing (rowFamily first) (rowFamily second) (rowFamily third) := by
  unfold seventhPairing
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [fintype_sum_pow_four, fintype_sum_pow_two, mul_pow]
  conv_lhs =>
    enter [2, site]
    rw [fintype_sum_mul_sum_mul_sum]
  rw [fintype_sum_rotate_four]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro site _
  ring
theorem seventhPairing_combinedWord
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (coefficient : Logical ⊕ Stabilizer → F1024) :
    seventhPairing (R.combinedWord coefficient) (R.combinedWord coefficient)
        (R.combinedWord coefficient) =
      ∑ logical : Logical, coefficient (Sum.inl logical) ^ 7 := by
  unfold combinedWord
  rw [seventhPairing_sum_smul]
  change
    (∑ first : Logical ⊕ Stabilizer,
      ∑ second : Logical ⊕ Stabilizer,
      ∑ third : Logical ⊕ Stabilizer,
        coefficient first ^ 4 * coefficient second ^ 2 * coefficient third *
          seventhPairing (Sum.elim R.logicalRow R.stabilizerRow first)
            (Sum.elim R.logicalRow R.stabilizerRow second)
            (Sum.elim R.logicalRow R.stabilizerRow third)) = _
  simp_rw [R.seventh_condition]
  simp [seventhTarget, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro logical _
  rw [Finset.sum_eq_single logical]
  · rw [Finset.sum_eq_single logical]
    · simp
      ring
    · intro third _ hthird
      have hne : logical ≠ third := Ne.symm hthird
      simp [hne]
    · simp
  · intro second _ hsecond
    apply Finset.sum_eq_zero
    intro third _
    have hne : logical ≠ second := Ne.symm hsecond
    simp [hne]
  · simp
theorem seventhExponent_cosetLabel
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (h : R.StabilizerCarrier) :
    seventhExponent (R.cosetLabel u h) = ∑ logical : Logical, u logical ^ 7 := by
  classical
  obtain ⟨stabilizerCoefficient, hstabilizer⟩ :=
    (Submodule.mem_span_range_iff_exists_fun F1024).mp h.property
  let coefficient : Logical ⊕ Stabilizer → F1024 :=
    Sum.elim u stabilizerCoefficient
  have hcombined : R.combinedWord coefficient = R.cosetLabel u h := by
    unfold combinedWord cosetLabel logicalWord coefficient
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, row_inl, row_inr]
    rw [hstabilizer]
  rw [← hcombined, seventhExponent_eq_seventhPairing,
    R.seventhPairing_combinedWord]
  rfl
@[simp]
theorem tracePhase_zero : tracePhase 0 = 1 := by
  simp [tracePhase, additiveCharacter, fieldTrace,
    PauliSymplectic.binaryPhaseScalar]
theorem tracePhase_finset_sum {Index : Type} [DecidableEq Index]
    (indices : Finset Index) (value : Index → F1024) :
    tracePhase (∑ index ∈ indices, value index) =
      ∏ index ∈ indices, tracePhase (value index) := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex, tracePhase_add, Finset.prod_insert hindex, ih]
theorem tracePhase_fintype_sum {Index : Type} [Fintype Index]
    (value : Index → F1024) :
    tracePhase (∑ index : Index, value index) =
      ∏ index : Index, tracePhase (value index) := by
  classical
  simpa using tracePhase_finset_sum (Finset.univ : Finset Index) value
def uOneSevenAtAmplitude {Index : Type} (index : Index)
    (label : Why24Word Index) : Complex :=
  tracePhase (label index ^ 7)
noncomputable def uOneSevenAtOperator {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index) :
    Operator (ComputationalBasisRegister F1024 Index) where
  toFun psi := WithLp.toLp 2 fun label => uOneSevenAtAmplitude index label * psi label
  map_add' psi chi := by
    ext label
    change uOneSevenAtAmplitude index label * (psi label + chi label) =
      uOneSevenAtAmplitude index label * psi label +
        uOneSevenAtAmplitude index label * chi label
    ring
  map_smul' scalar psi := by
    ext label
    change uOneSevenAtAmplitude index label * (scalar * psi label) =
      scalar * (uOneSevenAtAmplitude index label * psi label)
    ring
@[simp]
theorem uOneSevenAtOperator_apply {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index)
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    uOneSevenAtOperator index psi label = uOneSevenAtAmplitude index label * psi label :=
  rfl
theorem uOneSevenAtOperator_map_inner {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index)
    (psi chi : ComputationalBasisRegister F1024 Index) :
    inner Complex (uOneSevenAtOperator index psi) (uOneSevenAtOperator index chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [uOneSevenAtOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (uOneSevenAtAmplitude index label * chi label) *
        (starRingEnd Complex (uOneSevenAtAmplitude index label) *
          starRingEnd Complex (psi label)) =
      (uOneSevenAtAmplitude index label *
          starRingEnd Complex (uOneSevenAtAmplitude index label)) *
        (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      unfold uOneSevenAtAmplitude
      rw [tracePhase_conj, tracePhase_square, one_mul]
noncomputable def uOneSevenAtTransport {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index) :
    UnitaryTransport (ComputationalBasisRegister F1024 Index)
      (ComputationalBasisRegister F1024 Index) where
  toLinearEquiv :=
    { toFun := uOneSevenAtOperator index
      invFun := uOneSevenAtOperator index
      left_inv := by
        intro psi
        ext label
        simp only [uOneSevenAtOperator_apply]
        rw [← mul_assoc]
        unfold uOneSevenAtAmplitude
        rw [tracePhase_square, one_mul]
      right_inv := by
        intro psi
        ext label
        simp only [uOneSevenAtOperator_apply]
        rw [← mul_assoc]
        unfold uOneSevenAtAmplitude
        rw [tracePhase_square, one_mul]
      map_add' := (uOneSevenAtOperator index).map_add
      map_smul' := (uOneSevenAtOperator index).map_smul }
  map_inner := uOneSevenAtOperator_map_inner index
@[simp]
theorem uOneSevenAtTransport_apply {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index)
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    uOneSevenAtTransport index psi label = uOneSevenAtAmplitude index label * psi label :=
  rfl
noncomputable def why24SiteEquivFin (Index : Type) [Fintype Index] :
    Fin (Fintype.card Index) ≃ Index :=
  (Fintype.equivFin Index).symm
noncomputable def registerUOneSeven {Index : Type}
    [Fintype Index] [DecidableEq Index] :
    UnitaryTransport (ComputationalBasisRegister F1024 Index)
      (ComputationalBasisRegister F1024 Index) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card Index) =>
    uOneSevenAtTransport (why24SiteEquivFin Index j)
theorem composeUOneSevenAtTransports_apply {Index : Type}
    [Fintype Index] [DecidableEq Index] (indices : List Index)
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    UnitaryTransport.composeList (indices.map uOneSevenAtTransport) psi label =
      (indices.map fun index => uOneSevenAtAmplitude index label).prod * psi label := by
  induction indices generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons index indices ih =>
      change UnitaryTransport.composeList (indices.map uOneSevenAtTransport)
          (uOneSevenAtTransport index psi) label = _
      rw [ih]
      simp only [uOneSevenAtTransport_apply, List.map_cons, List.prod_cons]
      ring
theorem registerUOneSeven_apply {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    registerUOneSeven psi label =
      (∏ index : Index, uOneSevenAtAmplitude index label) * psi label := by
  rw [registerUOneSeven, UnitaryTransport.composeFamily]
  have hlist :
      List.ofFn (fun j : Fin (Fintype.card Index) =>
        uOneSevenAtTransport (why24SiteEquivFin Index j)) =
        (List.ofFn (why24SiteEquivFin Index)).map uOneSevenAtTransport := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist, composeUOneSevenAtTransports_apply]
  rw [List.map_ofFn, Fin.prod_ofFn]
  congr 1
  exact Fintype.prod_equiv (why24SiteEquivFin Index) _ _ (fun _ => rfl)
theorem registerUOneSeven_apply_phase {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    registerUOneSeven psi label = tracePhase (seventhExponent label) * psi label := by
  rw [registerUOneSeven_apply]
  unfold uOneSevenAtAmplitude seventhExponent
  rw [tracePhase_fintype_sum]
theorem registerUOneSeven_apply_basis {Index : Type}
    [Fintype Index] [DecidableEq Index] (label : Why24Word Index) :
    registerUOneSeven (registerBasisKet label) =
      tracePhase (seventhExponent label) • registerBasisKet label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [registerUOneSeven_apply_phase, registerBasisKet,
      EuclideanSpace.basisFun_apply]
  · simp [registerUOneSeven_apply_phase, registerBasisKet,
      EuclideanSpace.basisFun_apply, htarget]
def why24CoordinateSupport {Index : Type} [DecidableEq Index]
    (index : Index) : Finset Index :=
  {index}
@[simp]
theorem why24CoordinateSupport_card {Index : Type} [DecidableEq Index]
    (index : Index) : (why24CoordinateSupport index).card = 1 := by
  simp [why24CoordinateSupport]
theorem why24CoordinateSupport_disjoint {Index : Type} [DecidableEq Index]
    {first second : Index} (hne : first ≠ second) :
    Disjoint (why24CoordinateSupport first) (why24CoordinateSupport second) := by
  simpa [why24CoordinateSupport] using (Finset.disjoint_singleton.mpr hne)
inductive UOneSevenLocalGate {Index : Type}
    [Fintype Index] [DecidableEq Index] : Finset Index → Type
  | at (index : Index) : UOneSevenLocalGate (why24CoordinateSupport index)
noncomputable def registerUOneSevenGateModel {Index : Type}
    [Fintype Index] [DecidableEq Index] :
    FinitePhysicalGateModel Index (ComputationalBasisRegister F1024 Index) where
  LocalGate := UOneSevenLocalGate
  realize gate := match gate with
    | .at index => uOneSevenAtTransport index
noncomputable def registerUOneSevenSitewiseFactorization {Index : Type}
    [Fintype Index] [DecidableEq Index] :
    SitewiseTransversalityData (registerUOneSevenGateModel (Index := Index))
      (registerUOneSeven (Index := Index)) where
  factorCount := Fintype.card Index
  support j := why24CoordinateSupport (why24SiteEquivFin Index j)
  factor j := .at (why24SiteEquivFin Index j)
  pairwise_disjoint := by
    intro i j hij
    exact why24CoordinateSupport_disjoint ((why24SiteEquivFin Index).injective.ne hij)
  realizes := rfl
  support_card_le_one := by
    intro j
    simp
noncomputable def physicalUOneSeven
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    UnitaryTransport (ComputationalBasisRegister F1024 Site)
      (ComputationalBasisRegister F1024 Site) :=
  registerUOneSeven
noncomputable def logicalUOneSeven
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    UnitaryTransport (ComputationalBasisRegister F1024 Logical)
      (ComputationalBasisRegister F1024 Logical) :=
  registerUOneSeven
noncomputable def physicalGateModel
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    FinitePhysicalGateModel Site (ComputationalBasisRegister F1024 Site) :=
  registerUOneSevenGateModel
noncomputable def physicalUOneSevenSitewiseFactorization
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    SitewiseTransversalityData R.physicalGateModel R.physicalUOneSeven :=
  registerUOneSevenSitewiseFactorization
theorem physicalUOneSeven_cosetKet
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.physicalUOneSeven (R.cosetKet u) =
      tracePhase (∑ logical : Logical, u logical ^ 7) • R.cosetKet u := by
  unfold physicalUOneSeven cosetKet
  rw [map_smul, map_sum]
  simp_rw [registerUOneSeven_apply_basis, R.seventhExponent_cosetLabel]
  change R.cosetNormalization •
      (∑ h : R.StabilizerCarrier,
        tracePhase (∑ logical : Logical, u logical ^ 7) •
          registerBasisKet (R.cosetLabel u h)) =
    tracePhase (∑ logical : Logical, u logical ^ 7) •
      (R.cosetNormalization •
        ∑ h : R.StabilizerCarrier, registerBasisKet (R.cosetLabel u h))
  rw [← Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_comm]
theorem physicalUOneSeven_intertwines_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.physicalUOneSeven (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalUOneSeven (registerBasisKet u)) := by
  rw [R.encodedCode_apply_logical_basis, R.physicalUOneSeven_cosetKet]
  unfold logicalUOneSeven
  rw [registerUOneSeven_apply_basis,
    R.encodedCode_encode_eq_encodingLinearMap, map_smul,
    R.encodingLinearMap_apply_logical_basis]
  rfl
theorem physicalUOneSeven_implements_logicalUOneSeven
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.encodedCode.ImplementsLogicalGate R.physicalUOneSeven R.logicalUOneSeven := by
  intro psi
  let encodeAmbient :
      ComputationalBasisRegister F1024 Logical →ₗ[Complex]
        ComputationalBasisRegister F1024 Site :=
    R.encodedCode.code.carrier.subtype.comp R.encodedCode.encoding.toLinearMap
  have hlinear :
      R.physicalUOneSeven.toLinearEquiv.toLinearMap.comp encodeAmbient =
        encodeAmbient.comp R.logicalUOneSeven.toLinearEquiv.toLinearMap := by
    apply (EuclideanSpace.basisFun (Logical → F1024) Complex).toBasis.ext
    intro u
    change R.physicalUOneSeven
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalUOneSeven (registerBasisKet u))
    exact R.physicalUOneSeven_intertwines_basis u
  exact LinearMap.congr_fun hlinear psi
noncomputable def sitewiseTransversalUOneSeven
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    SitewiseTransversalLogicalGate R.encodedCode R.logicalUOneSeven R.physicalGateModel where
  physicalGate := R.physicalUOneSeven
  implements := R.physicalUOneSeven_implements_logicalUOneSeven
  transversality := R.physicalUOneSevenSitewiseFactorization
end WeightedTriorthogonalMatrix
end QEC.Distillation.Why24WeightedTriorthogonalCSS


