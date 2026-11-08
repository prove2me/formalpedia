-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
-- name    : QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:07:37.918321+00:00
-- url     : https://prove2.me/theorems/e4daca24-2553-4aa6-b9ae-47f80e69e390
-- title:
--   Finite Field CSSPresentation
-- statement:
--   Definitions and structural lemmas for Finite Field CSSPresentation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldCSSPresentation.lean

import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_chainComplex_cssQuditCode_dimension_eq_pow_homology
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_extendLocalToRegister_selectedPhase
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_extendLocalToRegister_selectedShift
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_mem_chainComplex_cssQuantumCode_iff_elementaryChecks
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
import Theorems.Thm_QEC_Semantics_QuantumCode_mem_transport_carrier_iff_symm
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.FiniteFieldCSSPresentation
open QEC.Coding.FiniteFieldPauli
universe u
variable {F ι κ₀ κ₂ : Type u}
variable [Field F] [Fintype F]
variable [Fintype ι] [Fintype κ₀] [Fintype κ₂]
local instance _p2m_local_instance_10414ac4d3_24 : DecidableEq ι := Classical.decEq ι
abbrev CheckIndex (F κ₀ κ₂ : Type u) := Sum (κ₀ × F) (κ₂ × F)
def xCheckWord
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (p : κ₀ × F) : Word F ι :=
  wordLinearMapTranspose K.boundary1 (p.2 • canonicalBasisWord p.1)
def zCheckWord
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (p : κ₂ × F) : Word F ι :=
  K.boundary2 (p.2 • canonicalBasisWord p.1)
def wordRegion (x : Word F ι) :
    @Semantics.QuditSubsystem ι inferInstance (Classical.decEq ι)
      (fun _ : ι => Fintype.card F) where
  selected := hammingSupport x
theorem word_eq_zero_outside_wordRegion (x : Word F ι) :
    ∀ j, j ∉ (wordRegion x).selected → x j = 0 := by
  intro j hj
  simpa [wordRegion, hammingSupport] using hj
def check
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (c : CheckIndex F κ₀ κ₂) :
    @QLDPC.FiniteQuditCheck ι inferInstance (Classical.decEq ι)
      (Fintype.card F) :=
  match c with
  | Sum.inl p =>
      { region := wordRegion (xCheckWord K p)
        localOperator := selectedShift (wordRegion (xCheckWord K p)) (xCheckWord K p) }
  | Sum.inr p =>
      { region := wordRegion (zCheckWord K p)
        localOperator := selectedPhase (wordRegion (zCheckWord K p)) (zCheckWord K p) }
omit [Fintype κ₂] in
/-- An elementary X check extends to its transported global shift. -/
theorem check_inl_globalOperator
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (p : κ₀ × F) :
    (check K (Sum.inl p)).globalOperator =
      (registerUnitary (F := F) (ι' := ι)).conjOperator (shift (xCheckWord K p)) := by
  change (wordRegion (xCheckWord K p)).extendLocalToRegister
      (selectedShift (wordRegion (xCheckWord K p)) (xCheckWord K p)) = _
  exact extendLocalToRegister_selectedShift
    (wordRegion (xCheckWord K p)) (xCheckWord K p)
      (word_eq_zero_outside_wordRegion (xCheckWord K p))
omit [Fintype κ₂] in
/-- An elementary Z check extends to its transported global phase. -/
theorem check_inr_globalOperator
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (p : κ₂ × F) :
    (check K (Sum.inr p)).globalOperator =
      (registerUnitary (F := F) (ι' := ι)).conjOperator (phase (zCheckWord K p)) := by
  change (wordRegion (zCheckWord K p)).extendLocalToRegister
      (selectedPhase (wordRegion (zCheckWord K p)) (zCheckWord K p)) = _
  exact extendLocalToRegister_selectedPhase
    (wordRegion (zCheckWord K p)) (zCheckWord K p)
      (word_eq_zero_outside_wordRegion (zCheckWord K p))
theorem mem_cssQuditCode_iff_elementaryChecks
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (ψ : Semantics.Qudit.QuditRegister (fun _ : ι => Fintype.card F)) :
    ψ ∈ (cssQuditCode K.firstCoboundaryCheckCode K.middleBoundaryCode).carrier ↔
      ∀ c : CheckIndex F κ₀ κ₂, (check K c).globalOperator ψ = ψ := by
  let U := registerUnitary (F := F) (ι' := ι)
  change ψ ∈ ((cssQuantumCode K.firstCoboundaryCheckCode
    K.middleBoundaryCode).transport U).carrier ↔ _
  rw [Semantics.QuantumCode.mem_transport_carrier_iff_symm]
  rw [mem_chainComplex_cssQuantumCode_iff_elementaryChecks]
  constructor
  · rintro ⟨hX, hZ⟩ c
    cases c with
    | inl p =>
        rw [check_inl_globalOperator]
        change U.toLinearEquiv
          (shift (xCheckWord K p) (U.toLinearEquiv.symm ψ)) = ψ
        simp only [xCheckWord]
        rw [hX p.1 p.2]
        exact U.toLinearEquiv.apply_symm_apply ψ
    | inr p =>
        rw [check_inr_globalOperator]
        change U.toLinearEquiv
          (phase (zCheckWord K p) (U.toLinearEquiv.symm ψ)) = ψ
        simp only [zCheckWord]
        rw [hZ p.1 p.2]
        exact U.toLinearEquiv.apply_symm_apply ψ
  · intro hfixed
    constructor
    · intro k a
      have h := hfixed (Sum.inl (k, a))
      rw [check_inl_globalOperator] at h
      have h' := congrArg U.toLinearEquiv.symm h
      simpa [xCheckWord, U] using h'
    · intro k a
      have h := hfixed (Sum.inr (k, a))
      rw [check_inr_globalOperator] at h
      have h' := congrArg U.toLinearEquiv.symm h
      simpa [zCheckWord, U] using h'
def presentation
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    @QLDPC.FiniteQuditCheckPresentation ι (CheckIndex F κ₀ κ₂)
      inferInstance (Classical.decEq ι) inferInstance where
  alphabetSize := Fintype.card F
  alphabetSize_ge_two := by
    exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  code := cssQuditCode K.firstCoboundaryCheckCode K.middleBoundaryCode
  checks := check K
  carrier_iff_fixed := by
    intro ψ
    exact mem_cssQuditCode_iff_elementaryChecks K ψ
  encodedQudits := Module.finrank F K.middleHomology
  dimension_eq := chainComplex_cssQuditCode_dimension_eq_pow_homology K
def baseCheckIndex : CheckIndex F κ₀ κ₂ → Sum κ₀ κ₂
  | Sum.inl p => Sum.inl p.1
  | Sum.inr p => Sum.inr p.1
def checkIndexEquiv : CheckIndex F κ₀ κ₂ ≃ (Sum κ₀ κ₂) × F where
  toFun c := (baseCheckIndex c,
    match c with
    | Sum.inl p => p.2
    | Sum.inr p => p.2)
  invFun p :=
    match p.1 with
    | Sum.inl k => Sum.inl (k, p.2)
    | Sum.inr l => Sum.inr (l, p.2)
  left_inv := by rintro (⟨k, a⟩ | ⟨l, a⟩) <;> rfl
  right_inv := by rintro ⟨k | l, a⟩ <;> rfl
end QEC.Coding.FiniteFieldCSSPresentation


