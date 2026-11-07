-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
-- name    : QEC_Coding_Stabilizer_FiniteFieldPauli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T05:42:57.524608+00:00
-- url     : https://prove2.me/theorems/42993efb-7f1d-4b43-b6a1-7ff3fc1acd67
-- title:
--   Finite Field Pauli
-- statement:
--   Definitions and structural lemmas for Finite Field Pauli, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Coding_QLDPC_BPTMeasurementDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
namespace QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
abbrev Register (F : Type u) (ι : Type v) [Field F] [Fintype F] [Fintype ι] :=
  EuclideanSpace Complex (Word F ι)
def character (F : Type u) [Field F] [Fintype F] : AddChar F Complex :=
  AddChar.FiniteField.primitiveChar_to_Complex F
theorem character_isPrimitive : (character F).IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
theorem exists_character_mul_ne_one (a : F) (ha : a ≠ 0) :
    ∃ t : F, character F (a * t) ≠ 1 := by
  by_contra hnone
  have hall : ∀ t : F, character F (a * t) = 1 := by
    intro t
    by_contra ht
    exact hnone ⟨t, ht⟩
  have heq : (character F).mulShift a = 1 := by
    ext t
    simpa using hall t
  exact character_isPrimitive ha heq
def wordCharacter (z : Word F ι) : AddChar (Word F ι) Complex where
  toFun η := character F (wordPairing (F := F) (ι := ι) z η)
  map_zero_eq_one' := by simp [character]
  map_add_eq_mul' η ξ := by
    rw [(wordPairing (F := F) (ι := ι) z).map_add]
    exact AddChar.map_add_eq_mul _ _ _
theorem wordCharacter_injective :
    Function.Injective (wordCharacter (F := F) (ι := ι)) := by
  intro z w hzw
  have hpair : ∀ η : Word F ι,
      wordPairing (F := F) (ι := ι) z η =
        wordPairing (F := F) (ι := ι) w η := by
    intro η
    apply AddChar.to_mulShift_inj_of_isPrimitive
      (character_isPrimitive (F := F))
    ext t
    have hvalue := congrArg (fun φ : AddChar (Word F ι) Complex => φ (t • η)) hzw
    simpa [wordCharacter, AddChar.mulShift_apply, map_smul, mul_comm] using hvalue
  have hzero : z - w = 0 := by
    apply (wordPairing_nondegenerate (F := F) (ι := ι)).left
    intro η
    rw [LinearMap.BilinForm.sub_left]
    exact sub_eq_zero.mpr (hpair η)
  exact sub_eq_zero.mp hzero
noncomputable def wordCharacterEquiv :
    Word F ι ≃ AddChar (Word F ι) Complex := by
  classical
  apply Equiv.ofBijective (wordCharacter (F := F) (ι := ι))
  rw [Fintype.bijective_iff_injective_and_card,
    AddChar.card_eq]
  exact ⟨wordCharacter_injective, rfl⟩
noncomputable def wordCharacterBasis :
    Module.Basis (Word F ι) Complex (Word F ι → Complex) :=
  (AddChar.complexBasis (Word F ι)).reindex
    (wordCharacterEquiv (F := F) (ι := ι)).symm
@[simp] theorem wordCharacterBasis_apply (z η : Word F ι) :
    wordCharacterBasis (F := F) (ι := ι) z η =
      character F (wordPairing (F := F) (ι := ι) z η) := by
  simp [wordCharacterBasis, Module.Basis.reindex_apply, wordCharacterEquiv,
    wordCharacter]
def wordTranslate (t : Word F ι) :
    (Word F ι → Complex) →ₗ[Complex] (Word F ι → Complex) where
  toFun f := fun b => f (b + t)
  map_add' f g := by funext b; rfl
  map_smul' c f := by funext b; rfl
def shift (x : Word F ι) : Semantics.Operator (Register F ι) where
  toFun ψ := WithLp.toLp 2 (fun η => ψ (η + x))
  map_add' ψ φ := by
    ext η
    simp
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul]
@[simp] theorem shift_apply (x : Word F ι) (ψ : Register F ι) (η : Word F ι) :
    shift x ψ η = ψ (η + x) := rfl
def phase (z : Word F ι) : Semantics.Operator (Register F ι) where
  toFun ψ := WithLp.toLp 2 (fun η =>
    character F (wordPairing (F := F) (ι := ι) z η) * ψ η)
  map_add' ψ φ := by
    ext η
    simp [mul_add]
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul, mul_left_comm]
@[simp] theorem phase_apply (z : Word F ι) (ψ : Register F ι) (η : Word F ι) :
    phase z ψ η = character F (wordPairing (F := F) (ι := ι) z η) * ψ η := rfl
@[simp] theorem shift_zero : shift (0 : Word F ι) = 1 := by
  ext ψ η
  simp
@[simp] theorem phase_zero : phase (0 : Word F ι) = 1 := by
  ext ψ η
  simp [character]
def cssCarrier (xCode zCode : LinearCode F ι) :
    Submodule Complex (Register F ι) :=
  (⨅ x : xCode.carrier, LinearMap.ker (shift x.1 - 1)) ⊓
    (⨅ z : zCode.carrier, LinearMap.ker (phase z.1 - 1))
def cssQuantumCode (xCode zCode : LinearCode F ι) :
    Semantics.QuantumCode (Register F ι) where
  carrier := cssCarrier xCode zCode
theorem mem_cssQuantumCode_iff (xCode zCode : LinearCode F ι)
    (ψ : Register F ι) :
    ψ ∈ (cssQuantumCode xCode zCode).carrier ↔
      (∀ x : Word F ι, x ∈ xCode.carrier → shift x ψ = ψ) ∧
      (∀ z : Word F ι, z ∈ zCode.carrier → phase z ψ = ψ) := by
  simp [cssQuantumCode, cssCarrier, LinearMap.mem_ker, sub_eq_zero]
def cosetKet (xCode : LinearCode F ι) (a : Word F ι) : Register F ι := by
  classical
  exact WithLp.toLp 2 (fun η => if η - a ∈ xCode.carrier then 1 else 0)
@[simp] theorem cosetKet_apply (xCode : LinearCode F ι) (a η : Word F ι) :
    cosetKet xCode a η = if η - a ∈ xCode.carrier then 1 else 0 := by
  classical
  rfl
theorem shift_cosetKet (xCode : LinearCode F ι) (a x : Word F ι)
    (hx : x ∈ xCode.carrier) :
    shift x (cosetKet xCode a) = cosetKet xCode a := by
  classical
  ext η
  rw [shift_apply, cosetKet_apply, cosetKet_apply]
  have hrewrite : η + x - a = (η - a) + x := by abel
  rw [hrewrite]
  have hmem : (η - a) + x ∈ xCode.carrier ↔ η - a ∈ xCode.carrier := by
    constructor
    · intro h
      have : (η - a) + x - x ∈ xCode.carrier := xCode.carrier.sub_mem h hx
      simpa using this
    · exact fun h => xCode.carrier.add_mem h hx
  by_cases h : η - a ∈ xCode.carrier <;> simp [h, hmem]
theorem phase_cosetKet (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (a : Word F ι) (ha : a ∈ zCode.dual.carrier)
    (z : Word F ι) (hz : z ∈ zCode.carrier) :
    phase z (cosetKet xCode a) = cosetKet xCode a := by
  ext η
  rw [phase_apply, cosetKet_apply]
  by_cases hu : η - a ∈ xCode.carrier
  · have huPair : wordPairing (F := F) (ι := ι) z (η - a) = 0 :=
      zCode.dual_orthogonal hz (horth hu)
    have haPair : wordPairing (F := F) (ι := ι) z a = 0 :=
      zCode.dual_orthogonal hz ha
    have hη : η = (η - a) + a := by abel
    have hpair : wordPairing (F := F) (ι := ι) z η = 0 := by
      conv_lhs => rw [hη]
      rw [(wordPairing (F := F) (ι := ι) z).map_add, huPair, haPair]
      simp
    simp [hu, hpair, character]
  · simp [hu]
def pauli (x z : Word F ι) : Semantics.Operator (Register F ι) :=
  shift x * phase z
@[simp] theorem pauli_apply (x z : Word F ι) (ψ : Register F ι)
    (η : Word F ι) :
    pauli x z ψ η =
      character F (wordPairing (F := F) (ι := ι) z (η + x)) * ψ (η + x) :=
  rfl
def matrixDiagonal (E : Semantics.Operator (Register F ι))
    (x b : Word F ι) : Complex :=
  E (EuclideanSpace.basisFun (Word F ι) Complex b) (b - x)
set_option maxHeartbeats 1000000 in
/-- The matrix diagonal of a tensor-local operator in native field coordinates. -/
def localMatrixDiagonal
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x b : Word F ι') : Complex :=
  matrixDiagonal (Semantics.FiniteAlphabet.localOperator S E) x b
@[simp] theorem matrixDiagonal_sum {α : Type*} (s : Finset α)
    (E : α → Semantics.Operator (Register F ι)) (x b : Word F ι) :
    matrixDiagonal (∑ a ∈ s, E a) x b =
      ∑ a ∈ s, matrixDiagonal (E a) x b := by
  simp [matrixDiagonal]
@[simp] theorem matrixDiagonal_smul (c : Complex)
    (E : Semantics.Operator (Register F ι)) (x b : Word F ι) :
    matrixDiagonal (c • E) x b = c * matrixDiagonal E x b := by
  simp [matrixDiagonal, smul_eq_mul]
def pauliFourierCoefficient
    (E : Semantics.Operator (Register F ι))
    (x z : Word F ι) : Complex :=
  (wordCharacterBasis (F := F) (ι := ι)).repr
    (fun b => matrixDiagonal E x b) z
def pauliFourierReconstruction
    (E : Semantics.Operator (Register F ι)) :
    Semantics.Operator (Register F ι) :=
  ∑ x : Word F ι, ∑ z : Word F ι,
    pauliFourierCoefficient E x z • pauli x z
theorem label_mem_dual_of_phase_fixed (zCode : LinearCode F ι)
    (ψ : Register F ι)
    (hfixed : ∀ z : Word F ι, z ∈ zCode.carrier → phase z ψ = ψ)
    (η : Word F ι) (hψ : ψ η ≠ 0) :
    η ∈ zCode.dual.carrier := by
  apply (zCode.mem_dual η).2
  intro z hz
  have hpair : wordPairing (F := F) (ι := ι) z η = 0 := by
    by_contra hne
    obtain ⟨t, ht⟩ := exists_character_mul_ne_one
      (wordPairing (F := F) (ι := ι) z η) hne
    have hscaled : t • z ∈ zCode.carrier := zCode.carrier.smul_mem t hz
    have hvalue := congrArg (fun φ : Register F ι => φ η)
      (hfixed (t • z) hscaled)
    rw [phase_apply] at hvalue
    have hpairscaled : wordPairing (F := F) (ι := ι) (t • z) η =
        wordPairing (F := F) (ι := ι) z η * t := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
    rw [hpairscaled] at hvalue
    have hchar : character F (wordPairing (F := F) (ι := ι) z η * t) = 1 := by
      apply mul_right_cancel₀ hψ
      simpa using hvalue
    exact ht hchar
  simpa [wordPairing_apply, dotProduct_comm] using hpair
theorem apply_add_eq_of_shift_fixed (ψ : Register F ι)
    (x : Word F ι) (hfixed : shift x ψ = ψ) (η : Word F ι) :
    ψ (η + x) = ψ η := by
  have hvalue := congrArg (fun φ : Register F ι => φ η) hfixed
  simpa using hvalue
theorem mem_cssQuantumCode_iff_support_and_coset_constant
    (xCode zCode : LinearCode F ι) (ψ : Register F ι) :
    ψ ∈ (cssQuantumCode xCode zCode).carrier ↔
      (∀ η : Word F ι, η ∉ zCode.dual.carrier → ψ η = 0) ∧
      (∀ η x : Word F ι, x ∈ xCode.carrier → ψ (η + x) = ψ η) := by
  constructor
  · intro hψ
    obtain ⟨hX, hZ⟩ := (mem_cssQuantumCode_iff xCode zCode ψ).1 hψ
    constructor
    · intro η hη
      by_contra hnonzero
      exact hη (label_mem_dual_of_phase_fixed zCode ψ hZ η hnonzero)
    · intro η x hx
      exact apply_add_eq_of_shift_fixed ψ x (hX x hx) η
  · rintro ⟨hsupport, hconstant⟩
    apply (mem_cssQuantumCode_iff xCode zCode ψ).2
    constructor
    · intro x hx
      ext η
      exact hconstant η x hx
    · intro z hz
      ext η
      rw [phase_apply]
      by_cases hη : η ∈ zCode.dual.carrier
      · have hpair : wordPairing (F := F) (ι := ι) z η = 0 :=
          zCode.dual_orthogonal hz hη
        simp [hpair, character]
      · rw [hsupport η hη]
        simp
theorem cosetKet_mem_cssQuantumCode (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (a : Word F ι) (ha : a ∈ zCode.dual.carrier) :
    cosetKet xCode a ∈ (cssQuantumCode xCode zCode).carrier := by
  rw [mem_cssQuantumCode_iff]
  constructor
  · intro x hx
    exact shift_cosetKet xCode a x hx
  · intro z hz
    exact phase_cosetKet xCode zCode horth a ha z hz
def pauliSupport [DecidableEq F] (x z : Word F ι) : Finset ι := by
  classical
  exact hammingSupport x ∪ hammingSupport z
def quotientCosetKet (xCode : LinearCode F ι)
    (q : Word F ι ⧸ xCode.carrier) : Register F ι :=
  cosetKet xCode (Quotient.out q)
theorem quotientCosetKet_apply_out (xCode : LinearCode F ι)
    (q r : Word F ι ⧸ xCode.carrier) :
    quotientCosetKet xCode q (Quotient.out r) = if q = r then 1 else 0 := by
  classical
  rw [quotientCosetKet, cosetKet_apply]
  have hq : (Quotient.out r - Quotient.out q ∈ xCode.carrier) ↔ r = q := by
    rw [← Submodule.Quotient.eq]
    simp only [Submodule.Quotient.mk_out]
  simp only [hq, eq_comm]
theorem quotientCosetKet_apply (xCode : LinearCode F ι)
    (q : Word F ι ⧸ xCode.carrier) (η : Word F ι) :
    quotientCosetKet xCode q η =
      if q = Submodule.Quotient.mk η then 1 else 0 := by
  classical
  rw [quotientCosetKet, cosetKet_apply]
  have hq : (η - Quotient.out q ∈ xCode.carrier) ↔
      Submodule.Quotient.mk η = q := by
    rw [← Submodule.Quotient.eq]
    simp only [Submodule.Quotient.mk_out]
  simp only [hq, eq_comm]
def AdmissibleCoset (xCode zCode : LinearCode F ι) :=
  {q : Word F ι ⧸ xCode.carrier // Quotient.out q ∈ zCode.dual.carrier}
instance instFintypeAdmissibleCoset (xCode zCode : LinearCode F ι) :
    Fintype (AdmissibleCoset xCode zCode) := by
  classical
  unfold AdmissibleCoset
  infer_instance
theorem out_mem_dual_iff (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (η : Word F ι) :
    Quotient.out (Submodule.Quotient.mk η : Word F ι ⧸ xCode.carrier)
      ∈ zCode.dual.carrier ↔ η ∈ zCode.dual.carrier := by
  have hmem : Quotient.out (Submodule.Quotient.mk η :
      Word F ι ⧸ xCode.carrier) - η ∈ zCode.dual.carrier := by
    apply horth
    apply (Submodule.Quotient.eq xCode.carrier).1
    exact (Submodule.Quotient.mk_out _).trans rfl
  constructor
  · intro h
    have : Quotient.out (Submodule.Quotient.mk η :
        Word F ι ⧸ xCode.carrier) -
        (Quotient.out (Submodule.Quotient.mk η :
          Word F ι ⧸ xCode.carrier) - η) ∈ zCode.dual.carrier :=
      zCode.dual.carrier.sub_mem h hmem
    simpa using this
  · intro h
    have : η + (Quotient.out (Submodule.Quotient.mk η :
        Word F ι ⧸ xCode.carrier) - η) ∈ zCode.dual.carrier :=
      zCode.dual.carrier.add_mem h hmem
    simpa using this
theorem admissibleCosetKet_mem_cssQuantumCode (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (q : AdmissibleCoset xCode zCode) :
    quotientCosetKet xCode q.1 ∈ (cssQuantumCode xCode zCode).carrier :=
  cosetKet_mem_cssQuantumCode xCode zCode horth (Quotient.out q.1) q.2
def admissibleCosetKet (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (q : AdmissibleCoset xCode zCode) :
    (cssQuantumCode xCode zCode).carrier :=
  ⟨quotientCosetKet xCode q.1,
    admissibleCosetKet_mem_cssQuantumCode xCode zCode horth q⟩
theorem quotientCosetKet_linearIndependent (xCode : LinearCode F ι) :
    LinearIndependent Complex (quotientCosetKet xCode) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have heval := congrArg (fun ψ : Register F ι => ψ (Quotient.out i)) hsum
  simpa [quotientCosetKet_apply_out, hi] using heval
theorem admissibleCosetKet_linearIndependent (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    LinearIndependent Complex (admissibleCosetKet xCode zCode horth) := by
  apply LinearIndependent.of_comp
    ((cssQuantumCode xCode zCode).carrier.subtype)
  exact (quotientCosetKet_linearIndependent xCode).comp Subtype.val
    Subtype.val_injective
theorem sum_admissibleCosetKet (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (ψ : (cssQuantumCode xCode zCode).carrier) :
    (∑ q : AdmissibleCoset xCode zCode,
      (ψ.1 (Quotient.out q.1)) • admissibleCosetKet xCode zCode horth q) = ψ := by
  classical
  apply Subtype.ext
  ext η
  have hsupport :=
    (mem_cssQuantumCode_iff_support_and_coset_constant xCode zCode ψ.1).1 ψ.2 |>.1
  by_cases hη : η ∈ zCode.dual.carrier
  · let qη : AdmissibleCoset xCode zCode :=
      ⟨Submodule.Quotient.mk η, (out_mem_dual_iff xCode zCode horth η).2 hη⟩
    have heq : ∀ q : AdmissibleCoset xCode zCode,
        (q.1 = Submodule.Quotient.mk η) ↔ q = qη := by
      intro q
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    have hconstant :=
      (mem_cssQuantumCode_iff_support_and_coset_constant xCode zCode ψ.1).1 ψ.2 |>.2
    have hrepr : ψ.1 (Quotient.out qη.1) = ψ.1 η := by
      have hmem : Quotient.out qη.1 - η ∈ xCode.carrier := by
        apply (Submodule.Quotient.eq xCode.carrier).1
        exact (Submodule.Quotient.mk_out _).trans rfl
      have hrewrite : Quotient.out qη.1 = η + (Quotient.out qη.1 - η) := by abel
      conv_lhs => rw [hrewrite]
      exact hconstant η _ hmem
    simp [admissibleCosetKet, quotientCosetKet_apply, heq, hrepr]
  · have hall : ∀ q : AdmissibleCoset xCode zCode,
        q.1 ≠ Submodule.Quotient.mk η := by
      intro q heq
      have hout : Quotient.out (Submodule.Quotient.mk η :
          Word F ι ⧸ xCode.carrier) ∈ zCode.dual.carrier := by
        rw [← heq]
        exact q.2
      exact hη ((out_mem_dual_iff xCode zCode horth η).1 hout)
    simp [admissibleCosetKet, quotientCosetKet_apply, hall, hsupport η hη]
theorem span_admissibleCosetKet (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    Submodule.span Complex (Set.range (admissibleCosetKet xCode zCode horth)) = ⊤ := by
  apply top_unique
  intro ψ _
  rw [← sum_admissibleCosetKet xCode zCode horth ψ]
  apply Submodule.sum_mem
  intro q _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q))
noncomputable def cssCosetBasis (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    Module.Basis (AdmissibleCoset xCode zCode) Complex
      (cssQuantumCode xCode zCode).carrier :=
  Module.Basis.mk (admissibleCosetKet_linearIndependent xCode zCode horth)
    (by rw [span_admissibleCosetKet xCode zCode horth])
def xWithinDual (xCode zCode : LinearCode F ι) :
    Submodule F zCode.dual.carrier :=
  xCode.carrier.comap zCode.dual.carrier.subtype
def dualQuotientToAdmissible (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (zCode.dual.carrier ⧸ xWithinDual xCode zCode) →
      AdmissibleCoset xCode zCode := by
  intro q
  refine Quotient.liftOn q (fun d =>
    ⟨Submodule.Quotient.mk d.1,
      (out_mem_dual_iff xCode zCode horth d.1).2 d.2⟩) ?_
  intro a b hab
  apply Subtype.ext
  apply (Submodule.Quotient.eq xCode.carrier).2
  have hmem := (Submodule.Quotient.eq (xWithinDual xCode zCode)).1
    (Quotient.sound hab)
  exact hmem
noncomputable def admissibleCosetEquivDualQuotient (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (zCode.dual.carrier ⧸ xWithinDual xCode zCode) ≃
      AdmissibleCoset xCode zCode := by
  apply Equiv.ofBijective (dualQuotientToAdmissible xCode zCode horth)
  constructor
  · intro a b hab
    revert hab
    refine Quotient.inductionOn₂ a b ?_
    intro da db hab'
    apply (Submodule.Quotient.eq (xWithinDual xCode zCode)).2
    have heq : (Submodule.Quotient.mk da.1 : Word F ι ⧸ xCode.carrier) =
        Submodule.Quotient.mk db.1 := congrArg Subtype.val hab'
    exact (Submodule.Quotient.eq xCode.carrier).1 heq
  · intro q
    refine ⟨Submodule.Quotient.mk ⟨Quotient.out q.1, q.2⟩, ?_⟩
    apply Subtype.ext
    change (Submodule.Quotient.mk (Quotient.out q.1) :
      Word F ι ⧸ xCode.carrier) = q.1
    exact Submodule.Quotient.mk_out q.1
def fieldLabelEquiv {ι' : Type u} [Fintype ι'] :
    Word F ι' ≃ Semantics.Qudit.Label (fun _ : ι' => Fintype.card F) :=
  Equiv.piCongrRight fun _ => Fintype.equivFin F
def registerUnitary {ι' : Type u} [Fintype ι'] :
    Semantics.UnitaryTransport (Register F ι')
      (Semantics.Qudit.QuditRegister (fun _ : ι' => Fintype.card F)) where
  toLinearEquiv := (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (fieldLabelEquiv (F := F) (ι' := ι'))).toLinearEquiv
  map_inner := (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (fieldLabelEquiv (F := F) (ι' := ι'))).inner_map_map
def restrictWordToRegion
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') : Word F S.SelectedCoordinates :=
  fun j => x j.1
def restrictWordToComplement
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') : Word F S.ComplementCoordinates :=
  fun j => x j.1
omit [Field F] in
@[simp]
theorem splitLabel_fieldLabelEquiv_first
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') :
    (S.splitLabel (fieldLabelEquiv (F := F) x)).1 =
      fieldLabelEquiv (F := F) (restrictWordToRegion S x) := by
  rfl
omit [Field F] in
@[simp]
theorem splitLabel_fieldLabelEquiv_second
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') :
    (S.splitLabel (fieldLabelEquiv (F := F) x)).2 =
      fieldLabelEquiv (F := F) (restrictWordToComplement S x) := by
  rfl
def selectedShift
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') : Semantics.Operator S.selectedSystem where
  toFun ψ := WithLp.toLp 2 (fun labels =>
    ψ (fieldLabelEquiv (F := F)
      ((fieldLabelEquiv (F := F)).symm labels + restrictWordToRegion S x)))
  map_add' ψ φ := by ext labels; simp
  map_smul' c ψ := by ext labels; simp [smul_eq_mul]
def selectedPhase
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (z : Word F ι') : Semantics.Operator S.selectedSystem where
  toFun ψ := WithLp.toLp 2 (fun labels =>
    character F (wordPairing (F := F) (ι := S.SelectedCoordinates)
      (restrictWordToRegion S z) ((fieldLabelEquiv (F := F)).symm labels)) *
        ψ labels)
  map_add' ψ φ := by ext labels; simp [mul_add]
  map_smul' c ψ := by ext labels; simp [smul_eq_mul, mul_left_comm]
def cssQuditCode {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι') :
    Semantics.QuantumCode
      (Semantics.Qudit.QuditRegister (fun _ : ι' => Fintype.card F)) :=
  (cssQuantumCode xCode zCode).transport (registerUnitary (F := F))
end QEC.Coding.FiniteFieldPauli


