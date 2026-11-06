-- Prove2me | Definitions.Def_QEC_Coding_CSS_ParityChecks
-- name    : QEC_Coding_CSS_ParityChecks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:49:06.766948+00:00
-- url     : https://prove2.me/theorems/e0c29d0f-8801-4f10-bd92-c2f73b76469f
-- title:
--   Parity Checks
-- statement:
--   Definitions and structural lemmas for Parity Checks, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/ParityChecks.lean

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSCheckSet_pairwise_commutes_iff_dual_le
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedGroup_pairwise_commutes
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
import Theorems.Thm_QEC_QLDPC_generatedStabilizer_cssXCheck_sum
import Theorems.Thm_QEC_QLDPC_generatedStabilizer_cssZCheck_sum
import Theorems.Thm_QEC_QLDPC_generatedStabilizer_of_generators_generated
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
open Classical
universe u v
noncomputable def parityCheckRow
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) (r : κ) : Word F ι :=
  wordLinearMapTranspose P (Pi.single r 1)
def parityCheckKernelCode
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) : LinearCode F ι where
  carrier := LinearMap.ker P
noncomputable def parityCheckRowCode
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) : LinearCode F ι where
  carrier := LinearMap.range (wordLinearMapTranspose P)
@[simp]
theorem mem_parityCheckKernelCode
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) (x : Word F ι) :
    x ∈ (parityCheckKernelCode P).carrier ↔ P x = 0 := by
  simp [parityCheckKernelCode]
@[simp]
theorem mem_parityCheckRowCode
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) (x : Word F ι) :
    x ∈ (parityCheckRowCode P).carrier ↔
      ∃ y : Word F κ, wordLinearMapTranspose P y = x := by
  simp [parityCheckRowCode]
theorem parityCheckRow_mem_rowCode
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) (r : κ) :
    parityCheckRow P r ∈ (parityCheckRowCode P).carrier := by
  exact (mem_parityCheckRowCode P _).2 ⟨Pi.single r 1, rfl⟩
theorem wordLinearMapTranspose_eq_sum_parityCheckRows
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) (y : Word F κ) :
    wordLinearMapTranspose P y =
      ∑ r : κ, y r • parityCheckRow P r := by
  calc
    wordLinearMapTranspose P y =
        wordLinearMapTranspose P (∑ r : κ, Pi.single r (y r)) := by
          rw [word_eq_sum_single y]
    _ = ∑ r : κ, wordLinearMapTranspose P (Pi.single r (y r)) := by
          rw [map_sum]
    _ = ∑ r : κ, y r • parityCheckRow P r := by
          apply Finset.sum_congr rfl
          intro r _hr
          simp only [parityCheckRow]
          rw [← map_smul]
          congr 1
          rw [← Pi.single_smul]
          simp
theorem mem_parityCheckRowCode_iff_exists_sum_rows
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) (x : Word F ι) :
    x ∈ (parityCheckRowCode P).carrier ↔
      ∃ y : Word F κ, x = ∑ r : κ, y r • parityCheckRow P r := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, wordLinearMapTranspose_eq_sum_parityCheckRows P y⟩
  · rintro ⟨y, rfl⟩
    exact (mem_parityCheckRowCode P _).2
      ⟨y, wordLinearMapTranspose_eq_sum_parityCheckRows P y⟩
theorem parityCheckRowCode_dual_eq_kernelCode
    {F : Type u} {ι κ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (P : Word F ι →ₗ[F] Word F κ) :
    (parityCheckRowCode P).dual = parityCheckKernelCode P := by
  have hcarrier : ((parityCheckRowCode P).dual).carrier =
      (parityCheckKernelCode P).carrier := by
    ext x
    constructor
    · intro hx
      change P x = 0
      funext r
      calc
        P x r = wordPairing (F := F) (ι := κ) (Pi.single r 1) (P x) := by
          simp [wordPairing_apply]
        _ = wordPairing (F := F) (ι := ι) (parityCheckRow P r) x := by
          exact (wordPairing_wordLinearMapTranspose P (Pi.single r 1) x).symm
        _ = wordPairing (F := F) (ι := ι) x (parityCheckRow P r) := by
          simp [wordPairing_apply, dotProduct_comm]
        _ = 0 :=
          ((parityCheckRowCode P).mem_dual x).1 hx
            (parityCheckRow P r) (parityCheckRow_mem_rowCode P r)
    · intro hx
      change P x = 0 at hx
      refine ((parityCheckRowCode P).mem_dual x).2 ?_
      intro c hc
      rcases (mem_parityCheckRowCode P c).1 hc with ⟨y, rfl⟩
      calc
        wordPairing (F := F) (ι := ι) x (wordLinearMapTranspose P y) =
            wordPairing (F := F) (ι := ι) (wordLinearMapTranspose P y) x := by
              simp [wordPairing_apply, dotProduct_comm]
        _ = wordPairing (F := F) (ι := κ) y (P x) :=
          wordPairing_wordLinearMapTranspose P y x
        _ = 0 := by rw [hx]; simp
  cases hrow : (parityCheckRowCode P).dual with
  | mk rowCarrier =>
      cases hkernel : parityCheckKernelCode P with
      | mk kernelCarrier =>
          rw [hrow, hkernel] at hcarrier
          change rowCarrier = kernelCarrier at hcarrier
          cases hcarrier
          rfl
theorem parityCheckRows_orthogonal_iff_rowCode_le_dual
    {F : Type u} {ι κP κQ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κP] [Fintype κQ]
    (P : Word F ι →ₗ[F] Word F κP)
    (Q : Word F ι →ₗ[F] Word F κQ) :
    (∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0) ↔
      (parityCheckRowCode P).carrier ≤ (parityCheckRowCode Q).dual.carrier := by
  constructor
  · intro horth z hz
    rw [parityCheckRowCode_dual_eq_kernelCode]
    have hrow : ∀ p, parityCheckRow P p ∈ (parityCheckKernelCode Q).carrier := by
      intro p
      rw [mem_parityCheckKernelCode]
      funext q
      calc
        Q (parityCheckRow P p) q =
            wordPairing (F := F) (ι := κQ) (Pi.single q 1)
              (Q (parityCheckRow P p)) := by
                simp [wordPairing_apply]
        _ = wordPairing (F := F) (ι := ι)
              (parityCheckRow Q q) (parityCheckRow P p) := by
                exact (wordPairing_wordLinearMapTranspose
                  Q (Pi.single q 1) (parityCheckRow P p)).symm
        _ = wordPairing (F := F) (ι := ι)
              (parityCheckRow P p) (parityCheckRow Q q) := by
                simp [wordPairing_apply, dotProduct_comm]
        _ = 0 := horth p q
    rcases (mem_parityCheckRowCode_iff_exists_sum_rows P z).1 hz with ⟨y, rfl⟩
    exact Submodule.sum_mem _ fun p _hp =>
      (parityCheckKernelCode Q).carrier.smul_mem (y p) (hrow p)
  · intro hle p q
    exact ((parityCheckRowCode Q).mem_dual (parityCheckRow P p)).1
      (hle (parityCheckRow_mem_rowCode P p))
      (parityCheckRow Q q) (parityCheckRow_mem_rowCode Q q)
namespace PauliSymplectic
variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]
noncomputable def binaryCSSParityCheckGenerators
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ) :
    Sum κP κQ → Binary ι
  | Sum.inl p => cssZCheck (parityCheckRow P p)
  | Sum.inr q => cssXCheck (parityCheckRow Q q)
omit [DecidableEq ι] in
/-- Each explicit parity-check row generator belongs to the oriented CSS check set. -/
theorem binaryCSSParityCheckGenerator_mem_checkSet
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (j : Sum κP κQ) :
    binaryCSSParityCheckGenerators P Q j ∈
      binaryCSSCheckSet (parityCheckRowCode Q) (parityCheckRowCode P) := by
  cases j with
  | inl p =>
      exact Or.inr ⟨parityCheckRow P p, parityCheckRow_mem_rowCode P p, rfl⟩
  | inr q =>
      exact Or.inl ⟨parityCheckRow Q q, parityCheckRow_mem_rowCode Q q, rfl⟩
theorem binaryCSSParityCheckGenerators_generate_cssXCheck
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    {x : Word (ZMod 2) ι} (hx : x ∈ (parityCheckRowCode Q).carrier) :
    GeneratedStabilizer (binaryCSSParityCheckGenerators P Q) (cssXCheck x) := by
  rcases (mem_parityCheckRowCode Q x).1 hx with ⟨y, rfl⟩
  have hterm : ∀ q ∈ (Finset.univ : Finset κQ),
      GeneratedStabilizer (binaryCSSParityCheckGenerators P Q)
        (cssXCheck (wordLinearMapTranspose Q (Pi.single q (y q)))) := by
    intro q _hq
    by_cases hq0 : y q = 0
    · have hzero : wordLinearMapTranspose Q (Pi.single q (y q)) = 0 := by
        simp [hq0]
      rw [hzero]
      simpa [binaryOne] using
        (GeneratedStabilizer.one (generators := binaryCSSParityCheckGenerators P Q))
    · have hq1 : y q = 1 := zmod_two_eq_one_of_ne_zero hq0
      simpa [binaryCSSParityCheckGenerators, parityCheckRow, hq1] using
        (GeneratedStabilizer.generator (generators := binaryCSSParityCheckGenerators P Q)
          (Sum.inr q))
  have hsum := QLDPC.generatedStabilizer_cssXCheck_sum
    (binaryCSSParityCheckGenerators P Q) Finset.univ
    (fun q : κQ => wordLinearMapTranspose Q (Pi.single q (y q))) hterm
  have hsum_eq :
      (∑ q : κQ, wordLinearMapTranspose Q (Pi.single q (y q))) =
        wordLinearMapTranspose Q y := by
    rw [← map_sum, word_eq_sum_single]
  rwa [hsum_eq] at hsum
theorem binaryCSSParityCheckGenerators_generate_cssZCheck
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    {z : Word (ZMod 2) ι} (hz : z ∈ (parityCheckRowCode P).carrier) :
    GeneratedStabilizer (binaryCSSParityCheckGenerators P Q) (cssZCheck z) := by
  rcases (mem_parityCheckRowCode P z).1 hz with ⟨y, rfl⟩
  have hterm : ∀ p ∈ (Finset.univ : Finset κP),
      GeneratedStabilizer (binaryCSSParityCheckGenerators P Q)
        (cssZCheck (wordLinearMapTranspose P (Pi.single p (y p)))) := by
    intro p _hp
    by_cases hp0 : y p = 0
    · have hzero : wordLinearMapTranspose P (Pi.single p (y p)) = 0 := by
        simp [hp0]
      rw [hzero]
      simpa [binaryOne] using
        (GeneratedStabilizer.one (generators := binaryCSSParityCheckGenerators P Q))
    · have hp1 : y p = 1 := zmod_two_eq_one_of_ne_zero hp0
      simpa [binaryCSSParityCheckGenerators, parityCheckRow, hp1] using
        (GeneratedStabilizer.generator (generators := binaryCSSParityCheckGenerators P Q)
          (Sum.inl p))
  have hsum := QLDPC.generatedStabilizer_cssZCheck_sum
    (binaryCSSParityCheckGenerators P Q) Finset.univ
    (fun p : κP => wordLinearMapTranspose P (Pi.single p (y p))) hterm
  have hsum_eq :
      (∑ p : κP, wordLinearMapTranspose P (Pi.single p (y p))) =
        wordLinearMapTranspose P y := by
    rw [← map_sum, word_eq_sum_single]
  rwa [hsum_eq] at hsum
theorem binaryCSSParityCheckGenerators_generate_check
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    {S : Binary ι}
    (hS : S ∈ binaryCSSCheckSet (parityCheckRowCode Q) (parityCheckRowCode P)) :
    GeneratedStabilizer (binaryCSSParityCheckGenerators P Q) S := by
  rcases hS with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · exact binaryCSSParityCheckGenerators_generate_cssXCheck P Q hx
  · exact binaryCSSParityCheckGenerators_generate_cssZCheck P Q hz
noncomputable def binaryCSSStabilizerCodeOfParityChecks
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0) :
    StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι) where
  stabilizers := binaryCSSCheckSet (parityCheckRowCode Q) (parityCheckRowCode P)
  code := binaryStabilizerCommonFixedQuantumCode
    (binaryCSSCheckSet (parityCheckRowCode Q) (parityCheckRowCode P))
  isotropic :=
    (binaryCSSCheckSet_pairwise_commutes_iff_dual_le
      (parityCheckRowCode Q) (parityCheckRowCode P)).2
      ((parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).1 horth)
theorem binaryCSSParityCheckGenerators_generate_generatedGroup
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0) :
    generatedStabilizerSet (binaryCSSParityCheckGenerators P Q) =
      (binaryCSSStabilizerCodeOfParityChecks P Q horth).generatedGroup := by
  classical
  let C := binaryCSSStabilizerCodeOfParityChecks P Q horth
  letI : Fintype {S : Binary ι // S ∈ C.stabilizers} := Fintype.ofFinite _
  ext S
  constructor
  · intro hS
    change GeneratedStabilizer (binaryCSSParityCheckGenerators P Q) S at hS
    unfold StabilizerCode.generatedGroup
    apply QLDPC.generatedStabilizer_of_generators_generated ?_ hS
    intro j
    exact GeneratedStabilizer.generator
      (generators := fun check : {T : Binary ι // T ∈ C.stabilizers} => check.1)
      (⟨binaryCSSParityCheckGenerators P Q j, by
        simpa [C, binaryCSSStabilizerCodeOfParityChecks,
          binaryCSSStabilizerCodeOfDualLe] using
          binaryCSSParityCheckGenerator_mem_checkSet P Q j⟩ :
        {T : Binary ι // T ∈ C.stabilizers})
  · intro hS
    unfold StabilizerCode.generatedGroup at hS
    change GeneratedStabilizer (binaryCSSParityCheckGenerators P Q) S
    apply QLDPC.generatedStabilizer_of_generators_generated ?_ hS
    intro check
    apply binaryCSSParityCheckGenerators_generate_check P Q
    have hcheck := check.2
    change check.1 ∈
      binaryCSSCheckSet (parityCheckRowCode Q) (parityCheckRowCode P) at hcheck
    exact hcheck
theorem binaryCSSStabilizerCodeOfParityChecks_spec
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0) :
    let C := binaryCSSStabilizerCodeOfParityChecks P Q horth
    C.stabilizers =
        binaryCSSCheckSet (parityCheckRowCode Q) (parityCheckRowCode P) ∧
    generatedStabilizerSet (binaryCSSParityCheckGenerators P Q) =
        C.generatedGroup ∧
    binarySign (ι := ι) 1 ∉ C.generatedGroup ∧
    (∀ A, A ∈ C.generatedGroup → ∀ B, B ∈ C.generatedGroup → Commutes A B) ∧
    ∀ ψ, ψ ∈ C.code.carrier ↔
      ∀ S, S ∈ C.generatedGroup → toQubitOperator S ψ = ψ := by
  let C := binaryCSSStabilizerCodeOfParityChecks P Q horth
  let hdual : (parityCheckRowCode P).carrier ≤
      (parityCheckRowCode Q).dual.carrier :=
    (parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).1 horth
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact binaryCSSParityCheckGenerators_generate_generatedGroup P Q horth
  · exact binarySign_one_not_mem_binaryCSSStabilizerCodeOfDualLe_generatedGroup
        (parityCheckRowCode Q) (parityCheckRowCode P) hdual
  · intro A hA B hB
    exact StabilizerCode.generatedGroup_pairwise_commutes C hA hB
  · intro ψ
    calc
      ψ ∈ C.code.carrier ↔
          ∀ S, S ∈ C.stabilizers → toQubitOperator S ψ = ψ := by
            simp [C, binaryCSSStabilizerCodeOfParityChecks]
      _ ↔ ∀ S, S ∈ C.generatedGroup → toQubitOperator S ψ = ψ :=
        (fixed_generatedGroup_iff_fixed_stabilizers C ψ).symm
theorem binaryCSSStabilizerCodeOfParityChecks_isSourceValidBinary
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0) :
    (binaryCSSStabilizerCodeOfParityChecks P Q horth).IsSourceValidBinary := by
  rcases binaryCSSStabilizerCodeOfParityChecks_spec P Q horth with
    ⟨_hchecks, _hgenerated, hsign, _hcommutes, hfixed⟩
  exact ⟨hsign, hfixed⟩
noncomputable def binaryCSSSourceValidStabilizerOfParityChecks
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0) :
    StabilizerCode.SourceValidBinary ι :=
  ⟨binaryCSSStabilizerCodeOfParityChecks P Q horth,
    binaryCSSStabilizerCodeOfParityChecks_isSourceValidBinary P Q horth⟩
end PauliSymplectic
end Coding
end QEC


