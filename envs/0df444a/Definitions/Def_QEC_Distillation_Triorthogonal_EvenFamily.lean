-- Prove2me | Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
-- name    : QEC_Distillation_Triorthogonal_EvenFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:25:22.194429+00:00
-- url     : https://prove2.me/theorems/fab80820-3688-443e-a98a-eadcff75a912
-- title:
--   Even Family
-- statement:
--   Definitions and structural lemmas for Even Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_cssQuantumCode_finrank_carrier
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_evenCode_disjoint_oddCode
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
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
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
abbrev OddRow (q : Nat) := Fin q × Fin 2
abbrev EvenRow := Fin 3
abbrev Column (q : Nat) := Sum (Fin 4) (Sum (Fin 4) (Fin q × Fin 6))
def logicalCount (q : Nat) : Nat := 2 * q
@[simp] theorem card_oddRow (q : Nat) :
    Fintype.card (OddRow q) = logicalCount q := by
  simp [OddRow, logicalCount, Nat.mul_comm]
@[simp] theorem card_evenRow : Fintype.card EvenRow = 3 := by
  simp [EvenRow]
@[simp] theorem card_column (q : Nat) :
    Fintype.card (Column q) = 3 * logicalCount q + 8 := by
  simp [Column, logicalCount]
  omega
@[simp] theorem card_row (q : Nat) :
    Fintype.card (Sum (OddRow q) EvenRow) = logicalCount q + 3 := by
  simp [logicalCount, Nat.mul_comm]
def leftBlock (_ : Fin 2) (_ : Fin 4) : ZMod 2 := 1
def oddBlock : Fin 2 → Fin 6 → ZMod 2 :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]
def evenFourBlock : Fin 3 → Fin 4 → ZMod 2 :=
  !![0, 1, 0, 1;
     0, 0, 1, 1;
     1, 1, 1, 1]
def evenSixBlock : Fin 3 → Fin 6 → ZMod 2 :=
  !![1, 0, 1, 1, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 0]
def oddWord {q : Nat} (a : OddRow q) : Word (ZMod 2) (Column q)
  | .inl _ => 0
  | .inr (.inl c) => leftBlock a.2 c
  | .inr (.inr jc) => if jc.1 = a.1 then oddBlock a.2 jc.2 else 0
def evenWord {q : Nat} (r : EvenRow) : Word (ZMod 2) (Column q)
  | .inl c => evenFourBlock r c
  | .inr (.inl c) => evenFourBlock r c
  | .inr (.inr jc) => evenSixBlock r jc.2
def family (q : Nat) : BinaryRowFamily (OddRow q) EvenRow (Column q) where
  oddRow := oddWord
  evenRow := evenWord
theorem oddBlock_self_sum (b : Fin 2) :
    (∑ c, (oddBlock b c * oddBlock b c).val) = 3 := by
  fin_cases b <;> decide +kernel
theorem evenFour_self_sum (r : Fin 3) :
    (∑ c, (evenFourBlock r c * evenFourBlock r c).val) = ![2, 2, 4] r := by
  fin_cases r <;> decide +kernel
theorem evenSix_self_sum (r : Fin 3) :
    (∑ c, (evenSixBlock r c * evenSixBlock r c).val) = ![4, 4, 0] r := by
  fin_cases r <;> decide +kernel
theorem sum_block_ite_self {q : Nat} (i j : Fin q) (b : Fin 2) :
    (∑ c : Fin 6,
      ((if j = i then oddBlock b c else 0) *
        (if j = i then oddBlock b c else 0)).val) =
      if j = i then 3 else 0 := by
  by_cases h : j = i
  · simp [h, oddBlock_self_sum]
  · simp [h]
theorem evenRows_linearIndependent (q : Nat) :
    LinearIndependent (ZMod 2) (@evenWord q) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have h0 := congrFun hc (Sum.inl (0 : Fin 4))
  have h1 := congrFun hc (Sum.inl (1 : Fin 4))
  have h2 := congrFun hc (Sum.inl (2 : Fin 4))
  simp [evenWord, evenFourBlock, Fin.sum_univ_succ] at h0 h1 h2
  fin_cases a
  · simpa [h0] using h1
  · simpa [h0] using h2
  · exact h0
theorem left_pair_sum (b d : Fin 2) :
    (∑ c, (leftBlock b c * leftBlock d c).val) = 4 := by
  fin_cases b <;> fin_cases d <;> decide +kernel
theorem left_triple_sum (b d e : Fin 2) :
    (∑ c, (leftBlock b c * leftBlock d c * leftBlock e c).val) = 4 := by
  fin_cases b <;> fin_cases d <;> fin_cases e <;> decide +kernel
theorem oddBlock_pair_sum (b d : Fin 2) :
    (∑ c, (oddBlock b c * oddBlock d c).val) = if b = d then 3 else 0 := by
  fin_cases b <;> fin_cases d <;> decide +kernel
theorem oddBlock_triple_sum (b d e : Fin 2) :
    (∑ c, (oddBlock b c * oddBlock d c * oddBlock e c).val) =
      if b = d ∧ d = e then 3 else 0 := by
  fin_cases b <;> fin_cases d <;> fin_cases e <;> decide +kernel
theorem left_even_pair_sum (b : Fin 2) (r : Fin 3) :
    (∑ c, (leftBlock b c * evenFourBlock r c).val) = ![2, 2, 4] r := by
  fin_cases b <;> fin_cases r <;> decide +kernel
theorem odd_even_pair_sum (b : Fin 2) (r : Fin 3) :
    (∑ c, (oddBlock b c * evenSixBlock r c).val) = ![2, 2, 0] r := by
  fin_cases b <;> fin_cases r <;> decide +kernel
theorem evenFour_pair_sum (r s : Fin 3) :
    (∑ c, (evenFourBlock r c * evenFourBlock s c).val) =
      !![2, 1, 2; 1, 2, 2; 2, 2, 4] r s := by
  fin_cases r <;> fin_cases s <;> decide +kernel
theorem evenSix_pair_sum (r s : Fin 3) :
    (∑ c, (evenSixBlock r c * evenSixBlock s c).val) =
      !![4, 2, 0; 2, 4, 0; 0, 0, 0] r s := by
  fin_cases r <;> fin_cases s <;> decide +kernel
theorem left_left_even_triple_sum (b d : Fin 2) (r : Fin 3) :
    (∑ c, (leftBlock b c * leftBlock d c * evenFourBlock r c).val) =
      ![2, 2, 4] r := by
  fin_cases b <;> fin_cases d <;> fin_cases r <;> decide +kernel
theorem odd_odd_even_triple_sum (b d : Fin 2) (r : Fin 3) :
    (∑ c, (oddBlock b c * oddBlock d c * evenSixBlock r c).val) =
      if b = d then ![2, 2, 0] r else 0 := by
  fin_cases b <;> fin_cases d <;> fin_cases r <;> decide +kernel
theorem left_even_even_triple_sum (b : Fin 2) (r s : Fin 3) :
    (∑ c, (leftBlock b c * evenFourBlock r c * evenFourBlock s c).val) =
      !![2, 1, 2; 1, 2, 2; 2, 2, 4] r s := by
  fin_cases b <;> fin_cases r <;> fin_cases s <;> decide +kernel
theorem odd_even_even_triple_sum (b : Fin 2) (r s : Fin 3) :
    (∑ c, (oddBlock b c * evenSixBlock r c * evenSixBlock s c).val) =
      !![2, 1, 0; 1, 2, 0; 0, 0, 0] r s := by
  fin_cases b <;> fin_cases r <;> fin_cases s <;> decide +kernel
theorem evenFour_triple_sum_of_distinct (r s t : Fin 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (∑ c, (evenFourBlock r c * evenFourBlock s c * evenFourBlock t c).val) = 1 := by
  fin_cases r <;> fin_cases s <;> fin_cases t <;> simp_all <;> decide +kernel
theorem evenSix_triple_sum_of_distinct (r s t : Fin 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (∑ c, (evenSixBlock r c * evenSixBlock s c * evenSixBlock t c).val) = 0 := by
  fin_cases r <;> fin_cases s <;> fin_cases t <;> simp_all <;> decide +kernel
theorem oddOdd_block_pair {q : Nat} (i j u : Fin q) (b d : Fin 2) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) *
        (if u = j then oddBlock d c else 0)).val) =
      if u = i ∧ u = j then (if b = d then 3 else 0) else 0 := by
  by_cases hui : u = i
  · subst i
    by_cases huj : u = j
    · subst j
      simp [oddBlock_pair_sum]
    · simp [huj]
  · by_cases huj : u = j
    · subst j
      simp [hui]
    · simp [hui, huj]
theorem oddEven_block_pair {q : Nat} (i u : Fin q) (b : Fin 2) (r : Fin 3) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) * evenSixBlock r c).val) =
      if u = i then ![2, 2, 0] r else 0 := by
  by_cases hui : u = i <;> simp [hui, odd_even_pair_sum]
theorem oddOddOdd_block_triple {q : Nat}
    (i j l u : Fin q) (b d e : Fin 2) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) *
        (if u = j then oddBlock d c else 0) *
        (if u = l then oddBlock e c else 0)).val) =
      if u = i ∧ u = j ∧ u = l then
        (if b = d ∧ d = e then 3 else 0) else 0 := by
  by_cases hui : u = i
  · subst i
    by_cases huj : u = j
    · subst j
      by_cases hul : u = l
      · subst l
        simp [oddBlock_triple_sum]
      · simp [hul]
    · simp [huj]
  · simp [hui]
theorem oddOddEven_block_triple {q : Nat}
    (i j u : Fin q) (b d : Fin 2) (r : Fin 3) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) *
        (if u = j then oddBlock d c else 0) * evenSixBlock r c).val) =
      if u = i ∧ u = j then (if b = d then ![2, 2, 0] r else 0) else 0 := by
  by_cases hui : u = i
  · subst i
    by_cases huj : u = j
    · subst j
      simp [odd_odd_even_triple_sum]
    · simp [huj]
  · simp [hui]
theorem oddEvenEven_block_triple {q : Nat}
    (i u : Fin q) (b : Fin 2) (r s : Fin 3) :
    (∑ c : Fin 6,
      ((if u = i then oddBlock b c else 0) * evenSixBlock r c *
        evenSixBlock s c).val) =
      if u = i then !![2, 1, 0; 1, 2, 0; 0, 0, 0] r s else 0 := by
  by_cases hui : u = i <;> simp [hui, odd_even_even_triple_sum]
theorem oddWeight {q : Nat} (a : OddRow q) :
    HammingWeight (oddWord a) = 7 := by
  rw [← BinaryRowFamily.pairOverlap_self_eq_hammingWeight]
  simp only [BinaryRowFamily.pairOverlap, oddWord, leftBlock, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [sum_block_ite_self]
  simp
  decide
theorem evenWeight {q : Nat} (r : EvenRow) :
    HammingWeight (evenWord (q := q) r) = ![4 + 4 * q, 4 + 4 * q, 8] r := by
  rw [← BinaryRowFamily.pairOverlap_self_eq_hammingWeight]
  simp only [BinaryRowFamily.pairOverlap, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [evenFour_self_sum, evenSix_self_sum]
  fin_cases r <;> simp <;> omega
theorem oddOddPairOverlap {q : Nat} (a b : OddRow q) (hab : a ≠ b) :
    BinaryRowFamily.pairOverlap (oddWord a) (oddWord b) = 4 := by
  classical
  rcases a with ⟨i, u⟩
  rcases b with ⟨j, v⟩
  simp only [BinaryRowFamily.pairOverlap, oddWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddOdd_block_pair]
  rw [left_pair_sum]
  by_cases hij : i = j
  · have huv : u ≠ v := by
      intro huv
      exact hab (Prod.ext hij huv)
    simp [hij, huv]
  · simp [hij]
theorem oddEvenPairOverlap {q : Nat} (a : OddRow q) (r : EvenRow) :
    BinaryRowFamily.pairOverlap (oddWord a) (evenWord r) = 4 := by
  classical
  rcases a with ⟨i, b⟩
  simp only [BinaryRowFamily.pairOverlap, oddWord, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddEven_block_pair]
  rw [left_even_pair_sum]
  fin_cases r <;> simp
theorem evenEvenPairOverlap {q : Nat} (r s : EvenRow) (hrs : r ≠ s) :
    BinaryRowFamily.pairOverlap (evenWord (q := q) r) (evenWord s) =
      !![0, 2 + 2 * q, 4; 2 + 2 * q, 0, 4; 4, 4, 0] r s := by
  simp only [BinaryRowFamily.pairOverlap, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [evenFour_pair_sum, evenSix_pair_sum]
  fin_cases r <;> fin_cases s <;> simp_all <;> omega
theorem oddOddOddTripleOverlap {q : Nat} (a b c : OddRow q)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    BinaryRowFamily.tripleOverlap (oddWord a) (oddWord b) (oddWord c) = 4 := by
  classical
  rcases a with ⟨i, u⟩
  rcases b with ⟨j, v⟩
  rcases c with ⟨l, w⟩
  simp only [BinaryRowFamily.tripleOverlap, oddWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddOddOdd_block_triple]
  rw [left_triple_sum]
  have hzero : ∀ x : Fin q,
      (if x = i ∧ x = j ∧ x = l then
        (if u = v ∧ v = w then 3 else 0) else 0) = 0 := by
    intro x
    by_cases hidx : x = i ∧ x = j ∧ x = l
    · rcases hidx with ⟨hxi, hxj, hxl⟩
      have hij : i = j := hxi.symm.trans hxj
      have hil : i = l := hxi.symm.trans hxl
      have huv : u ≠ v := by intro h; exact hab (Prod.ext hij h)
      have huw : u ≠ w := by intro h; exact hac (Prod.ext hil h)
      fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all
    · simp [hidx]
  simp_rw [hzero]
  simp
theorem oddOddEvenTripleOverlap {q : Nat} (a b : OddRow q) (r : EvenRow)
    (hab : a ≠ b) :
    BinaryRowFamily.tripleOverlap (oddWord a) (oddWord b) (evenWord r) =
      ![2, 2, 4] r := by
  classical
  rcases a with ⟨i, u⟩
  rcases b with ⟨j, v⟩
  simp only [BinaryRowFamily.tripleOverlap, oddWord, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddOddEven_block_triple]
  rw [left_left_even_triple_sum]
  by_cases hij : i = j
  · have huv : u ≠ v := by intro h; exact hab (Prod.ext hij h)
    simp [hij, huv]
  · simp [hij]
theorem oddEvenEvenTripleOverlap {q : Nat} (a : OddRow q) (r s : EvenRow)
    (hrs : r ≠ s) :
    BinaryRowFamily.tripleOverlap (oddWord a) (evenWord r) (evenWord s) = 2 := by
  classical
  rcases a with ⟨i, b⟩
  simp only [BinaryRowFamily.tripleOverlap, oddWord, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp_rw [oddEvenEven_block_triple]
  rw [left_even_even_triple_sum]
  fin_cases r <;> fin_cases s <;> simp_all
theorem evenEvenEvenTripleOverlap {q : Nat} (r s t : EvenRow)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    BinaryRowFamily.tripleOverlap (evenWord (q := q) r) (evenWord s) (evenWord t) = 2 := by
  simp only [BinaryRowFamily.tripleOverlap, evenWord, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  rw [evenFour_triple_sum_of_distinct r s t hrs hrt hst]
  simp_rw [evenSix_triple_sum_of_distinct r s t hrs hrt hst]
  simp
theorem pairOverlap_comm {q : Nat} (x y : Word (ZMod 2) (Column q)) :
    BinaryRowFamily.pairOverlap x y = BinaryRowFamily.pairOverlap y x := by
  classical
  simp [BinaryRowFamily.pairOverlap, mul_comm]
theorem tripleOverlap_swap12 {q : Nat}
    (x y z : Word (ZMod 2) (Column q)) :
    BinaryRowFamily.tripleOverlap x y z = BinaryRowFamily.tripleOverlap y x z := by
  classical
  simp [BinaryRowFamily.tripleOverlap, mul_comm]
theorem tripleOverlap_swap23 {q : Nat}
    (x y z : Word (ZMod 2) (Column q)) :
    BinaryRowFamily.tripleOverlap x y z = BinaryRowFamily.tripleOverlap x z y := by
  classical
  simp [BinaryRowFamily.tripleOverlap, mul_comm, mul_left_comm]
theorem even_two_or_four (r : Fin 3) : Even (![2, 2, 4] r) := by
  fin_cases r
  · exact ⟨1, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
theorem isTriorthogonal (q : Nat) : (family q).IsTriorthogonal := by
  classical
  refine
    { odd_weight := ?_
      even_weight := ?_
      pair_even := ?_
      triple_even := ?_ }
  · intro a
    change Odd (HammingWeight (oddWord a))
    rw [oddWeight]
    exact ⟨3, rfl⟩
  · intro r
    change Even (HammingWeight (evenWord r))
    rw [evenWeight]
    fin_cases r
    · simpa using (show Even (4 + 4 * q) from ⟨2 + 2 * q, by omega⟩)
    · simpa using (show Even (4 + 4 * q) from ⟨2 + 2 * q, by omega⟩)
    · simpa using (show Even 8 from ⟨4, rfl⟩)
  · intro a b hab
    rcases a with a | r <;> rcases b with b | s
    all_goals simp only [family, BinaryRowFamily.row]
    · rw [oddOddPairOverlap a b (by simpa using hab)]
      exact ⟨2, rfl⟩
    · rw [oddEvenPairOverlap]
      exact ⟨2, rfl⟩
    · rw [pairOverlap_comm, oddEvenPairOverlap]
      exact ⟨2, rfl⟩
    · have hrs : r ≠ s := by simpa using hab
      rw [evenEvenPairOverlap r s hrs]
      fin_cases r <;> fin_cases s <;> simp_all
      all_goals first | exact ⟨1 + q, by omega⟩ | exact ⟨2, rfl⟩
  · intro a b c hab hac hbc
    rcases a with a | r <;> rcases b with b | s <;> rcases c with c | t
    all_goals simp only [family, BinaryRowFamily.row]
    · rw [oddOddOddTripleOverlap a b c (by simpa using hab)
        (by simpa using hac) (by simpa using hbc)]
      exact ⟨2, rfl⟩
    · rw [oddOddEvenTripleOverlap a b t (by simpa using hab)]
      exact even_two_or_four t
    · rw [tripleOverlap_swap23,
        oddOddEvenTripleOverlap a c s (by simpa using hac)]
      exact even_two_or_four s
    · rw [oddEvenEvenTripleOverlap a s t (by simpa using hbc)]
      exact ⟨1, rfl⟩
    · rw [tripleOverlap_swap12, tripleOverlap_swap23,
        oddOddEvenTripleOverlap b c r (by simpa using hbc)]
      exact even_two_or_four r
    · rw [tripleOverlap_swap12,
        oddEvenEvenTripleOverlap b r t (by simpa using hac)]
      exact ⟨1, rfl⟩
    · rw [tripleOverlap_swap12, tripleOverlap_swap23,
        tripleOverlap_swap12, tripleOverlap_swap23,
        oddEvenEvenTripleOverlap c r s (by simpa using hab)]
      exact ⟨1, rfl⟩
    · rw [evenEvenEvenTripleOverlap r s t (by simpa using hab)
        (by simpa using hac) (by simpa using hbc)]
      exact ⟨1, rfl⟩
theorem rows_linearIndependent (q : Nat) :
    LinearIndependent (ZMod 2) (family q).row := by
  have hOdd := (family q).oddRows_linearIndependent (isTriorthogonal q)
  have hDisjoint := (family q).evenCode_disjoint_oddCode (isTriorthogonal q)
  have hd : Disjoint
      (Submodule.span (ZMod 2) (Set.range (@oddWord q)))
      (Submodule.span (ZMod 2) (Set.range (@evenWord q))) := by
    simpa [BinaryRowFamily.oddCode, BinaryRowFamily.evenCode, family] using
      hDisjoint.symm
  have hrow : (family q).row = Sum.elim oddWord evenWord := by
    funext a
    rcases a with a | r <;> rfl
  rw [hrow]
  exact hOdd.sum_type (evenRows_linearIndependent q) hd
theorem cssLogicalExponent (q : Nat) :
    Length (ZMod 2) (Column q) - Dimension (family q).evenCode -
        Dimension (family q).rowCode.dual = logicalCount q := by
  simpa [logicalCount, Nat.mul_comm] using
    (family q).cssLogicalExponent_eq_card_oddRows (isTriorthogonal q)
theorem cssCarrierFinrank (q : Nat) :
    Module.finrank Complex (family q).cssQuantumCode.carrier = 2 ^ logicalCount q := by
  simpa [logicalCount, Nat.mul_comm] using
    (family q).cssQuantumCode_finrank_carrier (isTriorthogonal q)
def distanceWitness (q : Nat) : Word (ZMod 2) (Column q) :=
  Pi.single (Sum.inl (0 : Fin 4)) 1 +
    Pi.single (Sum.inr (Sum.inl (0 : Fin 4))) 1
@[simp] theorem zero_cssLogicalExponent :
    Length (ZMod 2) (Column 0) - Dimension (family 0).evenCode -
        Dimension (family 0).rowCode.dual = 0 := by
  simpa only [logicalCount, Nat.mul_zero] using cssLogicalExponent 0
@[simp] theorem zero_cssCarrierFinrank :
    Module.finrank Complex (family 0).cssQuantumCode.carrier = 1 := by
  simpa only [logicalCount, Nat.mul_zero, pow_zero] using cssCarrierFinrank 0
def evenCombination (q : Nat) (c : EvenRow → ZMod 2) : Word (ZMod 2) (Column q) :=
  Fintype.linearCombination (ZMod 2) (@evenWord q) c
def coefficientBits : Fin 8 → EvenRow → ZMod 2 :=
  !![0, 0, 0;
     1, 0, 0;
     0, 1, 0;
     1, 1, 0;
     0, 0, 1;
     1, 0, 1;
     0, 1, 1;
     1, 1, 1]
theorem coefficientBits_bijective : Function.Bijective coefficientBits := by
  decide +kernel
def coefficientEquiv : Fin 8 ≃ (EvenRow → ZMod 2) :=
  Equiv.ofBijective coefficientBits coefficientBits_bijective
def combineFour (c : EvenRow → ZMod 2) (j : Fin 4) : ZMod 2 :=
  ∑ r, c r * evenFourBlock r j
def combineSix (c : EvenRow → ZMod 2) (j : Fin 6) : ZMod 2 :=
  ∑ r, c r * evenSixBlock r j
@[simp] theorem evenCombination_first_apply (q : Nat)
    (c : EvenRow → ZMod 2) (j : Fin 4) :
    evenCombination q c (Sum.inl j) = combineFour c j := by
  simp [evenCombination, combineFour, evenWord, Fintype.linearCombination_apply]
@[simp] theorem evenCombination_second_apply (q : Nat)
    (c : EvenRow → ZMod 2) (j : Fin 4) :
    evenCombination q c (Sum.inr (Sum.inl j)) = combineFour c j := by
  simp [evenCombination, combineFour, evenWord, Fintype.linearCombination_apply]
@[simp] theorem evenCombination_six_apply (q : Nat)
    (c : EvenRow → ZMod 2) (i : Fin q) (j : Fin 6) :
    evenCombination q c (Sum.inr (Sum.inr (i, j))) = combineSix c j := by
  simp [evenCombination, combineSix, evenWord, Fintype.linearCombination_apply]
def oddCosetWord {q : Nat} (a : OddRow q) (i : Fin 8) :
    Word (ZMod 2) (Column q) :=
  evenCombination q (coefficientBits i) + oddWord a
@[simp] theorem oddCosetWord_first_apply {q : Nat}
    (a : OddRow q) (i : Fin 8) (j : Fin 4) :
    oddCosetWord a i (Sum.inl j) = combineFour (coefficientBits i) j := by
  simp [oddCosetWord, oddWord]
@[simp] theorem oddCosetWord_second_apply {q : Nat}
    (a : OddRow q) (i : Fin 8) (j : Fin 4) :
    oddCosetWord a i (Sum.inr (Sum.inl j)) =
      combineFour (coefficientBits i) j + 1 := by
  simp [oddCosetWord, oddWord, leftBlock]
@[simp] theorem oddCosetWord_six_apply {q : Nat}
    (a : OddRow q) (i : Fin 8) (u : Fin q) (j : Fin 6) :
    oddCosetWord a i (Sum.inr (Sum.inr (u, j))) =
      combineSix (coefficientBits i) j +
        (if u = a.1 then oddBlock a.2 j else 0) := by
  simp [oddCosetWord, oddWord]
theorem evenCombination_mem_evenCode (q : Nat) (c : EvenRow → ZMod 2) :
    evenCombination q c ∈ (family q).evenCode.carrier := by
  rw [evenCombination, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun r _ =>
    (family q).evenCode.carrier.smul_mem _ ((family q).evenRow_mem_evenCode r)
noncomputable def evenCombinationLinearMap (q : Nat) :
    (EvenRow → ZMod 2) →ₗ[ZMod 2] (family q).evenCode.carrier :=
  LinearMap.codRestrict (family q).evenCode.carrier
    (Fintype.linearCombination (ZMod 2) (@evenWord q))
    (evenCombination_mem_evenCode q)
@[simp] theorem coe_evenCombinationLinearMap_apply (q : Nat)
    (c : EvenRow → ZMod 2) :
    (evenCombinationLinearMap q c : Word (ZMod 2) (Column q)) = evenCombination q c :=
  rfl
theorem evenCombinationLinearMap_bijective (q : Nat) :
    Function.Bijective (evenCombinationLinearMap q) := by
  constructor
  · intro c d hcd
    apply (evenRows_linearIndependent q).fintypeLinearCombination_injective
    exact congrArg Subtype.val hcd
  · intro x
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp x.2
    refine ⟨c, Subtype.ext ?_⟩
    exact hc
noncomputable def evenCoefficientLinearEquiv (q : Nat) :
    (EvenRow → ZMod 2) ≃ₗ[ZMod 2] (family q).evenCode.carrier :=
  LinearEquiv.ofBijective (evenCombinationLinearMap q)
    (evenCombinationLinearMap_bijective q)
@[simp] theorem coe_evenCoefficientLinearEquiv_apply (q : Nat)
    (c : EvenRow → ZMod 2) :
    ((evenCoefficientLinearEquiv q c : (family q).evenCode.carrier) :
      Word (ZMod 2) (Column q)) = evenCombination q c :=
  rfl
def codeWeightSum {A : Type*} [AddCommMonoid A] {I : Type*}
    [Fintype I] [DecidableEq I] (C : LinearCode (ZMod 2) I) (f : Nat → A) : A :=
  letI : Fintype C.carrier := Fintype.ofFinite C.carrier
  ∑ x : C.carrier, f (HammingWeight (x : Word (ZMod 2) I))
def oddCosetWeightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) : A :=
  letI : Fintype (family q).evenCode.carrier := Fintype.ofFinite _
  ∑ x : (family q).evenCode.carrier,
    f (HammingWeight ((x : Word (ZMod 2) (Column q)) + oddWord a))
def extensionRow {q : Nat} (a : OddRow q) :
    Sum Unit EvenRow → Word (ZMod 2) (Column q)
  | .inl _ => oddWord a
  | .inr r => evenWord r
def singleOddExtensionCode {q : Nat} (a : OddRow q) : LinearCode (ZMod 2) (Column q) where
  carrier := Submodule.span (ZMod 2) (Set.range (extensionRow a))
def extensionEmbedding {q : Nat} (a : OddRow q) :
    Sum Unit EvenRow → Sum (OddRow q) EvenRow
  | .inl _ => .inl a
  | .inr r => .inr r
theorem extensionEmbedding_injective {q : Nat} (a : OddRow q) :
    Function.Injective (extensionEmbedding a) := by
  intro x y hxy
  rcases x with x | r <;> rcases y with y | s <;> simp_all [extensionEmbedding]
theorem extensionRows_linearIndependent {q : Nat} (a : OddRow q) :
    LinearIndependent (ZMod 2) (extensionRow a) := by
  have h := (rows_linearIndependent q).comp (extensionEmbedding a)
    (extensionEmbedding_injective a)
  have heq : extensionRow a = (family q).row ∘ extensionEmbedding a := by
    funext x
    rcases x with x | r <;> rfl
  rw [heq]
  exact h
def extensionCombination {q : Nat} (a : OddRow q)
    (c : Sum Unit EvenRow → ZMod 2) : Word (ZMod 2) (Column q) :=
  Fintype.linearCombination (ZMod 2) (extensionRow a) c
def extensionCoefficientBits : (ZMod 2 × Fin 8) → (Sum Unit EvenRow → ZMod 2)
  | (b, _), .inl _ => b
  | (_, i), .inr r => coefficientBits i r
theorem extensionCoefficientBits_bijective :
    Function.Bijective extensionCoefficientBits := by
  decide +kernel
def extensionCoefficientEquiv :
    (ZMod 2 × Fin 8) ≃ (Sum Unit EvenRow → ZMod 2) :=
  Equiv.ofBijective extensionCoefficientBits extensionCoefficientBits_bijective
theorem extensionCombination_mem {q : Nat} (a : OddRow q)
    (c : Sum Unit EvenRow → ZMod 2) :
    extensionCombination a c ∈ (singleOddExtensionCode a).carrier := by
  rw [extensionCombination, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun r _ =>
    (singleOddExtensionCode a).carrier.smul_mem _
      (Submodule.subset_span ⟨r, rfl⟩)
noncomputable def extensionCombinationLinearMap {q : Nat} (a : OddRow q) :
    (Sum Unit EvenRow → ZMod 2) →ₗ[ZMod 2] (singleOddExtensionCode a).carrier :=
  LinearMap.codRestrict (singleOddExtensionCode a).carrier
    (Fintype.linearCombination (ZMod 2) (extensionRow a))
    (extensionCombination_mem a)
theorem extensionCombinationLinearMap_bijective {q : Nat} (a : OddRow q) :
    Function.Bijective (extensionCombinationLinearMap a) := by
  constructor
  · intro c d hcd
    apply (extensionRows_linearIndependent a).fintypeLinearCombination_injective
    exact congrArg Subtype.val hcd
  · intro x
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp x.2
    exact ⟨c, Subtype.ext hc⟩
noncomputable def extensionCoefficientLinearEquiv {q : Nat} (a : OddRow q) :
    (Sum Unit EvenRow → ZMod 2) ≃ₗ[ZMod 2] (singleOddExtensionCode a).carrier :=
  LinearEquiv.ofBijective (extensionCombinationLinearMap a)
    (extensionCombinationLinearMap_bijective a)
def codeWeightEnumerator {I : Type*} [Fintype I] [DecidableEq I]
    (C : LinearCode (ZMod 2) I) : Polynomial Nat :=
  codeWeightSum C fun w => Polynomial.X ^ w
def oddCosetWeightEnumerator {q : Nat} (a : OddRow q) : Polynomial Nat :=
  oddCosetWeightSum a fun w => Polynomial.X ^ w
end QEC.Distillation.Triorthogonal.BH12EvenFamily


