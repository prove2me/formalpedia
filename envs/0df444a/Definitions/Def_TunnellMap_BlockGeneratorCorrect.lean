-- Prove2me | Definitions.Def_TunnellMap_BlockGeneratorCorrect
-- name    : TunnellMap_BlockGeneratorCorrect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:27:56.108236+00:00
-- url     : https://prove2.me/theorems/26bae1ce-2db2-49d2-931b-5abad7c4fa83
-- title:
--   Block Generator Correct
-- statement:
--   Definitions and structural lemmas for Block Generator Correct, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean

import Definitions.Def_TunnellMap_BlockGenerator
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
import Theorems.Thm_TunnellMap_DirectionKey_lt_iff
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_OrderedGenerator_mem_orderedIndexList
import Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_nodup
import Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_pairwise
import Theorems.Thm_TunnellMap_OrderedGenerator_targetOfValid_lift
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_canonicalTargetLift_eq
import Theorems.Thm_TunnellMap_directionKeyExec_eq
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_directionKey_vsmul
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_isResidualTargetLift_iff
import Theorems.Thm_TunnellMap_keyLeExec_iff
import Theorems.Thm_TunnellMap_keyLtExec_iff
import Theorems.Thm_TunnellMap_minusVector_ne_zero
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_plus_minus_keys_ne
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_eq_self_of_content_one_of_oriented
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitiveKey_eq_directionKey
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_tripleContent_eq_tripleGcd
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.BlockGen.remainingTrace_initial
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList
attribute [local simp] TunnellMap.OrderedGenerator.mem_orderedIndexList
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.keyLeExec_iff
attribute [local simp] TunnellMap.keyLtExec_iff
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.qForm_vsmul
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.tripleLexLtExec_iff
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


set_option autoImplicit true
namespace TunnellMap
namespace BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
theorem mem_blockIndexList (n : ℤ) (F : OrthogonalFrame p) (h : ℤ)
    (i : GeneratorIndex) :
    i ∈ blockIndexList n F h ↔
      i.A = h ∧ i.q ∈ qValues n h ∧ i.b ∈ bValues n F h i.q ∧
        i.u ∈ rootValues F h i.q i.b := by
  simp only [blockIndexList, List.mem_flatMap, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨q, hq, b, hb, u, hu, hi⟩
    subst hi
    exact ⟨rfl, hq, hb, hu⟩
  · rintro ⟨hA, hq, hb, hu⟩
    exact ⟨i.q, hq, i.b, hb, i.u, hu, by cases i; simp_all⟩
theorem blockIndexList_nodup (n : ℤ) (F : OrthogonalFrame p) (h : ℤ) :
    (blockIndexList n F h).Nodup := by
  rw [blockIndexList, List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro q _
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro b _
      refine (Finset.sort_nodup _ _).map ?_
      intro u v huv
      exact congrArg GeneratorIndex.u huv
    · refine (Finset.sort_nodup (bValues n F h q) (· ≤ ·)).imp ?_
      intro b₁ b₂ hne
      simp only [Function.onFun]
      intro i hi₁ hi₂
      simp only [List.mem_map] at hi₁ hi₂
      obtain ⟨u₁, -, h₁⟩ := hi₁
      obtain ⟨u₂, -, h₂⟩ := hi₂
      exact hne (by
        have := congrArg GeneratorIndex.b (h₁.trans h₂.symm)
        simpa using this)
  · refine (Finset.sort_nodup (qValues n h) (· ≤ ·)).imp ?_
    intro q₁ q₂ hne
    simp only [Function.onFun]
    intro i hi₁ hi₂
    simp only [List.mem_flatMap, List.mem_map] at hi₁ hi₂
    obtain ⟨b₁, -, u₁, -, h₁⟩ := hi₁
    obtain ⟨b₂, -, u₂, -, h₂⟩ := hi₂
    exact hne (by
      have := congrArg GeneratorIndex.q (h₁.trans h₂.symm)
      simpa using this)
theorem mem_rawIndices_iff (n : ℤ) (F : OrthogonalFrame p) (i : GeneratorIndex) :
    i ∈ rawIndices n F ↔
      (1 ≤ i.A ∧ i.A ≤ hMax n) ∧ i ∈ blockIndexList n F i.A := by
  rw [mem_rawIndices, mem_blockIndexList]
  simp only [AValues, mem_intIcc, hMax, true_and]
theorem blockIndexList_q_ne_zero {n : ℤ} {F : OrthogonalFrame p} {h : ℤ}
    {i : GeneratorIndex} (hi : i ∈ blockIndexList n F h) : i.q ≠ 0 := by
  have hq := ((mem_blockIndexList n F h i).mp hi).2.1
  rw [qValues, Finset.mem_filter] at hq
  exact hq.2.1
theorem blockIndexList_A {n : ℤ} {F : OrthogonalFrame p} {h : ℤ}
    {i : GeneratorIndex} (hi : i ∈ blockIndexList n F h) : i.A = h :=
  ((mem_blockIndexList n F h i).mp hi).1
variable {s : BResidual n}
theorem dValue_ne_zero {F : OrthogonalFrame (tau (residualSourceLift s))}
    {i : GeneratorIndex} (hgcd : tripleGcd (dValue F i) = 1) :
    dValue F i ≠ ⟨0, 0, 0⟩ := by
  intro hzero
  rw [hzero] at hgcd
  simp [tripleGcd] at hgcd
theorem plusVector_eq_vsmul (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) (t : AResidual n)
    (ht : residualTargetLift t = targetValue s F i) :
    plusVector s t = vsmul (2 * i.q) (dValue F i) := by
  rw [plusVector, ht]
  unfold targetValue reconstructedTarget
  apply Triple.ext <;> simp [vadd, vsmul, negTriple]
theorem retained_iff_passesFilters
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} (hq : i.q ≠ 0) :
    Retained s F i ↔ PassesFilters s F i := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨t, ht⟩ := (isResidualTargetLift_iff n (targetValue s F i)).mp h5
    have hd0 : dValue F i ≠ ⟨0, 0, 0⟩ := dValue_ne_zero h2
    have hkeyd : primitiveKey (dValue F i) = directionKey (dValue F i) :=
      primitiveKey_eq_directionKey h2 h3
    have hplus : plusVector s t = vsmul (2 * i.q) (dValue F i) :=
      plusVector_eq_vsmul F i t ht
    have hplusKey : directionKey (plusVector s t) = directionKey (dValue F i) := by
      rw [hplus]
      exact directionKey_vsmul (by omega) hd0
    have hminus : minusVector s t = vsub (residualSourceLift s) (targetValue s F i) := by
      rw [minusVector, ht]
    have hminusKey : directionKeyExec
        (vsub (residualSourceLift s) (targetValue s F i)) =
        directionKey (minusVector s t) := by
      rw [← hminus]
      exact directionKeyExec_eq (minusVector_ne_zero s t)
    refine ⟨h1, by rw [tripleContent_eq_tripleGcd]; exact h2, h3, h4, t, ht, ?_⟩
    have hlt : directionKey (plusVector s t) < directionKey (minusVector s t) := by
      rw [hplusKey, ← hkeyd, ← hminusKey]
      exact h6
    rw [representativeEdgeKey, min_eq_left hlt.le, hplusKey]
  · rintro ⟨h1, h2, h3, h4, t, ht, hkey⟩
    have h2' : tripleGcd (dValue F i) = 1 := by
      rw [← tripleContent_eq_tripleGcd]; exact h2
    have hd0 : dValue F i ≠ ⟨0, 0, 0⟩ := dValue_ne_zero h2'
    have hkeyd : primitiveKey (dValue F i) = directionKey (dValue F i) :=
      primitiveKey_eq_directionKey h2' h3
    have hplus : plusVector s t = vsmul (2 * i.q) (dValue F i) :=
      plusVector_eq_vsmul F i t ht
    have hplusKey : directionKey (plusVector s t) = directionKey (dValue F i) := by
      rw [hplus]
      exact directionKey_vsmul (by omega) hd0
    have hminus : minusVector s t = vsub (residualSourceLift s) (targetValue s F i) := by
      rw [minusVector, ht]
    have hminusKey : directionKeyExec
        (vsub (residualSourceLift s) (targetValue s F i)) =
        directionKey (minusVector s t) := by
      rw [← hminus]
      exact directionKeyExec_eq (minusVector_ne_zero s t)
    refine ⟨h1, h2', h3, h4, (isResidualTargetLift_iff n _).mpr ⟨t, ht⟩, ?_⟩
    rw [hkeyd, hminusKey]
    rcases lt_trichotomy (directionKey (plusVector s t))
      (directionKey (minusVector s t)) with hlt | heq | hgt
    · rwa [← hplusKey]
    · exact absurd heq (plus_minus_keys_ne s t)
    · exfalso
      rw [representativeEdgeKey, min_eq_right hgt.le] at hkey
      rw [← hplusKey] at hkey
      exact plus_minus_keys_ne s t hkey
def blockRetained (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) : List GeneratorIndex :=
  (blockIndexList n F h).filter fun i => decide (Retained s F i)
theorem mem_blockRetained (F : OrthogonalFrame (tau (residualSourceLift s)))
    (h : ℤ) (i : GeneratorIndex) :
    i ∈ blockRetained s F h ↔ i ∈ blockIndexList n F h ∧ Retained s F i := by
  simp [blockRetained]
theorem blockRetained_nodup (F : OrthogonalFrame (tau (residualSourceLift s)))
    (h : ℤ) : (blockRetained s F h).Nodup :=
  List.Nodup.filter _ (blockIndexList_nodup n F h)
theorem filterMap_emit_eq (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) :
    (blockIndexList n F h).filterMap (emit s F) =
      (blockRetained s F h).map (recordOf s F) := by
  unfold blockRetained
  induction blockIndexList n F h with
  | nil => simp
  | cons a l ih => by_cases ha : Retained s F a <;> simp [emit, ha, ih]
theorem blockRecords_perm (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) :
    (blockRecords s F h).Perm ((blockRetained s F h).map (recordOf s F)) := by
  rw [blockRecords, ← filterMap_emit_eq]
  exact List.mergeSort_perm _ _
theorem recordLe_trans (a b c : IncidentRecord) :
    recordLe a b = true → recordLe b c = true → recordLe a c = true := by
  simp only [recordLe, keyLeExec_iff]
  exact le_trans
theorem recordLe_total (a b : IncidentRecord) :
    (recordLe a b || recordLe b a) = true := by
  simp only [recordLe, Bool.or_eq_true, keyLeExec_iff]
  exact le_total _ _
theorem blockRecords_pairwise_le (F : OrthogonalFrame (tau (residualSourceLift s)))
    (h : ℤ) : (blockRecords s F h).Pairwise fun a b => a.key ≤ b.key := by
  have := List.pairwise_mergeSort recordLe_trans recordLe_total
    ((blockIndexList n F h).filterMap (emit s F))
  exact this.imp (by simp only [recordLe, keyLeExec_iff]; exact id)
theorem mem_validIndices_of_block (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hh1 : 1 ≤ h) (hh2 : h ≤ hMax n) {i : GeneratorIndex}
    (hi : i ∈ blockIndexList n F h) (hr : Retained s F i) : i ∈ validIndices s F := by
  have hA : i.A = h := blockIndexList_A hi
  rw [mem_validIndices_iff]
  refine ⟨?_, (retained_iff_passesFilters F (blockIndexList_q_ne_zero hi)).mp hr⟩
  rw [mem_rawIndices_iff]
  exact ⟨⟨by omega, by omega⟩, by rw [hA]; exact hi⟩
theorem block_of_mem_validIndices (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} (hi : i ∈ validIndices s F) :
    1 ≤ i.A ∧ i.A ≤ hMax n ∧ i ∈ blockIndexList n F i.A ∧ Retained s F i := by
  rw [mem_validIndices_iff] at hi
  obtain ⟨hraw, hpf⟩ := hi
  rw [mem_rawIndices_iff] at hraw
  exact ⟨hraw.1.1, hraw.1.2, hraw.2,
    (retained_iff_passesFilters F (blockIndexList_q_ne_zero hraw.2)).mpr hpf⟩
theorem recordOf_key_of_valid (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} (hi : i ∈ validIndices s F) :
    (recordOf s F i).key = directionKey (dValue F i) := by
  have hpf := ((mem_validIndices_iff s F i).mp hi).2
  exact primitiveKey_eq_directionKey
    (by rw [← tripleContent_eq_tripleGcd]; exact hpf.2.1) hpf.2.2.1
theorem recordOf_key_fst (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} (hi : i ∈ validIndices s F) :
    (recordOf s F i).key.form = i.A := by
  have hpf := ((mem_validIndices_iff s F i).mp hi).2
  have hraw := ((mem_validIndices_iff s F i).mp hi).1
  have hfix := primitiveDirection_eq_self_of_content_one_of_oriented hpf.2.1 hpf.2.2.1
  rw [recordOf_key_of_valid F hi]
  simp only [directionKey, hfix]
  exact qForm_dValue_of_rawIndex F hraw hpf.1
theorem recordOf_key_lt_of_A_lt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i j : GeneratorIndex} (hi : i ∈ validIndices s F) (hj : j ∈ validIndices s F)
    (hij : i.A < j.A) : (recordOf s F i).key < (recordOf s F j).key := by
  rw [DirectionKey.lt_iff]
  exact Or.inl (by rw [recordOf_key_fst F hi, recordOf_key_fst F hj]; exact hij)
theorem recordOf_injOn_valid (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i j : GeneratorIndex} (hi : i ∈ validIndices s F) (hj : j ∈ validIndices s F)
    (h : (recordOf s F i).key = (recordOf s F j).key) : i = j := by
  have hkey : directionKey (dValue F i) = directionKey (dValue F j) := by
    rw [← recordOf_key_of_valid F hi, ← recordOf_key_of_valid F hj]; exact h
  have := validIndex_eq_of_directionKey_eq s F ⟨i, hi⟩ ⟨j, hj⟩ hkey
  exact congrArg Subtype.val this
theorem mem_blockRecords (F : OrthogonalFrame (tau (residualSourceLift s)))
    (h : ℤ) (r : IncidentRecord) :
    r ∈ blockRecords s F h ↔
      ∃ i, (i ∈ blockIndexList n F h ∧ Retained s F i) ∧ r = recordOf s F i := by
  rw [(blockRecords_perm F h).mem_iff, List.mem_map]
  simp only [mem_blockRetained]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
theorem blockRecords_pairwise_key_ne (F : OrthogonalFrame (tau (residualSourceLift s)))
    {a : ℤ} (h1 : 1 ≤ a) (h2 : a ≤ hMax n) :
    (blockRecords s F a).Pairwise fun x y => x.key ≠ y.key := by
  refine ((blockRecords_perm F a).pairwise_iff (fun {x y} hxy => Ne.symm hxy)).mpr ?_
  rw [List.pairwise_map]
  refine (blockRetained_nodup F a).imp_of_mem ?_
  intro i j hi hj hne hkey
  rw [mem_blockRetained] at hi hj
  exact hne (recordOf_injOn_valid F (mem_validIndices_of_block F h1 h2 hi.1 hi.2)
    (mem_validIndices_of_block F h1 h2 hj.1 hj.2) hkey)
theorem blockRecords_pairwise_key_lt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {a : ℤ} (h1 : 1 ≤ a) (h2 : a ≤ hMax n) :
    (blockRecords s F a).Pairwise fun x y => x.key < y.key :=
  ((blockRecords_pairwise_le F a).and (blockRecords_pairwise_key_ne F h1 h2)).imp
    fun hx => lt_of_le_of_ne hx.1 hx.2
def blockRange (n h : ℤ) : List ℤ :=
  (List.range (hMax n + 1 - h).toNat).map fun k : ℕ => h + (k : ℤ)
theorem mem_blockRange (n h x : ℤ) : x ∈ blockRange n h ↔ h ≤ x ∧ x ≤ hMax n := by
  simp only [blockRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · rintro ⟨ha, hb⟩
    exact ⟨(x - h).toNat, by omega, by omega⟩
theorem blockRange_nil {n h : ℤ} (hgt : ¬ h ≤ hMax n) : blockRange n h = [] := by
  simp only [blockRange]
  rw [show (hMax n + 1 - h).toNat = 0 by omega]
  simp
theorem blockRange_cons {n h : ℤ} (hle : h ≤ hMax n) :
    blockRange n h = h :: blockRange n (h + 1) := by
  simp only [blockRange]
  rw [show (hMax n + 1 - h).toNat = (hMax n + 1 - (h + 1)).toNat + 1 by omega,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.cast_zero, add_zero]
  congr 1
  refine List.map_congr_left ?_
  intro k _
  simp only [Function.comp_apply, Nat.cast_succ]
  ring
theorem blockRange_pairwise_lt (n h : ℤ) : (blockRange n h).Pairwise (· < ·) := by
  rw [blockRange, List.pairwise_map]
  exact List.pairwise_lt_range.imp (by intro a b hab; omega)
theorem blocksFrom_eq_flatMap (F : OrthogonalFrame (tau (residualSourceLift s)))
    (h : ℤ) : blocksFrom s F h = (blockRange n h).flatMap (blockRecords s F) := by
  suffices H : ∀ k : ℕ, ∀ h : ℤ, (hMax n + 1 - h).toNat = k →
      blocksFrom s F h = (blockRange n h).flatMap (blockRecords s F) from H _ h rfl
  intro k
  induction k with
  | zero =>
      intro h hk
      have hgt : ¬ h ≤ hMax n := by omega
      rw [blocksFrom, if_neg hgt, blockRange_nil hgt]
      simp
  | succ k ih =>
      intro h hk
      have hle : h ≤ hMax n := by omega
      rw [blocksFrom, if_pos hle, blockRange_cons hle, List.flatMap_cons,
        ih (h + 1) (by omega)]
theorem mem_blocksFrom (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hh : 1 ≤ h) (r : IncidentRecord) :
    r ∈ blocksFrom s F h ↔
      ∃ i, i ∈ validIndices s F ∧ h ≤ i.A ∧ r = recordOf s F i := by
  rw [blocksFrom_eq_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, hr⟩
    rw [mem_blockRange] at ha
    rw [mem_blockRecords] at hr
    obtain ⟨i, ⟨hi, hret⟩, rfl⟩ := hr
    have hA : i.A = a := blockIndexList_A hi
    exact ⟨i, mem_validIndices_of_block F (by omega) ha.2 hi hret, by omega, rfl⟩
  · rintro ⟨i, hi, hiA, rfl⟩
    obtain ⟨hA1, hA2, hmem, hret⟩ := block_of_mem_validIndices F hi
    exact ⟨i.A, (mem_blockRange n h i.A).mpr ⟨hiA, hA2⟩,
      (mem_blockRecords F i.A _).mpr ⟨i, ⟨hmem, hret⟩, rfl⟩⟩
theorem mem_fullTrace (F : OrthogonalFrame (tau (residualSourceLift s)))
    (r : IncidentRecord) :
    r ∈ fullTrace s F ↔ ∃ i, i ∈ validIndices s F ∧ r = recordOf s F i := by
  rw [fullTrace, mem_blocksFrom F le_rfl]
  constructor
  · rintro ⟨i, hi, -, hr⟩; exact ⟨i, hi, hr⟩
  · rintro ⟨i, hi, hr⟩
    exact ⟨i, hi, (block_of_mem_validIndices F hi).1, hr⟩
theorem blocksFrom_pairwise_key_lt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hh : 1 ≤ h) :
    (blocksFrom s F h).Pairwise fun x y => x.key < y.key := by
  rw [blocksFrom_eq_flatMap, List.pairwise_flatMap]
  constructor
  · intro a ha
    rw [mem_blockRange] at ha
    exact blockRecords_pairwise_key_lt F (by omega) ha.2
  · refine (blockRange_pairwise_lt n h).imp_of_mem ?_
    intro a₁ a₂ ha₁ ha₂ hlt x hx y hy
    rw [mem_blockRange] at ha₁ ha₂
    rw [mem_blockRecords] at hx hy
    obtain ⟨i, ⟨hi, hri⟩, rfl⟩ := hx
    obtain ⟨j, ⟨hj, hrj⟩, rfl⟩ := hy
    have hiA : i.A = a₁ := blockIndexList_A hi
    have hjA : j.A = a₂ := blockIndexList_A hj
    exact recordOf_key_lt_of_A_lt F
      (mem_validIndices_of_block F (by omega) ha₁.2 hi hri)
      (mem_validIndices_of_block F (by omega) ha₂.2 hj hrj) (by omega)
theorem fullTrace_pairwise_key_lt (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (fullTrace s F).Pairwise fun x y => x.key < y.key :=
  blocksFrom_pairwise_key_lt F le_rfl
theorem fullTrace_nodup (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (fullTrace s F).Nodup :=
  (fullTrace_pairwise_key_lt F).imp fun hxy hEq => absurd (congrArg IncidentRecord.key hEq)
    (ne_of_lt hxy)
noncomputable def orbitTargetLift {n : ℤ} (hnpos : 0 < n)
    (o : (aResidualInvolution n hnpos).Orbit) : Triple :=
  residualTargetLift (canonicalAResidualRepresentative hnpos o)
theorem recordOf_target_eq (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    (recordOf s F i.1).target = orbitTargetLift hnpos (targetOrbitOfValid hnpos s F i) := by
  show canonicalTargetLift (targetValue s F i.1) = _
  rw [← targetOfValid_lift s F i, canonicalTargetLift_eq hnpos]
  rfl
theorem orderedIndexList_map_pairwise_key_lt
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ((orderedIndexList s F).map fun i => recordOf s F i.1).Pairwise
      fun x y => x.key < y.key := by
  rw [List.pairwise_map]
  refine (((orderedIndexList_pairwise s F).and (orderedIndexList_nodup s F)).imp ?_)
  rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨hle, hne⟩
  rw [recordOf_key_of_valid F hi, recordOf_key_of_valid F hj]
  refine lt_of_le_of_ne hle ?_
  intro hEq
  exact hne (Subtype.ext (congrArg Subtype.val
    (validIndex_eq_of_directionKey_eq s F ⟨i, hi⟩ ⟨j, hj⟩ hEq)))
theorem fullTrace_eq_map_orderedIndexList
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    fullTrace s F = (orderedIndexList s F).map fun i => recordOf s F i.1 := by
  refine List.Perm.eq_of_pairwise (le := fun x y => x.key < y.key)
    (fun a b _ _ h₁ h₂ => absurd h₂ (asymm h₁))
    (fullTrace_pairwise_key_lt F) (orderedIndexList_map_pairwise_key_lt F) ?_
  refine (List.perm_ext_iff_of_nodup (fullTrace_nodup F) ?_).mpr ?_
  · exact (orderedIndexList_map_pairwise_key_lt F).imp
      fun hxy hEq => absurd (congrArg IncidentRecord.key hEq) (ne_of_lt hxy)
  · intro r
    rw [mem_fullTrace, List.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, mem_orderedIndexList s F ⟨i, hi⟩, rfl⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
theorem fullTrace_target_eq_incidentStream (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (fullTrace s F).map IncidentRecord.target =
      (incidentStream hnpos s F).map (orbitTargetLift hnpos) := by
  rw [fullTrace_eq_map_orderedIndexList, incidentStream, List.map_map, List.map_map]
  refine List.map_congr_left ?_
  intro i _
  exact recordOf_target_eq hnpos F i
theorem fullTrace_length_eq (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (fullTrace s F).length = (incidentStream hnpos s F).length := by
  simpa using congrArg List.length (fullTrace_target_eq_incidentStream hnpos F)
end BlockGen
end TunnellMap


