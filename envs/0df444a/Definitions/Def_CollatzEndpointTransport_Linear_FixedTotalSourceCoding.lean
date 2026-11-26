-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
-- name    : CollatzEndpointTransport_Linear_FixedTotalSourceCoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:50:25.038106+00:00
-- url     : https://prove2.me/theorems/69e1f7b8-bc0b-5576-84f7-b0efc5593e87
-- title:
--   Fixed Total Source Coding
-- statement:
--   Definitions and structural lemmas for Fixed Total Source Coding, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Mathlib.Data.Fintype.BigOperators
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_eq_exponent_of_pow_two_mul_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_mod_two
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_injective_on_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_prefix_encodeComposition
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_replicate_false_append
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero


set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
abbrev SourceCode (M : ℕ) :=
  Unit ⊕ Σ u : Fin M, Composition (M - (u : ℕ))
noncomputable instance sourceCodeFintype (M : ℕ) :
    Fintype (SourceCode M) := by
  unfold SourceCode
  infer_instance
noncomputable instance sourceCodeDecidableEq (M : ℕ) :
    DecidableEq (SourceCode M) := Classical.decEq _
def sourceCodeList {M : ℕ} : SourceCode M → List Bool
  | Sum.inl _ => List.replicate M false
  | Sum.inr ⟨u, c⟩ =>
      List.replicate (u : ℕ) false ++ encodeBlocks c.blocks
theorem sourceCodeList_length
    {M : ℕ} (x : SourceCode M) :
    (sourceCodeList x).length = M := by
  cases x with
  | inl e =>
      simp [sourceCodeList]
  | inr p =>
      rcases p with ⟨u, c⟩
      have hlen :=
        encodeBlocks_length
          (ks := c.blocks) (fun k hk => c.blocks_pos hk)
      have hu : (u : ℕ) ≤ M := Nat.le_of_lt u.isLt
      simp only [sourceCodeList, List.length_append,
        List.length_replicate, hlen, c.blocks_sum]
      omega
def sourceCodeWord {M : ℕ} (x : SourceCode M) : Fin M → Bool :=
  fun i =>
    (sourceCodeList x).get
      ⟨(i : ℕ), by simpa [sourceCodeList_length x] using i.isLt⟩
theorem ofFn_sourceCodeWord
    {M : ℕ} (x : SourceCode M) :
    List.ofFn (sourceCodeWord x) = sourceCodeList x := by
  apply List.ext_getElem
  · simp [sourceCodeList_length]
  · intro i hi₁ hi₂
    simp [sourceCodeWord]
def listOddCount : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + listOddCount bs
@[simp]
theorem listOddCount_nil :
    listOddCount [] = 0 := rfl
@[simp]
theorem listOddCount_cons (b : Bool) (bs : List Bool) :
    listOddCount (b :: bs) =
      (if b then 1 else 0) + listOddCount bs := rfl
theorem listOddCount_append (xs ys : List Bool) :
    listOddCount (xs ++ ys) =
      listOddCount xs + listOddCount ys := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
      simp [ih, add_assoc]
@[simp]
theorem listOddCount_replicate_false (r : ℕ) :
    listOddCount (List.replicate r false) = 0 := by
  induction r with
  | zero => simp
  | succ r ih => simp [List.replicate_succ, ih]
theorem listOddCount_encodePart
    {k : ℕ} (hk : 0 < k) :
    listOddCount (encodePart k) = 1 := by
  simp [encodePart]
theorem listOddCount_encodeBlocks
    (ks : List ℕ) (hpos : ∀ k ∈ ks, 0 < k) :
    listOddCount (encodeBlocks ks) = ks.length := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have htail : ∀ l ∈ ks, 0 < l :=
        fun l hl => hpos l (by simp [hl])
      simp [encodeBlocks, listOddCount_append,
        listOddCount_encodePart hk, ih htail, Nat.add_comm]
theorem sourceCodeList_oddCount
    {M : ℕ} (u : Fin M) (c : Composition (M - (u : ℕ))) :
    listOddCount (sourceCodeList (Sum.inr ⟨u, c⟩ : SourceCode M)) =
      c.length := by
  simp [sourceCodeList, listOddCount_append,
    listOddCount_encodeBlocks c.blocks
      (fun k hk => c.blocks_pos hk)]
def sourceCodeCorrection {M : ℕ} : SourceCode M → ℕ
  | Sum.inl _ => 0
  | Sum.inr ⟨u, c⟩ => 2 ^ (u : ℕ) * syracuseNumerator c
def sourceCodeOddCount {M : ℕ} : SourceCode M → ℕ
  | Sum.inl _ => 0
  | Sum.inr ⟨_, c⟩ => c.length
theorem wordCorrection_sourceCodeList
    {M : ℕ} (x : SourceCode M) :
    wordCorrectionFrom 0 0 (sourceCodeList x) =
      sourceCodeCorrection x := by
  cases x with
  | inl e =>
      simpa [sourceCodeList, sourceCodeCorrection] using
        (wordCorrectionFrom_replicate_false_append 0 0 M [])
  | inr p =>
      rcases p with ⟨u, c⟩
      exact wordCorrectionFrom_prefix_encodeComposition (u : ℕ) c
theorem composition_numerator_pos
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    0 < syracuseNumerator c := by
  have hne := composition_blocks_ne_nil hN c
  obtain ⟨k, ks, hk⟩ := List.exists_cons_of_ne_nil hne
  rw [syracuseNumerator, hk]
  exact syracuseNumeratorList_pos k ks
theorem composition_numerator_mod_two
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    syracuseNumerator c % 2 = 1 := by
  have hne := composition_blocks_ne_nil hN c
  obtain ⟨k, ks, hk⟩ := List.exists_cons_of_ne_nil hne
  have hkpos : 0 < k := c.blocks_pos (hk ▸ by simp)
  rw [syracuseNumerator, hk]
  exact syracuseNumeratorList_mod_two hkpos ks
theorem sourceCodeWord_injective
    (M : ℕ) :
    Function.Injective (sourceCodeWord : SourceCode M → (Fin M → Bool)) := by
  intro x y hword
  have hlist : sourceCodeList x = sourceCodeList y := by
    have h := congrArg List.ofFn hword
    simpa [ofFn_sourceCodeWord] using h
  have hcorr : sourceCodeCorrection x = sourceCodeCorrection y := by
    have h := congrArg (wordCorrectionFrom 0 0) hlist
    simpa [wordCorrection_sourceCodeList] using h
  cases x with
  | inl ex =>
      cases y with
      | inl ey => rfl
      | inr py =>
          rcases py with ⟨v, d⟩
          have hN : 0 < M - (v : ℕ) := by omega
          have hpos := composition_numerator_pos hN d
          simp [sourceCodeCorrection] at hcorr
          exfalso
          have : 0 < 2 ^ (v : ℕ) * syracuseNumerator d := by
            exact mul_pos (pow_pos (by norm_num) _) hpos
          omega
  | inr px =>
      rcases px with ⟨u, c⟩
      cases y with
      | inl ey =>
          have hN : 0 < M - (u : ℕ) := by omega
          have hpos := composition_numerator_pos hN c
          simp [sourceCodeCorrection] at hcorr
          exfalso
          have : 0 < 2 ^ (u : ℕ) * syracuseNumerator c := by
            exact mul_pos (pow_pos (by norm_num) _) hpos
          omega
      | inr py =>
          rcases py with ⟨v, d⟩
          have hNu : 0 < M - (u : ℕ) := by omega
          have hNv : 0 < M - (v : ℕ) := by omega
          have huOdd := composition_numerator_mod_two hNu c
          have hvOdd := composition_numerator_mod_two hNv d
          have huv : (u : ℕ) = (v : ℕ) := by
            apply eq_exponent_of_pow_two_mul_eq huOdd hvOdd
            simpa [sourceCodeCorrection] using hcorr
          have huvFin : u = v := Fin.ext huv
          subst v
          have hlen : c.length = d.length := by
            have h := congrArg listOddCount hlist
            simpa [sourceCodeList_oddCount] using h
          have hnum : syracuseNumerator c = syracuseNumerator d := by
            have hmul :
                2 ^ (u : ℕ) * syracuseNumerator c =
                  2 ^ (u : ℕ) * syracuseNumerator d := by
              simpa [sourceCodeCorrection] using hcorr
            exact Nat.eq_of_mul_eq_mul_left
              (pow_pos (by norm_num : 0 < (2 : ℕ)) (u : ℕ)) hmul
          have hcd : c = d :=
            syracuseNumerator_injective_on_length
              rfl hlen.symm hnum
          subst d
          rfl
theorem one_add_reverse_pow_sum :
    ∀ M : ℕ,
      1 + ∑ u : Fin M, 2 ^ (M - (u : ℕ) - 1) = 2 ^ M := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]
      have htail :
          (∑ i : Fin M, 2 ^ (M + 1 - ((i.succ : Fin (M + 1)) : ℕ) - 1)) =
            ∑ i : Fin M, 2 ^ (M - (i : ℕ) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        simp only [Fin.val_succ]
        omega
      rw [htail]
      rw [pow_succ]
      omega
theorem sourceCode_card (M : ℕ) :
    Fintype.card (SourceCode M) = 2 ^ M := by
  simp only [SourceCode, Fintype.card_sum, Fintype.card_unique,
    Fintype.card_sigma, composition_card]
  exact one_add_reverse_pow_sum M
noncomputable def sourceCodeEquivWord
    (M : ℕ) : SourceCode M ≃ (Fin M → Bool) :=
  Equiv.ofBijective sourceCodeWord <| by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨sourceCodeWord_injective M,
      (sourceCode_card M).trans (by simp)⟩
noncomputable def sourceCodeEquivResidue
    (M : ℕ) : SourceCode M ≃ Fin (2 ^ M) :=
  (sourceCodeEquivWord M).trans (Terras.terrasEquiv M).symm
end
end FixedTotal
end CollatzEndpointTransport


