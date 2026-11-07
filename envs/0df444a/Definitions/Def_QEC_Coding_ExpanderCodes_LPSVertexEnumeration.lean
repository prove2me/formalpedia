-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
-- name    : QEC_Coding_ExpanderCodes_LPSVertexEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:51:02.134349+00:00
-- url     : https://prove2.me/theorems/728b79ee-9fbd-46dd-bfdc-f85838258018
-- title:
--   LPSVertex Enumeration
-- statement:
--   Definitions and structural lemmas for LPSVertex Enumeration, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_747ca7d85c_18 : Fact (Even (Fintype.card (Fin 2))) := ⟨by simp⟩
theorem sl_two_mem_center_iff (q : ℕ) [Fact q.Prime]
    (A : SL(2, ZMod q)) :
    A ∈ Subgroup.center SL(2, ZMod q) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r ^ 2 = 1 := by simpa using hr
    rcases sq_eq_one_iff.mp hr' with h | h
    · left
      apply Subtype.ext
      rw [← hA, h]
      simp
    · right
      apply Subtype.ext
      rw [← hA, h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · rintro (h | h)
    · subst A
      exact ⟨1, by simp, by simp⟩
    · subst A
      refine ⟨-1, by simp, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp
theorem lpsPSLMk_eq_iff (q : ℕ) [Fact q.Prime] (A B : SL(2, ZMod q)) :
    (QuotientGroup.mk A : PSL(2, ZMod q)) = QuotientGroup.mk B ↔ A = B ∨ -A = B := by
  change QuotientGroup.mk' (Subgroup.center SL(2, ZMod q)) A =
    QuotientGroup.mk' (Subgroup.center SL(2, ZMod q)) B ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, h⟩
    rcases (sl_two_mem_center_iff q z).mp hz with hz | hz
    · left
      simpa [hz] using h
    · right
      simpa [hz] using h
  · rintro (h | h)
    · exact ⟨1, (sl_two_mem_center_iff q 1).mpr (Or.inl rfl), by simpa using h⟩
    · exact ⟨-1, (sl_two_mem_center_iff q (-1)).mpr (Or.inr rfl), by simpa using h⟩
def lpsPSLDecidableEq (q : ℕ) [Fact q.Prime] : DecidableEq PSL(2, ZMod q) :=
  fun x y => Quotient.recOnSubsingleton₂ x y fun A B =>
    decidable_of_iff (A = B ∨ -A = B) (lpsPSLMk_eq_iff q A B).symm
def lpsEntryMatrix (q : ℕ) (a b c d : Fin q) : Matrix (Fin 2) (Fin 2) (ZMod q) :=
  !![(a.val : ZMod q), (b.val : ZMod q); (c.val : ZMod q), (d.val : ZMod q)]
def lpsSLMatrixCandidate (q : ℕ) (a b c d : Fin q) : Option SL(2, ZMod q) :=
  if h : (lpsEntryMatrix q a b c d).det = 1 then
    some ⟨lpsEntryMatrix q a b c d, h⟩ else none
def lpsSLList (q : ℕ) : List SL(2, ZMod q) :=
  (List.finRange q).flatMap fun a =>
    (List.finRange q).flatMap fun b =>
      (List.finRange q).flatMap fun c =>
        (List.finRange q).filterMap (fun d => lpsSLMatrixCandidate q a b c d)
theorem mem_lpsSLList (q : ℕ) [Fact q.Prime] (A : SL(2, ZMod q)) : A ∈ lpsSLList q := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  let a : Fin q := ⟨(A.val 0 0).val, ZMod.val_lt _⟩
  let b : Fin q := ⟨(A.val 0 1).val, ZMod.val_lt _⟩
  let c : Fin q := ⟨(A.val 1 0).val, ZMod.val_lt _⟩
  let d : Fin q := ⟨(A.val 1 1).val, ZMod.val_lt _⟩
  have hM : lpsEntryMatrix q a b c d = A.val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsEntryMatrix, a, b, c, d]
  have hdet : (lpsEntryMatrix q a b c d).det = 1 := by rw [hM]; exact A.property
  simp only [lpsSLList, List.mem_flatMap]
  refine ⟨a, List.mem_finRange _, b, List.mem_finRange _, c, List.mem_finRange _, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨d, List.mem_finRange _, ?_⟩
  simp only [lpsSLMatrixCandidate, dif_pos hdet]
  congr 1
  exact Subtype.ext hM
def lpsPSLList (q : ℕ) [Fact q.Prime] : List PSL(2, ZMod q) :=
  letI := lpsPSLDecidableEq q
  ((lpsSLList q).map (fun A => (QuotientGroup.mk A : PSL(2, ZMod q)))).dedup
theorem lpsPSLList_nodup (q : ℕ) [Fact q.Prime] : (lpsPSLList q).Nodup := by
  let := lpsPSLDecidableEq q
  exact List.nodup_dedup _
theorem mem_lpsPSLList (q : ℕ) [Fact q.Prime] (x : PSL(2, ZMod q)) : x ∈ lpsPSLList q := by
  let := lpsPSLDecidableEq q
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  rw [lpsPSLList, List.mem_dedup]
  exact List.mem_map.mpr ⟨A, mem_lpsSLList q A, rfl⟩
def lpsPSLEnumerationEquiv (q : ℕ) [Fact q.Prime] :
    Fin (lpsPSLList q).length ≃ PSL(2, ZMod q) :=
  letI := lpsPSLDecidableEq q
  List.Nodup.getEquivOfForallMemList (lpsPSLList q) (lpsPSLList_nodup q) (mem_lpsPSLList q)
def lpsPSLIndexMul (q : ℕ) [Fact q.Prime]
    (i j : Fin (lpsPSLList q).length) : Fin (lpsPSLList q).length :=
  (lpsPSLEnumerationEquiv q).symm
    ((lpsPSLEnumerationEquiv q) i * (lpsPSLEnumerationEquiv q) j)
def lpsPSLIndexInv (q : ℕ) [Fact q.Prime]
    (i : Fin (lpsPSLList q).length) : Fin (lpsPSLList q).length :=
  (lpsPSLEnumerationEquiv q).symm ((lpsPSLEnumerationEquiv q) i)⁻¹
def lpsPSLIndexOne (q : ℕ) [Fact q.Prime] : Fin (lpsPSLList q).length :=
  (lpsPSLEnumerationEquiv q).symm 1
def lpsQuaternionVertexIndex {p : ℕ} (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : Fin (lpsPSLList a.q).length :=
  (lpsPSLEnumerationEquiv a.q).symm (lpsEffectiveQuaternionPSL a t ht)
end QEC.Coding.TannerLiftedProduct


