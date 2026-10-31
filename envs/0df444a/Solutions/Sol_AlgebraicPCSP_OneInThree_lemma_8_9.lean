-- Prove2me | solution 1 for AlgebraicPCSP.OneInThree.lemma_8_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:47:46.31523+00:00
-- url     : https://prove2.me/submissions/baf2fa95-008c-4479-8146-51484e2256c0

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices
import Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_7
import Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_8

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.OneInThree

namespace Lemma89Proof

lemma isCyclic_iterate {D : Type} {n : ℕ} (t : (Fin n → D) → D) (hcyc : IsCyclic t)
    (a : Fin n → D) (m : ℕ) :
    t a = t (a ∘ (finRotate n)^[m]) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    rw [hcyc a, ih (a ∘ finRotate n), Function.iterate_succ', Function.comp_assoc]

lemma val_finRotate {N : ℕ} (i : Fin N) :
    (finRotate N i).val = (i.val + 1) % N := by
  rcases N with _ | n
  · exact i.elim0
  · rcases i with ⟨k, hk⟩
    by_cases h : k < n
    · rw [finRotate_of_lt h]
      exact (Nat.mod_eq_of_lt (Nat.succ_lt_succ h)).symm
    · have hk_eq : k = n := by omega
      subst hk_eq
      rw [finRotate_last']
      simp

lemma val_finRotate_iterate {N : ℕ} (m : ℕ) (i : Fin N) :
    ((finRotate N)^[m] i).val = (i.val + m) % N := by
  induction m generalizing i with
  | zero =>
    simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, val_finRotate, Nat.mod_add_mod, Nat.add_right_comm,
      Nat.add_assoc]

lemma mod_eq_ite {a N : ℕ} (h : a < 2 * N) :
    a % N = if a < N then a else a - N := by
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

lemma val_segTuple {p k : ℕ} (idx : Fin (p * p)) :
    (segTuple p k idx).val = if idx.val < k then 1 else 0 := by
  unfold segTuple
  split_ifs <;> rfl

lemma tOp_toMatrix_comp {D : Type} {p : ℕ} (f : Fin 2 → D) (s : (Fin p → D) → D)
    (x : Fin (p * p) → Fin 2) :
    tOp s (fun r c => f (toMatrix x r c)) = tFlat s (f ∘ x) := rfl

lemma seg_triple_not_all_equiv {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) {i j k : ℕ} (hsum : i + j + k = p * p) :
    ¬ (GEquiv f g s (seg p i) (seg p j) ∧ GEquiv f g s (seg p j) (seg p k)) := by
  let N := p * p
  let x : Fin N → Fin 2 := segTuple p i
  let y : Fin N → Fin 2 := segTuple p j ∘ (finRotate N)^[j + k]
  let z : Fin N → Fin 2 := segTuple p k ∘ (finRotate N)^[k]
  have htcyc : IsCyclic (tFlat s) := lemma_8_8 s hcyc
  have hy_eq : tOp s (fun r c => f (toMatrix y r c)) = tOp s (fun r c => f (seg p j r c)) := by
    rw [tOp_toMatrix_comp, seg, tOp_toMatrix_comp]
    exact (isCyclic_iterate (tFlat s) htcyc (f ∘ segTuple p j) (j + k)).symm
  have hz_eq : tOp s (fun r c => f (toMatrix z r c)) = tOp s (fun r c => f (seg p k r c)) := by
    rw [tOp_toMatrix_comp, seg, tOp_toMatrix_comp]
    exact (isCyclic_iterate (tFlat s) htcyc (f ∘ segTuple p k) k).symm
  have hcover : IsCover (toMatrix x) (toMatrix y) (toMatrix z) := by
    intro r c
    let idx : Fin N := finProdFinEquiv (r, c)
    have hidx : idx.val < N := idx.isLt
    change (x idx).val + (y idx).val + (z idx).val = 1
    dsimp [x, y, z]
    rw [val_segTuple, val_segTuple, val_segTuple, val_finRotate_iterate, val_finRotate_iterate]
    rw [mod_eq_ite (by omega), mod_eq_ite (by omega)]
    split_ifs <;> omega
  have hnot := lemma_8_7 R f g hf hg s hs (toMatrix x) (toMatrix y) (toMatrix z) hcover
  rintro ⟨hij, hjk⟩
  apply hnot
  refine ⟨?_, ?_⟩
  · unfold GEquiv at hij ⊢
    rw [hy_eq]
    exact hij
  · unfold GEquiv at hjk ⊢
    rw [hy_eq, hz_eq]
    exact hjk

lemma fin2_dichotomy {a b c : Fin 2} (hne : a ≠ b) : c = a ∨ c = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

end Lemma89Proof

theorem solution {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) (q : ℕ) (hq : p * p = 3 * q + 1) :
    (∀ i, i ≤ q → GEquiv f g s (seg p i) (seg p 0)) ∧
    (∀ i, q + 1 ≤ i → i ≤ 2 * q + 1 → GEquiv f g s (seg p i) (seg p (q + 1))) ∧
    ¬ GEquiv f g s (seg p q) (seg p (q + 1)) := by
  have _ := hp
  have _ := hp3
  have hneq : ¬ GEquiv f g s (seg p q) (seg p (q + 1)) := by
    intro h
    exact Lemma89Proof.seg_triple_not_all_equiv R f g hf hg s hs hcyc (i := q) (j := q) (k := q + 1)
      (by omega) ⟨rfl, h⟩
  have hdich (m : ℕ) : GEquiv f g s (seg p m) (seg p q) ∨ GEquiv f g s (seg p m) (seg p (q + 1)) :=
    Lemma89Proof.fin2_dichotomy hneq
  have hind : ∀ d : ℕ, d ≤ q →
      GEquiv f g s (seg p (q - d)) (seg p q) ∧
      GEquiv f g s (seg p (q + 1 + d)) (seg p (q + 1)) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp [GEquiv]
    | succ d ih =>
      intro hd
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have h1 : GEquiv f g s (seg p (q - (d + 1))) (seg p q) := by
        rcases hdich (q - (d + 1)) with h | h
        · exact h
        · exfalso
          exact Lemma89Proof.seg_triple_not_all_equiv R f g hf hg s hs hcyc
            (i := q - (d + 1)) (j := q + 1) (k := q + 1 + d) (by omega) ⟨h, ih2.symm⟩
      have h2 : GEquiv f g s (seg p (q + 1 + (d + 1))) (seg p (q + 1)) := by
        rcases hdich (q + 1 + (d + 1)) with h | h
        · exfalso
          exact Lemma89Proof.seg_triple_not_all_equiv R f g hf hg s hs hcyc
            (i := q + 1 + (d + 1)) (j := q) (k := q - (d + 1)) (by omega) ⟨h, h1.symm⟩
        · exact h
      exact ⟨h1, h2⟩
  have h0_eq_q : GEquiv f g s (seg p 0) (seg p q) := by
    have := (hind q le_rfl).1
    rwa [Nat.sub_self] at this
  refine ⟨?_, ?_, hneq⟩
  · intro i hi
    have hi_q : GEquiv f g s (seg p i) (seg p q) := by
      have := (hind (q - i) (by omega)).1
      rwa [Nat.sub_sub_self hi] at this
    exact hi_q.trans h0_eq_q.symm
  · intro i hi1 hi2
    have := (hind (i - (q + 1)) (by omega)).2
    rwa [Nat.add_sub_of_le hi1] at this
