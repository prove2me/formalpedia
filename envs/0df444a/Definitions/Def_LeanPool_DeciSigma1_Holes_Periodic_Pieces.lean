-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
-- name    : LeanPool_DeciSigma1_Holes_Periodic_Pieces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:40:46.378116+00:00
-- url     : https://prove2.me/theorems/b9eed794-4cae-4f12-8bf9-2d7bad471b49
-- title:
--   Pieces
-- statement:
--   Definitions and structural lemmas for Pieces, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_not_mem_deletedPositions
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_len_ge
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_root_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_sep
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_start_lt_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono
public import Theorems.Thm_DeciSigma1_Words_retainedCount_succ_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Holes_Periodic_Piece_getElem__eq_of_mod_eddd45ef4561
public import Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
omit [DecidableEq α] in
theorem Piece.start_add_len {d : ℕ} (P : Piece W d) : P.start + P.len = P.stop := by
  unfold Piece.len; have := P.long; omega
namespace AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
theorem site_sub {P : Piece W ρ.length} {p : ℕ}
    (hp1 : P.start + Periodic.boundaryMargin N ρ.length ≤ p)
    (hp2 : p < P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length
        * x P) :
    p ∈ deletedPositions W ρ N x P.coordinate := by
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at hp2; omega
  exact mem_deletedPositions.mpr ⟨P, hx.supp P hxP, rfl, hp1, hp2⟩
theorem before_not_mem (P : Piece W ρ.length) (hs : P.start ≠ 0) :
    P.start - 1 ∉ deletedPositions W ρ N x P.coordinate := by
  intro hp
  obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxR
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hd := P.period_pos
  have hne : R ≠ P := by intro h; subst h; omega
  rcases le_total R.start P.start with h | h
  · have := Piece.sep hne hRl h; omega
  · omega
theorem end_not_mem (P : Piece W ρ.length) : P.stop ∉ deletedPositions W ρ N x P.coordinate := by
  intro hp
  obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxR
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hd := P.period_pos
  have hne : R ≠ P := by intro h; subst h; omega
  rcases le_total R.start P.start with h | h
  · have := Piece.sep hne hRl h; have := P.long; omega
  · have := Piece.sep (Ne.symm hne) hRl.symm h; omega
theorem in_piece_not_mem (P : Piece W ρ.length) {p : ℕ} (h1 : P.start ≤ p) (h2 : p < P.stop)
    (hns : p < P.start + Periodic.boundaryMargin N ρ.length ∨ P.start + Periodic.boundaryMargin N
        ρ.length + Periodic.statePeriodModulus N ρ.length * x P ≤ p) :
    p ∉ deletedPositions W ρ N x P.coordinate :=
  hx.not_mem_deletedPositions P rfl h1 h2 hns
theorem not_mem_deletedPositions_of_piece_margin (P : Piece W ρ.length) {p : ℕ} (h1 : P.start ≤ p)
    (h2 : p < P.stop)
    (hns : p < P.start + Periodic.boundaryMargin N ρ.length ∨ x P = 0 ∨
      P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P ≤
          p) :
    p ∉ deletedPositions W ρ N x P.coordinate := by
  apply hx.in_piece_not_mem P h1 h2
  rcases hns with h | h | h
  · exact Or.inl h
  · by_cases hp : p < P.start + Periodic.boundaryMargin N ρ.length
    · exact Or.inl hp
    · exact Or.inr (by rw [h]; omega)
  · exact Or.inr h
theorem retainedCount_head (P : Piece W ρ.length) {o : ℕ}
    (ho : o ≤ Periodic.boundaryMargin N ρ.length ∨ x P = 0)
    (hoL : o ≤ P.len) : keepCut W ρ N x P.coordinate (P.start + o) =
        keepCut W ρ N x P.coordinate P.start + o := by
  apply retainedCount_add_of_not_mem
  intro i hi
  apply hx.not_mem_deletedPositions_of_piece_margin P (by omega) (by unfold Piece.len at hoL; omega)
  exact ho.elim (fun h => Or.inl (by omega)) (fun h => Or.inr (Or.inl h))
theorem retainedCount_tail (P : Piece W ρ.length) {o : ℕ}
    (ho : Periodic.boundaryMargin N ρ.length ≤ o)
    (hoL : o + Periodic.statePeriodModulus N ρ.length * x P ≤ P.len) :
    keepCut W ρ N x P.coordinate (P.start + o + Periodic.statePeriodModulus N ρ.length * x P) =
        keepCut W ρ N x P.coordinate P.start + o := by
  have h1 :=
      hx.retainedCount_head P (o := Periodic.boundaryMargin N ρ.length) (Or.inl le_rfl) (by omega)
  have h2 : keepCut W ρ N x P.coordinate
      (P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x
          P) =
      keepCut W ρ N x P.coordinate (P.start + Periodic.boundaryMargin N ρ.length) :=
    retainedCount_add_of_mem (fun i hi => hx.site_sub (by omega) (by omega))
  have h3 : keepCut W ρ N x P.coordinate
      (P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P +
      (o - Periodic.boundaryMargin N ρ.length)) =
          keepCut W ρ N x P.coordinate (P.start + Periodic.boundaryMargin N ρ.length +
      Periodic.statePeriodModulus N ρ.length * x P) + (o - Periodic.boundaryMargin N ρ.length) :=
    retainedCount_add_of_not_mem (fun i hi => hx.in_piece_not_mem P (by omega)
      (by unfold Piece.len at hoL; omega) (Or.inr (by omega)))
  rw [show P.start + o + Periodic.statePeriodModulus N ρ.length * x P = P.start +
      Periodic.boundaryMargin N ρ.length +
    Periodic.statePeriodModulus N ρ.length * x P +
        (o - Periodic.boundaryMargin N ρ.length) by omega, h3, h2, h1]
  omega
theorem retainedCount_piece_end (P : Piece W ρ.length) :
    keepCut W ρ N x P.coordinate P.stop = keepCut W ρ N x P.coordinate P.start +
        (P.len - Periodic.statePeriodModulus N ρ.length * x P) := by
  by_cases hxP : x P = 0
  · have := hx.retainedCount_head P (o := P.len) (Or.inr hxP) le_rfl
    rw [hxP, Nat.mul_zero, Nat.sub_zero, ← this]; unfold Piece.len; congr 1; have := P.long; omega
  · have hb := hx.site_bound hxP
    have := hx.retainedCount_tail P (o := P.len - Periodic.statePeriodModulus N ρ.length * x P)
      (by unfold Piece.len; omega) (by unfold Piece.len; omega)
    rw [← this]; congr 1; unfold Piece.len; have := P.long; omega
def retainedLength (P : Piece W ρ.length) :
    ℕ := P.len - Periodic.statePeriodModulus N ρ.length * x P
theorem retainedLength_ge (P : Piece W ρ.length) :
    2 * ρ.length ≤ retainedLength (N := N) (x := x) P := by
  unfold retainedLength
  by_cases hxP : x P = 0
  · rw [hxP]; simpa using P.len_ge
  · have := hx.long P (hx.supp P hxP) hxP
    have := Periodic.d_le_boundaryMargin N ρ.length
    unfold Periodic.fixedMargin at *; omega
omit [DecidableEq α] hx in
theorem retainedLength_le (P : Piece W ρ.length) :
    retainedLength (N := N) (x := x) P ≤ P.len := by
  unfold retainedLength; omega
theorem getElem?_new (P : Piece W ρ.length) {o : ℕ} (ho : o < retainedLength (N := N) (x := x) P) :
    (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.start + o]? =
        (W P.coordinate)[P.start + o]? := by
  have hL := retainedLength_le (N := N) (x := x) P
  have hPl := P.start_add_len
  have hle := P.stop_le_length
  unfold retainedLength at ho hL
  by_cases hh : o < Periodic.boundaryMargin N ρ.length ∨ x P = 0
  · have hret : P.start + o ∉ deletedPositions W ρ N x P.coordinate :=
      hx.not_mem_deletedPositions_of_piece_margin P (by omega)
      (by omega) (hh.elim (fun h => Or.inl (by omega)) (fun h => Or.inr (Or.inl h)))
    rw [← hx.retainedCount_head P (o := o) (hh.elim (fun h => Or.inl h.le) Or.inr) (by omega)]
    exact getElem?_deletePositions _ hret (by omega)
  · push Not at hh
    have hret : P.start + o + Periodic.statePeriodModulus N ρ.length * x P ∉
        deletedPositions W ρ N x P.coordinate :=
      hx.in_piece_not_mem P (by omega) (by omega) (Or.inr (by omega))
    rw [← hx.retainedCount_tail P hh.1 (by omega)]
    unfold keepCut
    rw [editedTuple, getElem?_deletePositions _ hret (by omega), Nat.add_assoc]
    apply P.getElem?_eq_of_mod (by omega) (by omega)
    rw [Periodic.statePeriodModulus, Nat.mul_assoc, Nat.add_mul_mod_self_left]
omit hx in
theorem keepCut_stop_le_length (P : Piece W ρ.length) :
    keepCut W ρ N x P.coordinate P.stop ≤ (editedTuple W ρ N x P.coordinate).length := by
  rw [editedTuple, length_deletePositions]; exact retainedCount_mono P.stop_le_length
theorem imagePiece_period (P : Piece W ρ.length) : ∀ p, keepCut W ρ N x P.coordinate P.start ≤ p →
    p + ρ.length < keepCut W ρ N x P.coordinate P.stop →
    (editedTuple W ρ N x P.coordinate)[p]? = (editedTuple W ρ N x P.coordinate)[p + ρ.length]? := by
  intro p hp hpe
  have hend := hx.retainedCount_piece_end P
  have hL := retainedLength_le (N := N) (x := x) P
  have hPl := P.start_add_len
  unfold retainedLength at hL
  obtain ⟨o, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [hx.getElem?_new P (by unfold retainedLength; omega), Nat.add_assoc,
    hx.getElem?_new P (by unfold retainedLength; omega), ← Nat.add_assoc]
  exact P.periodic _ (by omega) (by omega)
theorem take_drop_editedTuple_eq_root (P : Piece W ρ.length) :
    ((editedTuple W ρ N x P.coordinate).drop (keepCut W ρ N x P.coordinate P.start)).take ρ.length =
        P.root := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ρ.length
  · rw [List.getElem?_take_of_lt hi, List.getElem?_drop, hx.getElem?_new P
      (by have := hx.retainedLength_ge P; omega), Piece.root, List.getElem?_take_of_lt hi,
      List.getElem?_drop]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
      (by rw [P.root_length]; omega)]
theorem imagePiece_maxL (P : Piece W ρ.length) : keepCut W ρ N x P.coordinate P.start = 0 ∨
    (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.start - 1]? ≠
      (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.start - 1 + ρ.length]? := by
  by_cases hs0 : P.start = 0
  · left; rw [hs0]; rfl
  rcases P.left_maximal with h | h
  · exact absurd h hs0
  · right
    have hb := hx.before_not_mem P hs0
    have hk := retainedCount_succ_of_not_mem hb
    rw [show P.start - 1 + 1 = P.start by omega] at hk
    have hd := P.period_pos
    have hlt : P.start - 1 <
        (W P.coordinate).length := by have := P.start_lt_stop; have := P.stop_le_length; omega
    have hnew := hx.getElem?_new P (o := ρ.length - 1) (by have := hx.retainedLength_ge P; omega)
    unfold keepCut at hnew ⊢
    rw [hk, Nat.add_sub_cancel, editedTuple, getElem?_deletePositions _ hb hlt]
    rw [show retainedCount (deletedPositions W ρ N x P.coordinate) (P.start - 1) + ρ.length =
      retainedCount (deletedPositions W ρ N x P.coordinate) P.start + (ρ.length - 1) by omega]
    rw [editedTuple] at hnew
    rw [hnew, show P.start + (ρ.length - 1) = P.start - 1 + ρ.length by omega]
    exact h
theorem imagePiece_maxR (P : Piece W ρ.length) :
    keepCut W ρ N x P.coordinate P.stop = (editedTuple W ρ N x P.coordinate).length ∨
    (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.stop]? ≠
      (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.stop - ρ.length]? := by
  by_cases hE : P.stop = (W P.coordinate).length
  · left; unfold keepCut; rw [hE, editedTuple, length_deletePositions]
  rcases P.right_maximal with h | h
  · exact absurd h hE
  · right
    have he := hx.end_not_mem P
    have hlt : P.stop < (W P.coordinate).length := lt_of_le_of_ne P.stop_le_length hE
    have hend := hx.retainedCount_piece_end P
    have hd := P.period_pos
    have hnl := hx.retainedLength_ge P
    have hL := retainedLength_le (N := N) (x := x) P
    have hPl := P.start_add_len
    unfold retainedLength at hnl hL
    have hnew :=
        hx.getElem?_new P (o := P.len - Periodic.statePeriodModulus N ρ.length * x P - ρ.length)
      (by unfold retainedLength; omega)
    have hmod : (P.len - Periodic.statePeriodModulus N ρ.length * x P - ρ.length) % ρ.length =
        (P.len - ρ.length) % ρ.length := by
      have : P.len - ρ.length = (P.len - Periodic.statePeriodModulus N ρ.length * x P - ρ.length) +
          ρ.length * ((Nat.factorial N) * x P) := by
        have : Periodic.statePeriodModulus N ρ.length * x P = ρ.length *
            ((Nat.factorial N) * x P) := by
          unfold Periodic.statePeriodModulus; ring
        omega
      rw [this, Nat.add_mul_mod_self_left]
    have hper :=
        P.getElem?_eq_of_mod (o₁ := P.len - Periodic.statePeriodModulus N ρ.length * x P - ρ.length)
      (o₂ := P.len - ρ.length) (by omega) (by omega) hmod
    unfold keepCut at hnew hend ⊢
    rw [editedTuple, getElem?_deletePositions _ he hlt, hend]
    rw [editedTuple] at hnew
    rw [show retainedCount (deletedPositions W ρ N x P.coordinate) P.start +
        (P.len - Periodic.statePeriodModulus N ρ.length * x P) -
      ρ.length = retainedCount (deletedPositions W ρ N x P.coordinate) P.start +
          (P.len - Periodic.statePeriodModulus N ρ.length * x P -
      ρ.length) by omega, hnew, hper,
          show P.start + (P.len - ρ.length) = P.stop - ρ.length by omega]
    exact h
def imagePiece (P : Piece W ρ.length) : Piece (editedTuple W ρ N x) ρ.length where
  coordinate := P.coordinate
  start := keepCut W ρ N x P.coordinate P.start
  stop := keepCut W ρ N x P.coordinate P.stop
  long := by rw [hx.retainedCount_piece_end P]; have := hx.retainedLength_ge P;
             unfold retainedLength at this; omega
  stop_le_length := keepCut_stop_le_length (N := N) (x := x) P
  periodic := hx.imagePiece_period P
  primitive := by rw [hx.take_drop_editedTuple_eq_root P]; exact P.primitive
  left_maximal := hx.imagePiece_maxL P
  right_maximal := hx.imagePiece_maxR P
section States
variable [Fintype S] (T : Table α S k) (hN : N = Fintype.card S)
include hN
end States
omit hx in
/-- `c` is the canonical original cut of the cut `c'` of the edited word `l`: a retained
position, or the end of the word, whose image is `c'`. -/
def CanonicalCut (l : Fin k) (c c' : ℕ) : Prop :=
  c ≤ (W l).length ∧ keepCut W ρ N x l c = c' ∧ (c < (W l).length → c ∉ deletedPositions W ρ N x l)
end AdmissibleDeletion
end DeciSigma1.Holes.Periodic


