-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
-- name    : LeanPool_DeciSigma1_Holes_Tail_Compression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:56:32.600074+00:00
-- url     : https://prove2.me/theorems/0e0b9562-8517-4718-b33e-42a7c903192a
-- title:
--   Compression
-- statement:
--   Definitions and structural lemmas for Compression, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Compression.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_root_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_sep
public import Theorems.Thm_DeciSigma1_Holes_Periodic_fw_overlap
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_piecesOf
public import Theorems.Thm_DeciSigma1_Holes_Periodic_piece_ends_sep
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_le_card_sub_one_of_injOn
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_runPrefix_ne_of_le_firstRejection
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_runPrefix_ne_of_mortal
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_length_eq
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
section Keep
variable {D : Finset ℕ}
end Keep
theorem card_le_two_of_gaps (A : Finset ℕ) {a d : ℕ} (hA : ∀ x ∈ A, a < x ∧ x < a + 2 * d)
    (hgap : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → d < x - y ∨ d < y - x) : A.card ≤ 2 := by
  by_contra h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp (show 2 < A.card by omega)
  have := hA x hx; have := hA y hy; have := hA z hz
  have := hgap x hx y hy hxy; have := hgap x hx z hz hxz; have := hgap y hy z hz hyz
  omega
theorem card_le_two_of_gaps_with_exception (A : Finset ℕ) {a c d : ℕ}
    (hA : ∀ x ∈ A, x = c ∨ (a < x ∧ x < a + d))
    (hgap : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → d < x - y ∨ d < y - x) : A.card ≤ 2 := by
  by_contra h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp (show 2 < A.card by omega)
  have := hA x hx; have := hA y hy; have := hA z hz
  have := hgap x hx y hy hxy; have := hgap x hx z hz hxz; have := hgap y hy z hz hyz
  omega
section Count
variable [DecidableEq α] {U : Fin k → List α} {d : ℕ}
omit [DecidableEq α] in
/-- Distinct pieces of one word have ends more than `d` apart. -/
theorem piece_end_gap {P Q : Piece U d} (hl : P.coordinate = Q.coordinate) (hne : P ≠ Q) :
    d < P.stop - Q.stop ∨ d < Q.stop - P.stop := by
  have := piece_ends_sep hne hl
  omega
omit [DecidableEq α] in
theorem piece_end_injOn (A : Finset (Piece U d)) {i : Fin k} (hA : ∀ P ∈ A, P.coordinate = i) :
    Set.InjOn Piece.stop (A : Set (Piece U d)) := by
  intro P hP Q hQ he
  by_contra hne
  have := piece_end_gap ((hA P hP).trans (hA Q hQ).symm) hne
  omega
omit [DecidableEq α] in
/-- Comparable followers in one word: the later end's suffix is a prefix of the earlier one's. -/
theorem followerEdge_drop {P Q : Piece U d} (hl : P.coordinate = Q.coordinate)
    (hlt : P.stop < Q.stop) (hG : FollowerEdge P Q) :
    (U P.coordinate).drop Q.stop <+: (U P.coordinate).drop P.stop := by
  rcases hG with h | h
  · simp only [Piece.follower] at h
    rw [hl] at h
    have := h.length_le
    simp only [List.length_drop] at this
    have := Q.stop_le_length
    omega
  · simpa only [Piece.follower, hl] using h
variable [DecidableEq S]
omit [DecidableEq α] in
omit [DecidableEq S] in
/-- Pieces of one word with pairwise comparable followers, whose states at their ends are distinct
and live, number at most `N - 1`. -/
theorem card_chain_le [Fintype S] (M : StructuralReader α S k) (A : Finset (Piece U d)) {i : Fin k}
    (hA : ∀ P ∈ A, P.coordinate = i)
    (hdist : ∀ P ∈ A, ∀ Q ∈ A, P.stop < Q.stop → M.runPrefix U i P.stop ≠ M.runPrefix U i Q.stop)
    (hlive : ∀ P ∈ A, M.runPrefix U i P.stop ≠ M.dead) : A.card ≤ Fintype.card S - 1 := by
  classical
  exact
    card_le_card_sub_one_of_injOn A Piece.stop (piece_end_injOn A hA)
      (fun P => M.runPrefix U i P.stop) M.dead hdist hlive
omit [DecidableEq S] in
/-- The pieces of the class of `ρ` in word `i` that end after the first rejected cut number at
most two for each designated run of the word plus the uncovered positions of its rejected
tail. -/
theorem card_tail_le (M : StructuralReader α S k) {ρ : List α} (runs : Finset (RunSpec k))
    (hruns : ∀ r ∈ runs,
        IsPeriodicPiece U r.period r.coordinate r.start r.stop ∧ r.period ≤ ρ.length) {i : Fin k}
    (B : Finset (Piece U ρ.length))
    (hB : ∀ P ∈ B, P ∈ piecesOf U ρ ∧ P.coordinate = i ∧ M.firstRejection U i < P.stop) :
    B.card ≤ 2 * (runs.filter (fun r => r.coordinate = i)).card +
        (uncoveredTailPositions M U runs i).card := by
  classical
  have hsub : B ⊆ (runs.filter (fun r => r.coordinate = i)).biUnion
      (fun r => B.filter (fun P => r.start ≤ P.stop - 1 ∧ P.stop - 1 < r.stop)) ∪
        B.filter (fun P => P.stop - 1 ∈ uncoveredTailPositions M U runs i) := by
    intro P hP
    obtain ⟨-, hPl, hPJ⟩ := hB P hP
    by_cases hu : P.stop - 1 ∈ uncoveredTailPositions M U runs i
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hP, hu⟩)
    · apply Finset.mem_union_left
      simp only [uncoveredTailPositions, Finset.mem_filter, Finset.mem_Ico, not_and, not_not] at hu
      have hle := P.stop_le_length
      rw [hPl] at hle
      obtain ⟨r, hr, hrl, h1, h2⟩ := hu ⟨by omega, by omega⟩
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hrl⟩,
        Finset.mem_filter.mpr ⟨hP, h1, h2⟩⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
  · refine (Finset.card_biUnion_le_card_mul _ _ 2 fun r hr => ?_).trans_eq (Nat.mul_comm _ _)
    obtain ⟨hr, hrl⟩ := Finset.mem_filter.mp hr
    obtain ⟨hpc, hdr⟩ := hruns r hr
    set Br := B.filter (fun P => r.start ≤ P.stop - 1 ∧ P.stop - 1 < r.stop)
    have hBr : ∀ P ∈ Br, P ∈ piecesOf U ρ ∧ P.coordinate = i ∧ r.start < P.stop ∧ P.stop ≤
        r.stop := by
      intro P hP
      obtain ⟨hP, h1, h2⟩ := Finset.mem_filter.mp hP
      have := P.long; have := P.period_pos
      exact ⟨(hB P hP).1, (hB P hP).2.1, by omega, by omega⟩
    have hinj := piece_end_injOn Br (fun P hP => (hBr P hP).2.1)
    rw [← Finset.card_image_of_injOn hinj]
    have hgap : ∀ x ∈ Br.image Piece.stop, ∀ y ∈ Br.image Piece.stop, x ≠ y →
        ρ.length < x - y ∨ ρ.length < y - x := by
      intro x hx y hy hxy
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hy
      exact piece_end_gap ((hBr P hP).2.1.trans (hBr Q hQ).2.1.symm) (fun h => hxy (h ▸ rfl))
    let R : Piece U r.period := Piece.ofIsPeriodicPiece hpc
    by_cases hcls : IsConjugate R.root ρ
    · -- a run of the same class: its own end, and at most one end in `(R.start, R.start + d)`
      have hdeq : r.period = ρ.length := by
        have := hcls.length_eq; rw [R.root_length] at this; exact this.symm
      have hpc' : IsPeriodicPiece U ρ.length r.coordinate r.start r.stop := hdeq ▸ hpc
      let R' : Piece U ρ.length := Piece.ofIsPeriodicPiece hpc'
      apply card_le_two_of_gaps_with_exception _ (a := r.start) (c := r.stop) _ hgap
      intro x hx
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨-, hPl, h1, h2⟩ := hBr P hP
      have hR's : R'.start = r.start := rfl
      have hR'e : R'.stop = r.stop := rfl
      by_cases hPR : P = R'
      · left; rw [hPR]; exact hR'e
      · right
        have hl : P.coordinate = R'.coordinate := by rw [hPl]; exact hrl.symm
        have := P.long
        rcases le_total P.start R'.start with hs | hs
        · have := Piece.sep hPR hl hs
          omega
        · have := Piece.sep (Ne.symm hPR) hl.symm hs
          omega
    · -- a run of another class: ends in `(R.start, R.start + 2d)` (Fine–Wilf)
      apply card_le_two_of_gaps _ (a := r.start) _ hgap
      intro x hx
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hPc, hPl, h1, h2⟩ := hBr P hP
      have hdiff : ¬ IsConjugate P.root R.root := fun h =>
        hcls (h.symm.trans ((mem_piecesOf U).mp hPc))
      have hfw := fw_overlap P R hdiff hdr (by rw [hPl]; exact hrl.symm)
      have := P.long
      change min P.stop r.stop - max P.start r.start < ρ.length + r.period at hfw
      refine ⟨h1, ?_⟩
      rcases le_total P.start r.start with hs | hs
      · rw [min_eq_left h2, max_eq_right hs] at hfw; omega
      · rw [min_eq_left h2, max_eq_left hs] at hfw; omega
  · apply Finset.card_le_card_of_injOn (fun P => P.stop - 1)
    · intro P hP
      exact (Finset.mem_filter.mp hP).2
    · intro P hP Q hQ he
      have hPB := (Finset.mem_filter.mp hP).1
      have hQB := (Finset.mem_filter.mp hQ).1
      have := (hB P hPB).2.2; have := (hB Q hQB).2.2
      apply piece_end_injOn B (fun P hP => (hB P hP).2.1) hPB hQB
      simp only at he
      omega
open Classical in
/-- Pieces ending at or before first rejection, and pieces of mortal words, have bounded comparable
height. The remaining pieces are counted by designated runs and uncovered tail positions. -/
noncomputable def occurrenceSplit [Fintype S] (M : StructuralReader α S k)
    (hU : M.IsHole U) (ρ : List α) (runs : Finset (RunSpec k))
    (hruns : ∀ r ∈ runs,
      IsPeriodicPiece U r.period r.coordinate r.start r.stop ∧ r.period ≤ ρ.length)
    {t : ℕ} (ht : 2 * runs.card + ∑ i, (if M.Immortal (M.endState U i) then
      (uncoveredTailPositions M U runs i).card else 0) ≤ t) :
    OccurrenceSplit U ρ (k * (Fintype.card S - 1)) t := by
  classical
  refine ⟨(fun P => ¬ M.Immortal (M.endState U P.coordinate) ∨
    P.stop ≤ M.firstRejection U P.coordinate), ?_, ?_⟩
  · intro c _ hhead hchain
    have hword : ∀ i, (c.filter (fun P => P.coordinate = i)).card ≤ Fintype.card S - 1 := by
      intro i
      set ci := c.filter (fun P => P.coordinate = i)
      have hci : ∀ P ∈ ci, P ∈ c ∧ P.coordinate = i := fun P hP => Finset.mem_filter.mp hP
      have hdrop : ∀ P ∈ ci, ∀ Q ∈ ci, P.stop < Q.stop →
          (U i).drop Q.stop <+: (U i).drop P.stop := by
        intro P hP Q hQ hlt
        have h := followerEdge_drop ((hci P hP).2.trans (hci Q hQ).2.symm) hlt
          (hchain P (hci P hP).1 Q (hci Q hQ).1)
        rwa [(hci P hP).2] at h
      apply card_chain_le M ci (fun P hP => (hci P hP).2)
      · intro P hP Q hQ hlt
        by_cases him : M.Immortal (M.endState U i)
        · have hQJ := hhead Q (hci Q hQ).1
          rw [(hci Q hQ).2] at hQJ
          exact StructuralReader.runPrefix_ne_of_le_firstRejection (hU.1 i) hlt
            (hQJ.resolve_left (not_not.mpr him)) (hdrop P hP Q hQ hlt)
        · have hlen := Q.stop_le_length
          rw [(hci Q hQ).2] at hlen
          exact StructuralReader.runPrefix_ne_of_mortal (hU.1 i) him hlt hlen
            (hdrop P hP Q hQ hlt)
      · intro P _; exact (hU.1 i).runPrefix_ne _
    calc c.card = ∑ i, (c.filter (fun P => P.coordinate = i)).card :=
          Finset.card_eq_sum_card_fiberwise (fun P _ => Finset.mem_univ P.coordinate)
      _ ≤ ∑ _ : Fin k, (Fintype.card S - 1) := Finset.sum_le_sum fun i _ => hword i
      _ = k * (Fintype.card S - 1) := by simp
  · intro c hcsub htail
    have hword : ∀ i, (c.filter (fun P => P.coordinate = i)).card ≤
        2 * (runs.filter (fun r => r.coordinate = i)).card +
          (if M.Immortal (M.endState U i) then
            (uncoveredTailPositions M U runs i).card else 0) := by
      intro i
      by_cases him : M.Immortal (M.endState U i)
      · rw [if_pos him]
        apply card_tail_le M runs hruns
        intro P hP
        obtain ⟨hP, hPi⟩ := Finset.mem_filter.mp hP
        have hPJ := htail P hP
        rw [hPi] at hPJ
        exact ⟨hcsub hP, hPi, by omega⟩
      · have he : c.filter (fun P => P.coordinate = i) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro P hP
          obtain ⟨hP, hPi⟩ := Finset.mem_filter.mp hP
          exact htail P hP (Or.inl (by rwa [hPi]))
        rw [he, Finset.card_empty]
        exact Nat.zero_le _
    refine le_trans ?_ ht
    calc c.card = ∑ i, (c.filter (fun P => P.coordinate = i)).card :=
          Finset.card_eq_sum_card_fiberwise (fun P _ => Finset.mem_univ P.coordinate)
      _ ≤ ∑ i, (2 * (runs.filter (fun r => r.coordinate = i)).card +
          (if M.Immortal (M.endState U i) then
            (uncoveredTailPositions M U runs i).card else 0)) :=
        Finset.sum_le_sum fun i _ => hword i
      _ = 2 * runs.card + ∑ i, (if M.Immortal (M.endState U i) then
          (uncoveredTailPositions M U runs i).card else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (RunSpec.coordinate r))]
end Count
section Pass
variable [DecidableEq α] [Fintype S] [DecidableEq S]
end Pass
def compressionLengthBoundIter (k N D : ℕ) : ℕ → ℕ → ℕ
  | 0, E => E
  | n + 1, E => compressionLengthBoundIter k N D n
      (E + (n + 1) * Periodic.pieceLengthBound N D (k * (N - 1)) (2 * (n + 1) + E))
def compressionLengthBound (k N R D E : ℕ) : ℕ := compressionLengthBoundIter k N D (k * R) E
section Passes
variable [DecidableEq α] [Fintype S] [DecidableEq S]
end Passes
def tailLengthBound (σ k N : ℕ) : ℕ :=
  compressionLengthBound k N ((levelBounds σ k N).pieceCountBase + 3)
      ((levelBounds σ k N).periodBound (levelCount k))
    (uncoveredLengthBound (levelBounds σ k N))
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]
end DeciSigma1.Holes.Tail


