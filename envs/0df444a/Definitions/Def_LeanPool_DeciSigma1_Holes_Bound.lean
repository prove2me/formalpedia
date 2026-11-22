-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Bound
-- name    : LeanPool_DeciSigma1_Holes_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:12:42.408908+00:00
-- url     : https://prove2.me/theorems/47c9565b-d24f-4268-afb8-7aad57a7e87f
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Bound.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_visitedStates_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_exists_freshDominates_totalLength_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_rejectedTailLength_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_le
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_spec
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_fresh_of_mortal
public import Theorems.Thm_DeciSigma1_Readers_Table_fresh_iff
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_channel
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_visitedStates
public import Theorems.Thm_DeciSigma1_Readers_Table_pair_mem_channel
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_mem_visitedStates
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_succ
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
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
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
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
namespace DeciSigma1.Holes
open DeciSigma1.Readers
open DeciSigma1.Readers.Table DeciSigma1.Readers.StructuralReader
abbrev CoverState (S : Type) (k L : ℕ) := Option (Fin k × (S ⊕ Fin (L + 1)))
variable {α S : Type} [DecidableEq α] [DecidableEq S] {k : ℕ}
namespace Cover
variable (M : StructuralReader α S k) (W : Fin k → List α) (L : ℕ)
def step : CoverState S k L → α → CoverState S k L
  | none, _ => none
  | some (i, Sum.inl s), c =>
    if M.rejectedTailLength W i ≤ L then
      if M.rejected s = false then
        if M.step s c = M.runPrefix W i (M.firstRejection W i) then some (i, Sum.inr 0)
        else if M.rejected (M.step s c) = false then some (i, Sum.inl (M.step s c))
        else none
      else none
    else some (i, Sum.inl (M.step s c))
  | some (i, Sum.inr m), c =>
    if h : (m : ℕ) + 1 ≤ L ∧ (m : ℕ) < M.rejectedTailLength W i ∧
        (W i)[M.firstRejection W i + m]? = some c then
      some (i, Sum.inr ⟨m + 1, by omega⟩)
    else none
def start (i : Fin k) : CoverState S k L :=
  if M.rejectedTailLength W i ≤ L ∧ M.firstRejection W i = 0 then some (i, Sum.inr 0)
  else some (i, Sum.inl (M.start i))
def expect (i : Fin k) (a : ℕ) : CoverState S k L :=
  if M.rejectedTailLength W i ≤ L ∧ M.firstRejection W i ≤ a then
    some (i, Sum.inr ⟨min (a - M.firstRejection W i) L, by omega⟩)
  else some (i, Sum.inl (M.runPrefix W i a))
end Cover
def cover (M : StructuralReader α S k) (W : Fin k → List α) (L : ℕ) :
    Table α (CoverState S k L) k :=
  ⟨Cover.step M W L, Cover.start M W L⟩
def coverProjection (M : StructuralReader α S k) (W : Fin k → List α) (L : ℕ) : CoverState S k L → S
  | none => M.dead
  | some (_, Sum.inl s) => s
  | some (i, Sum.inr m) => M.runPrefix W i (M.firstRejection W i + m)
omit [DecidableEq S] in
theorem cover_card [Fintype S] (L : ℕ) :
    Fintype.card (CoverState S k L) = k * (Fintype.card S + L + 1) + 1 := by
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_sum]
  ring
variable {M : StructuralReader α S k} {W : Fin k → List α} {L : ℕ}
theorem cover_runPrefix {i : Fin k} (hE : M.Eligible W i) {a : ℕ} (ha : a ≤ (W i).length) :
    (cover M W L).runPrefix W i a = Cover.expect M W L i a := by
  have hJ := firstRejection_spec hE
  induction a with
  | zero =>
    simp only [runPrefix_zero, cover, Cover.start, Cover.expect, Nat.le_zero, Nat.zero_sub,
      Nat.zero_min]
    split_ifs <;> simp_all
  | succ a ih =>
    have hlt : a < (W i).length := by omega
    rw [runPrefix_succ W i hlt, ih (by omega)]
    simp only [cover]
    by_cases hw : M.rejectedTailLength W i ≤ L
    · by_cases haJ : M.firstRejection W i ≤ a
      · have hm : a - M.firstRejection W i ≤ L := by unfold rejectedTailLength at hw; omega
        simp only [Cover.expect, hw, haJ, true_and, ite_true,
          show M.firstRejection W i ≤ a + 1 by omega, Cover.step]
        rw [dif_pos]
        · congr 3
          simp only [Fin.ext_iff]
          unfold rejectedTailLength at hw
          omega
        · refine
            ⟨by unfold rejectedTailLength at hw; omega,
                by simp only [min_lt_iff]; unfold rejectedTailLength; omega, ?_⟩
          simp only [min_eq_left hm,
            show M.firstRejection W i + (a - M.firstRejection W i) = a by omega]
          exact List.getElem?_eq_getElem hlt
      · have hra : M.rejected (M.runPrefix W i a) = false := hJ.2.2 a (by omega)
        simp only [Cover.expect, hw, haJ, true_and, ite_false, Cover.step, ite_true, hra]
        rw [← runPrefix_succ W i hlt]
        by_cases hJa : M.firstRejection W i = a + 1
        · rw [if_pos (by rw [hJa]), if_pos (by omega)]
          congr 3
          simp only [Fin.ext_iff, Fin.val_zero]
          omega
        · have hr1 : M.rejected (M.runPrefix W i (a + 1)) = false := hJ.2.2 (a + 1) (by omega)
          have hne : M.runPrefix W i (a + 1) ≠ M.runPrefix W i (M.firstRejection W i) := by
            intro he; rw [he, hJ.2.1] at hr1; exact Bool.noConfusion hr1
          rw [if_neg hne, if_pos hr1, if_neg (by omega)]
    · simp only [Cover.expect, hw, false_and, ite_false, Cover.step]
      rw [runPrefix_succ W i hlt]
theorem cover_run (hW : M.IsHole W) (i : Fin k) {a : ℕ} (ha : a ≤ (W i).length) :
    coverProjection M W L ((cover M W L).runPrefix W i a) = M.runPrefix W i a := by
  rw [cover_runPrefix (hW.1 i) ha]
  unfold Cover.expect
  split_ifs with h
  · simp only [coverProjection]
    congr 1
    have : a - M.firstRejection W i ≤ L := by
      have := h.1; unfold rejectedTailLength at this; omega
    rw [min_eq_left this]
    omega
  · rfl
omit [DecidableEq α] [DecidableEq S] in
theorem cover_expect_ne_none (i : Fin k) (a : ℕ) : Cover.expect M W L i a ≠ none := by
  unfold Cover.expect; split_ifs <;> simp
theorem cover_fresh (hW : M.IsHole W)
  (hL : ∀ i, M.Immortal (M.endState W i) → M.rejectedTailLength W i ≤ L) (i : Fin k) :
  (cover M W L).Fresh W i := by
  classical
  rw [fresh_iff]
  intro a ha
  simp only [endState]
  rw [cover_runPrefix (hW.1 i) ha.le, cover_runPrefix (hW.1 i) le_rfl]
  by_cases hw : M.rejectedTailLength W i ≤ L
  · have hJ := firstRejection_le (hW.1 i)
    unfold Cover.expect
    have hlen : M.rejectedTailLength W i = (W i).length - M.firstRejection W i := rfl
    simp only [hw, true_and, show M.firstRejection W i ≤ (W i).length from hJ, ite_true]
    split_ifs with h
    · simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, true_and, Sum.inr.injEq,
        Fin.ext_iff]
      omega
    · simp
  · have hm : ¬ M.Immortal (M.endState W i) := fun hi => hw (hL i hi)
    have hf := fresh_of_mortal (hW.1 i) hm
    rw [fresh_iff] at hf
    simp only [Cover.expect, hw, false_and, ite_false, ne_eq, Option.some.injEq,
      Prod.mk.injEq, true_and, Sum.inl.injEq]
    exact hf a ha
theorem coverProjection_step {c : CoverState S k L} {x : α} (h : Cover.step M W L c x ≠ none) :
    coverProjection M W L (Cover.step M W L c x) = M.step (coverProjection M W L c) x := by
  match c with
  | none => exact absurd rfl h
  | some (i, Sum.inl s) =>
    simp only [Cover.step] at h ⊢
    split_ifs at h ⊢ with h1 h2 h3 h4
    · simp only [coverProjection, Nat.add_zero, Fin.val_zero]; exact h3.symm
    · rfl
    · exact absurd rfl h
    · exact absurd rfl h
    · rfl
  | some (i, Sum.inr m) =>
    simp only [Cover.step] at h ⊢
    split_ifs at h ⊢ with h1
    · obtain ⟨_, h2, h3⟩ := h1
      have hlt : M.firstRejection W i + m < (W i).length := by
        rcases Nat.lt_or_ge (M.firstRejection W i + m) (W i).length with h4 | h4
        · exact h4
        · rw [List.getElem?_eq_none h4] at h3; exact absurd h3 (by simp)
      simp only [coverProjection]
      rw [show M.firstRejection W i + (m + 1) = M.firstRejection W i + m + 1 by omega,
          runPrefix_succ W i hlt]
      congr 1
      rw [List.getElem?_eq_getElem hlt] at h3
      exact Option.some.inj h3
    · exact absurd rfl h
theorem coverProjection_start (i : Fin k) :
    coverProjection M W L ((cover M W L).start i) = M.start i := by
  simp only [cover, Cover.start]
  split_ifs with h
  · simp only [coverProjection, h.2, Nat.add_zero, Fin.val_zero, runPrefix_zero]
  · rfl
theorem coverProjection_runFrom (c : CoverState S k L) (u : List α)
    (h : ∀ a ≤ u.length, runFrom (cover M W L).step c (u.take a) ≠ none) :
    coverProjection M W L (runFrom (cover M W L).step c u) =
      runFrom M.step (coverProjection M W L c) u := by
  induction u generalizing c with
  | nil => rfl
  | cons x u ih =>
    have h1 : Cover.step M W L c x ≠ none := by simpa [cover] using h 1 (by simp)
    rw [runFrom_cons, runFrom_cons,
      ih _ (fun a ha => by simpa [cover] using h (a + 1) (by simp; omega))]
    exact congrArg (fun s => runFrom M.step s u) (coverProjection_step h1)
theorem cover_project_of_dom (hW : M.IsHole W) {U : Fin k → List α}
    (hU : Dominates (cover M W L) U W) : M.IsHole U ∧ ∀ i, M.endState U i = M.endState W i := by
  -- every cover state of `U` is a cover state of `W`
  have hvis : ∀ i a, a ≤ (U i).length →
      ∃ b ≤ (W i).length, (cover M W L).runPrefix U i a = (cover M W L).runPrefix W i b := by
    intro i a ha
    obtain ⟨b, hb, he⟩ :=
        mem_visitedStates.mp (hU.visitedStates_subset i (runPrefix_mem_visitedStates U i ha))
    exact ⟨b, hb, he.symm⟩
  have hnn : ∀ i a, a ≤ (U i).length → (cover M W L).runPrefix U i a ≠ none := by
    intro i a ha
    obtain ⟨b, hb, he⟩ := hvis i a ha
    rw [he, cover_runPrefix (hW.1 i) hb]
    exact cover_expect_ne_none i b
  have hproj : ∀ i a, a ≤ (U i).length →
      coverProjection M W L ((cover M W L).runPrefix U i a) = M.runPrefix U i a := by
    intro i a ha
    simp only [runPrefix]
    rw [coverProjection_runFrom _ _ (fun b hb => by
      rw [List.take_take]
      exact hnn i (min b a) (by omega)), coverProjection_start]
  have hstate : ∀ i a, a ≤ (U i).length → ∃ b ≤ (W i).length, M.runPrefix U i a =
      M.runPrefix W i b := by
    intro i a ha
    obtain ⟨b, hb, he⟩ := hvis i a ha
    exact ⟨b, hb, by rw [← hproj i a ha, he, cover_run hW i hb]⟩
  have hends : ∀ i, M.endState U i = M.endState W i := by
    intro i
    have h1 := hproj i _ le_rfl
    simp only [endState] at h1 ⊢
    rw [← h1, show (cover M W L).runPrefix U i (U i).length = (cover M W L).endState U i from rfl,
      hU.endState_eq i, show (cover M W L).endState W i =
          (cover M W L).runPrefix W i (W i).length from rfl,
      cover_run hW i le_rfl]
  refine ⟨⟨fun i => ⟨fun a ha => ?_, ?_⟩, fun i j pq hpq => ?_⟩, hends⟩
  · obtain ⟨b, hb, he⟩ := hstate i a ha
    rw [he]; exact (hW.1 i).1 b hb
  · rw [hends i]; exact (hW.1 i).2
  · obtain ⟨a, ha, b, hb, hp, rfl⟩ := mem_channel.mp hpq
    have hc := hU.channel_subset i j (pair_mem_channel ha hb hp)
    obtain ⟨a', ha', b', hb', hp', he⟩ := mem_channel.mp hc
    simp only [Prod.mk.injEq] at he
    have e1 : M.runPrefix U i a = M.runPrefix W i a' := by
      rw [← hproj i a ha, he.1, cover_run hW i ha']
    have e2 : M.runPrefix U j b = M.runPrefix W j b' := by
      rw [← hproj j b hb, he.2, cover_run hW j hb']
    simp only [e1, e2]
    exact hW.2 i j _ (pair_mem_channel ha' hb' hp')
theorem cover_project (hW : M.IsHole W) {U : Fin k → List α}
    (hU : FreshDominates (cover M W L) U W) : M.IsHole U ∧ ∀ i, M.endState U i = M.endState W i :=
  cover_project_of_dom hW hU.1
section SmallHole
variable [Fintype α] [Fintype S]
omit [Fintype α] in
/-- A hole whose immortal rejected tails have length at most `L` gives a hole of total length
at most `freshTupleBound k (k · (N + L + 1) + 1)`: a fresh dominator of the hole in its
cover. -/
theorem exists_hole_totalLength_le_of_tails (M : StructuralReader α S k)
    {W : Fin k → List α}
    (hW : M.IsHole W) {L : ℕ}
    (hL : ∀ i, M.Immortal (M.endState W i) → M.rejectedTailLength W i ≤ L) :
    ∃ U, M.IsHole U ∧
      totalLength U ≤ Fresh.freshTupleBound k (k * (Fintype.card S + L + 1) + 1) := by
  classical
  obtain ⟨U, hU, hb⟩ := Fresh.exists_freshDominates_totalLength_le (cover_fresh hW hL)
  rw [cover_card] at hb
  exact ⟨U, (cover_project hW hU).1, hb⟩
def smallHoleBound (σ k N : ℕ) : ℕ :=
  Fresh.freshTupleBound k (k * (N + Tail.tailLengthBound σ k N + 1) + 1)
theorem exists_small_hole (M : StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧ totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S) := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨W', hW', hL⟩ := Tail.exists_hole_rejectedTailLength_le M hW
  exact exists_hole_totalLength_le_of_tails M hW' hL
theorem exists_hole_iff_bounded (M : StructuralReader α S k) :
    (∃ W ∈ wordTuplesUpTo k (smallHoleBound (Fintype.card α) k (Fintype.card S)), M.IsHole W) ↔
      ∃ W, M.IsHole W := by
  constructor
  · rintro ⟨W, _, hW⟩; exact ⟨W, hW⟩
  · intro h
    obtain ⟨W, hW, hb⟩ := exists_small_hole M h
    exact ⟨W, mem_wordTuplesUpTo.mpr hb, hW⟩
def decideHole (M : StructuralReader α S k) : Decidable (∃ W, M.IsHole W) :=
  decidable_of_iff _ (exists_hole_iff_bounded M)
end SmallHole
end DeciSigma1.Holes


