-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
-- name    : LeanPool_DeciSigma1_Readers_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:41:09.292826+00:00
-- url     : https://prove2.me/theorems/7ea82ba1-18dd-4040-8e0f-934006895a66
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Theorems.Thm_DeciSigma1_Automata_Semiautomaton_pathSafe_append
public import Theorems.Thm_DeciSigma1_Automata_Semiautomaton_pathSafe_iff
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_append
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Readers
open DeciSigma1.Automata
structure Table (α S : Type) (k : ℕ) where
  /-- The transition function. -/
  step : S → α → S
  /-- The start state of each coordinate. -/
  start : Fin k → S
variable {α S : Type} {k : ℕ}
namespace Table
variable (T : Table α S k)
def runPrefix (W : Fin k → List α) (i : Fin k) (a : ℕ) : S :=
  runFrom T.step (T.start i) ((W i).take a)
def endState (W : Fin k → List α) (i : Fin k) : S := T.runPrefix W i (W i).length
def visitedStates [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Finset S :=
  (Finset.range ((W i).length + 1)).image (T.runPrefix W i)
def properVisitedStates [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Finset S :=
  (Finset.range (W i).length).image (T.runPrefix W i)
def pathChannel [DecidableEq α] [DecidableEq S] (p : S) (x : List α) (q : S) (y : List α) :
    Finset (S × S) :=
  (((Finset.range (x.length + 1)) ×ˢ (Finset.range (y.length + 1))).filter
      (fun ab => y.drop ab.2 <+: x.drop ab.1)).image
    (fun ab => (runFrom T.step p (x.take ab.1), runFrom T.step q (y.take ab.2)))
def channel [DecidableEq α] [DecidableEq S] (W : Fin k → List α) (i j : Fin k) : Finset (S × S) :=
  T.pathChannel (T.start i) (W i) (T.start j) (W j)
def Fresh [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Prop :=
  T.endState W i ∉ T.properVisitedStates W i
instance [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Decidable (T.Fresh W i) :=
  inferInstanceAs (Decidable (_ ∉ _))
variable {T}
@[simp] theorem runPrefix_zero (W : Fin k → List α) (i : Fin k) :
    T.runPrefix W i 0 = T.start i := by
  simp [runPrefix]
end Table
def totalLength (W : Fin k → List α) : ℕ := ∑ i, (W i).length
theorem length_le_totalLength (W : Fin k → List α) (i : Fin k) : (W i).length ≤ totalLength W :=
  Finset.single_le_sum (f := fun i => (W i).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
def wordTuplesUpTo [Fintype α] [DecidableEq α] (k B : ℕ) : Finset (Fin k → List α) :=
  (Fintype.piFinset fun _ => wordsUpTo B).filter (fun W => totalLength W ≤ B)
@[simp] theorem mem_wordTuplesUpTo [Fintype α] [DecidableEq α] {B : ℕ} {W : Fin k → List α} :
    W ∈ wordTuplesUpTo k B ↔ totalLength W ≤ B := by
  simp only [wordTuplesUpTo, Finset.mem_filter, Fintype.mem_piFinset, mem_wordsUpTo,
    and_iff_right_iff_imp]
  intro h i
  exact (length_le_totalLength W i).trans h
open Table
section Domination
variable [DecidableEq α] [DecidableEq S]
structure Dominates (T : Table α S k) (U W : Fin k → List α) : Prop where
  endState_eq : ∀ i, T.endState U i = T.endState W i
  visitedStates_subset : ∀ i, T.visitedStates U i ⊆ T.visitedStates W i
  channel_subset : ∀ i j, T.channel U i j ⊆ T.channel W i j
def FreshDominates (T : Table α S k) (U W : Fin k → List α) : Prop :=
  Dominates T U W ∧ ∀ i, T.Fresh U i
def IsMinimalFresh (T : Table α S k) (W : Fin k → List α) : Prop :=
  (∀ i, T.Fresh W i) ∧ ∀ U, FreshDominates T U W → totalLength W ≤ totalLength U
variable {T : Table α S k} {U V W : Fin k → List α}
theorem dominates_iff : Dominates T U W ↔ (∀ i, T.endState U i = T.endState W i) ∧
    (∀ i, T.visitedStates U i ⊆ T.visitedStates W i) ∧ ∀ i j, T.channel U i j ⊆ T.channel W i j :=
  ⟨fun h => ⟨h.endState_eq, h.visitedStates_subset, h.channel_subset⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
instance (T : Table α S k) (U W : Fin k → List α) : Decidable (Dominates T U W) :=
  decidable_of_iff _ dominates_iff.symm
instance (T : Table α S k) (U W : Fin k → List α) : Decidable (FreshDominates T U W) :=
  inferInstanceAs (Decidable (_ ∧ _))
theorem isMinimalFresh_iff_bounded [Fintype α] : IsMinimalFresh T W ↔ (∀ i, T.Fresh W i) ∧
    ∀ U ∈ wordTuplesUpTo k (totalLength W), FreshDominates T U W → totalLength W ≤
        totalLength U := by
  constructor
  · exact fun h => ⟨h.1, fun U _ hU => h.2 U hU⟩
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun U hU => ?_⟩
    by_contra hlt
    exact hlt (h U (mem_wordTuplesUpTo.mpr (by omega)) hU)
instance [Fintype α] (T : Table α S k) (W : Fin k → List α) : Decidable (IsMinimalFresh T W) :=
  decidable_of_iff _ isMinimalFresh_iff_bounded.symm
end Domination
structure StructuralReader (α S : Type) (k : ℕ) extends Table α S k where
  /-- The absorbing dead state. -/
  dead : S
  /-- The rejected states. -/
  rejected : S → Bool
  /-- The admitted pairs (host state, target state). -/
  admitted : S → S → Bool
  step_dead : ∀ a, step dead a = dead
  rejected_dead : rejected dead = false
  rejected_step : ∀ q a, rejected q = true → step q a ≠ dead → rejected (step q a) = true
  not_admitted_step_of_rejected : ∀ p q a, rejected q = true → step q a ≠ dead →
      admitted p (step q a) = false
namespace StructuralReader
variable (M : StructuralReader α S k)
def Eligible (W : Fin k → List α) (i : Fin k) : Prop :=
  (∀ a ≤ (W i).length, M.runPrefix W i a ≠ M.dead) ∧ M.rejected (M.endState W i) = true
def IsHole [DecidableEq α] [DecidableEq S] (W : Fin k → List α) : Prop :=
  (∀ i, M.Eligible W i) ∧ ∀ i j, ∀ pq ∈ M.channel W i j, M.admitted pq.1 pq.2 = false
instance [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Decidable (M.Eligible W i) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance [DecidableEq α] [DecidableEq S] (W : Fin k → List α) : Decidable (M.IsHole W) :=
  inferInstanceAs (Decidable (_ ∧ _))
def Immortal (q : S) : Prop :=
  ∀ n, ∃ u : List α, u.length = n ∧ ∀ a ≤ n, runFrom M.step q (u.take a) ≠ M.dead
def LiveAlong (q : S) (u : List α) : Prop := ∀ a ≤ u.length, runFrom M.step q (u.take a) ≠ M.dead
instance [DecidableEq S] (q : S) (u : List α) : Decidable (M.LiveAlong q u) :=
  inferInstanceAs (Decidable (∀ a ≤ u.length, _))
def firstRejection (W : Fin k → List α) (i : Fin k) : ℕ :=
  ((List.range ((W i).length + 1)).find? (fun a => M.rejected (M.runPrefix W i a))).getD
      (W i).length
def rejectedTailLength (W : Fin k → List α) (i : Fin k) : ℕ := (W i).length - M.firstRejection W i
def HasMixedMortality (W : Fin k → List α) : Prop :=
  (∃ i, M.Immortal (M.endState W i)) ∧ ∃ j, ¬ M.Immortal (M.endState W j)
variable {M}
def toSemiautomaton (M : StructuralReader α S k) : Automata.Semiautomaton α S :=
  ⟨M.dead, M.step⟩
theorem liveAlong_iff_pathSafe (q : S) (u : List α) :
    M.LiveAlong q u ↔ (toSemiautomaton M).PathSafe (· ≠ M.dead) q u := by
  rw [Automata.Semiautomaton.pathSafe_iff]; rfl
theorem liveAlong_append (q : S) (u v : List α) :
    M.LiveAlong q (u ++ v) ↔ M.LiveAlong q u ∧ M.LiveAlong (runFrom M.step q u) v := by
  simp only [liveAlong_iff_pathSafe]
  exact Automata.Semiautomaton.pathSafe_append _ _ q u v
theorem LiveAlong.take {q : S} {u : List α} (h : M.LiveAlong q u) (n : ℕ) :
    M.LiveAlong q (u.take n) := by
  have h' := (liveAlong_append q (u.take n) (u.drop n)).mp (by rwa [List.take_append_drop])
  exact h'.1
theorem LiveAlong.self {q : S} {u : List α} (h : M.LiveAlong q u) : q ≠ M.dead := by
  simpa using h 0 (Nat.zero_le _)
theorem liveAlong_nil {q : S} (h : q ≠ M.dead) : M.LiveAlong q [] := by
  intro a _; simpa using h
theorem liveAlong_flatten_replicate {p : S} {v : List α} (hv : M.LiveAlong p v)
    (hc : runFrom M.step p v = p) (m : ℕ) : M.LiveAlong p (List.replicate m v).flatten := by
  induction m with
  | zero => exact liveAlong_nil hv.self
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, liveAlong_append, hc]
    exact ⟨hv, ih⟩
theorem immortal_of_long {q : S} (h : ∀ n, ∃ u : List α, n ≤ u.length ∧ M.LiveAlong q u) :
    M.Immortal q := by
  intro n
  obtain ⟨u, hn, hu⟩ := h n
  refine ⟨u.take n, by simp [hn], fun a ha => ?_⟩
  have := hu.take n a (by simp; omega)
  exact this
theorem immortal_of_cycle {q : S} {u v : List α} (hv : v ≠ []) (hl : M.LiveAlong q (u ++ v))
    (hc : runFrom M.step (runFrom M.step q u) v = runFrom M.step q u) : M.Immortal q := by
  rw [liveAlong_append] at hl
  apply immortal_of_long
  intro n
  refine ⟨u ++ (List.replicate n v).flatten, ?_, ?_⟩
  · have hv1 : 1 ≤ v.length := List.length_pos_iff.mpr hv
    simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
      smul_eq_mul]
    nlinarith
  · rw [liveAlong_append]
    exact ⟨hl.1, liveAlong_flatten_replicate hl.2 hc n⟩
theorem immortal_iff_card [Fintype S] {q : S} : M.Immortal q ↔ ∃ u : List α,
    u.length = Fintype.card S ∧ ∀ a ≤ u.length, runFrom M.step q (u.take a) ≠ M.dead := by
  constructor
  · intro h
    obtain ⟨u, hu, hl⟩ := h (Fintype.card S)
    exact ⟨u, hu, hu ▸ hl⟩
  · rintro ⟨u, hu, hl⟩
    have hl' : M.LiveAlong q u := hl
    let f : Fin (Fintype.card S + 1) → S := fun a => runFrom M.step q (u.take a)
    obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    wlog hlt : a < b generalizing a b
    · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
    have ha : (a : ℕ) < b := hlt
    have hb : (b : ℕ) ≤ u.length := by have := b.isLt; omega
    refine immortal_of_cycle (u := u.take a) (v := (u.drop a).take (b - a)) ?_ ?_ ?_
    · simp; omega
    · rw [← List.take_add, show (a : ℕ) + (b - a) = b by omega]
      exact hl'.take b
    · rw [← runFrom_append, ← List.take_add, show (a : ℕ) + (b - a) = b by omega]
      exact he.symm
def wordsOfLength [Fintype α] [DecidableEq α] (n : ℕ) : Finset (List α) :=
  (Automata.wordsUpTo n).filter (fun u : List α => u.length = n)
theorem mem_wordsOfLength [Fintype α] [DecidableEq α] {n : ℕ} {u : List α} :
    u ∈ wordsOfLength n ↔ u.length = n := by
  simp only [wordsOfLength, Finset.mem_filter, Automata.mem_wordsUpTo, and_iff_right_iff_imp]
  exact fun h => h.le
instance [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S] : DecidablePred M.Immortal :=
  fun q => decidable_of_iff (∃ u ∈ wordsOfLength (α := α) (Fintype.card S), M.LiveAlong q u)
    (by
      rw [immortal_iff_card]
      simp only [mem_wordsOfLength]
      rfl)
instance [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S] (W : Fin k → List α) :
    Decidable (M.HasMixedMortality W) := inferInstanceAs (Decidable (_ ∧ _))
end StructuralReader
end DeciSigma1.Readers


