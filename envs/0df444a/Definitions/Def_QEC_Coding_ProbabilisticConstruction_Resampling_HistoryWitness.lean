-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:15:55.105753+00:00
-- url     : https://prove2.me/theorems/7c6e91db-6d7f-46af-8b6e-c478a01c6154
-- title:
--   History Witness
-- statement:
--   Definitions and structural lemmas for History Witness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
def pathLabel (root : I) : List I → I
  | [] => root
  | j :: rest => pathLabel j rest
@[simp] theorem pathLabel_nil (root : I) : pathLabel root [] = root := rfl
@[simp] theorem pathLabel_append_singleton (root j : I) (p : List I) :
    pathLabel root (p ++ [j]) = j := by
  induction p generalizing root with
  | nil => rfl
  | cons k p ih => exact ih k
def ProperPaths (root : I) (P : Finset (List I)) : Prop :=
  [] ∈ P ∧ ∀ p j, p ++ [j] ∈ P →
    p ∈ P ∧ j ∈ closedNeighbors G (pathLabel root p)
def attachmentCandidates (root j : I) (P : Finset (List I)) : Finset (List I) :=
  P.filter (fun p => j ∈ closedNeighbors G (pathLabel root p))
noncomputable def attachmentParent (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) : List I :=
  Classical.choose ((attachmentCandidates G root j P).exists_max_image List.length h)
theorem attachmentParent_spec (root j : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) :
    attachmentParent G root j P h ∈ attachmentCandidates G root j P ∧
      ∀ q ∈ attachmentCandidates G root j P,
        q.length ≤ (attachmentParent G root j P h).length :=
  Classical.choose_spec ((attachmentCandidates G root j P).exists_max_image List.length h)
noncomputable def extendWitness (root j : I) (P : Finset (List I)) : Finset (List I) :=
  if h : (attachmentCandidates G root j P).Nonempty then
    insert (attachmentParent G root j P h ++ [j]) P
  else P
theorem subset_extendWitness (root j : I) (P : Finset (List I)) :
    P ⊆ extendWitness G root j P := by
  unfold extendWitness
  split_ifs <;> simp
theorem properPaths_extend (root j : I) (P : Finset (List I))
    (hP : ProperPaths G root P) : ProperPaths G root (extendWitness G root j P) := by
  refine ⟨subset_extendWitness G root j P hP.1, ?_⟩
  intro q k hq
  unfold extendWitness at hq ⊢
  split_ifs at hq ⊢ with h
  · rcases Finset.mem_insert.mp hq with he | hold
    · have hr : k :: q.reverse = j :: (attachmentParent G root j P h).reverse := by
        simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append] using congrArg (fun l : List I => l.reverse) he
      have hk := (List.cons.inj hr).1
      have hp := List.reverse_injective (List.cons.inj hr).2
      subst k
      subst q
      have hs := Finset.mem_filter.mp (attachmentParent_spec G root j P h).1
      exact ⟨Finset.mem_insert_of_mem hs.1, hs.2⟩
    · have hs := hP.2 q k hold
      exact ⟨Finset.mem_insert_of_mem hs.1, hs.2⟩
  · exact hP.2 q k hq
theorem extendWitness_depth (root j : I) (P : Finset (List I)) (d : ℕ)
    (hd : ∀ p ∈ P, p.length ≤ d) :
    ∀ p ∈ extendWitness G root j P, p.length ≤ d + 1 := by
  intro p hp
  unfold extendWitness at hp
  split_ifs at hp with h
  · rcases Finset.mem_insert.mp hp with rfl | hp
    · have hm := (Finset.mem_filter.mp (attachmentParent_spec G root j P h).1).1
      simpa using Nat.add_le_add_right (hd _ hm) 1
    · exact (hd p hp).trans (Nat.le_add_right _ _)
  · exact (hd p hp).trans (Nat.le_add_right _ _)
def labelCount (root k : I) (P : Finset (List I)) : ℕ :=
  (P.filter (fun p => pathLabel root p = k)).card
noncomputable def historyWitness (root : I) : List I → Finset (List I)
  | [] => {[]}
  | j :: rest => extendWitness G root j (historyWitness root rest)
theorem historyWitness_proper (root : I) (L : List I) :
    ProperPaths G root (historyWitness G root L) := by
  induction L with
  | nil =>
    refine ⟨by simp [historyWitness], ?_⟩
    intro p j h
    have he : p ++ [j] = [] := by simpa [historyWitness] using h
    have hn := congrArg List.length he
    simp at hn
  | cons j L ih => exact properPaths_extend G root j _ ih
theorem historyWitness_depth (root : I) (L : List I) :
    ∀ p ∈ historyWitness G root L, p.length ≤ L.length := by
  induction L with
  | nil => intro p hp; simpa [historyWitness] using hp
  | cons j L ih => exact extendWitness_depth G root j _ L.length ih
def childPaths (P : Finset (List I)) (j : I) : Finset (List I) :=
  (P.filter (fun p => p.head? = some j)).image List.tail
@[simp] theorem mem_childPaths (P : Finset (List I)) (j : I) (p : List I) :
    p ∈ childPaths P j ↔ j :: p ∈ P := by
  constructor
  · intro hp
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp
    obtain ⟨hqP, hhead⟩ := Finset.mem_filter.mp hq
    cases q with
    | nil => simp at hhead
    | cons k q =>
      have hk : k = j := by simpa using hhead
      subst k
      have hq : q = p := he
      simpa [hq] using hqP
  · intro hp
    exact Finset.mem_image.mpr ⟨j :: p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩
theorem ProperPaths.child {root j : I} {P : Finset (List I)}
    (hP : ProperPaths G root P) (hj : [j] ∈ P) :
    ProperPaths G j (childPaths P j) := by
  refine ⟨(mem_childPaths P j []).mpr hj, ?_⟩
  intro p k hp
  have hh : (j :: p) ++ [k] ∈ P := by simpa using (mem_childPaths P j _).mp hp
  obtain ⟨hparent, hadj⟩ := hP.2 (j :: p) k hh
  exact ⟨(mem_childPaths P j p).mpr hparent, hadj⟩
theorem childPaths_depth (P : Finset (List I)) (j : I) (h : ℕ)
    (hd : ∀ p ∈ P, p.length < h + 1) :
    ∀ p ∈ childPaths P j, p.length < h := by
  intro p hp
  have hh := hd (j :: p) ((mem_childPaths P j p).mp hp)
  simp only [List.length_cons] at hh
  omega
def pathsToTree : (h : ℕ) → (root : I) → (P : Finset (List I)) →
    ProperPaths G root P → (∀ p ∈ P, p.length < h) → WitnessTree G h root
  | 0, _, P, hP, hd => False.elim (Nat.not_lt_zero _ (hd [] hP.1))
  | h + 1, root, P, hP, hd => fun j =>
      if hj : [j.val] ∈ P then
        some (pathsToTree h j (childPaths P j) (ProperPaths.child G hP hj) (childPaths_depth P j h hd))
      else none
def witnessPaths : (h : ℕ) → (root : I) → WitnessTree G h root → Finset (List I)
  | 0, _, t => PEmpty.elim t
  | h + 1, root, t => insert []
      (Finset.univ.biUnion (fun j : closedNeighbors G root =>
        match t j with
        | none => ∅
        | some child => (witnessPaths h j child).image (List.cons j.val)))
noncomputable def encodedHistoryWitness (root : I) (L : List I) :
    WitnessTree G (L.length + 1) root :=
  pathsToTree G (L.length + 1) root (historyWitness G root L)
    (historyWitness_proper G root L)
    (fun p hp => Nat.lt_succ_of_le (historyWitness_depth G root L p hp))
end QEC.Coding.ProbabilisticConstruction.Resampling


