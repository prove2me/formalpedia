-- Prove2me | Definitions.Def_BuhaiPapers_Background_PolyTime_Lists
-- name    : BuhaiPapers_Background_PolyTime_Lists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:45.392642+00:00
-- url     : https://prove2.me/theorems/678222ce-c4b1-49a2-9343-802452516c64
-- title:
--   Background.PolyTime.Lists — More list operations in polynomial time
-- statement:
--   This is module `Background.PolyTime.Lists`, shared background material of the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0), published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) uses it.
--
--   Certificates, in the compositional form of complexitylib, for list operations that the
--   algorithms of the papers use and that complexitylib does not certify:
--
--   * right folds whose accumulator grows by a bounded amount per element
--     (`Turing.MultiTapeTM.ComputableInPolyTime.foldrWithInput_of_bounded_growth`), by a left fold of
--     the reversed list;
--   * `List.take` with a count in binary (`Turing.MultiTapeTM.ComputableInPolyTime.listTakeBin`);
--   * `List.dedup` (`Turing.MultiTapeTM.ComputableInPolyTime.listDedup`), as a right fold;
--   * `List.takeWhile` and `List.dropWhile` (`Turing.MultiTapeTM.ComputableInPolyTime.listTakeWhile`,
--     `Turing.MultiTapeTM.ComputableInPolyTime.listDropWhile`), cutting at the first failure;
--   * `List.mergeSort` for a total and transitive comparison
--     (`Turing.MultiTapeTM.ComputableInPolyTime.listMergeSort`): it is the stable insertion sort
--     (`List.mergeSort_eq_foldr_insertBy`), a right fold;
--   * `List.filterMap` (`Turing.MultiTapeTM.ComputableInPolyTime.listFilterMap`).
--
--   **Contents.** The module is published as a whole: 17 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BuhaiPapers_Background_PolyTime_Lists`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Background/PolyTime/Lists.lean

module

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Membership
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Dedup

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `Background.PolyTime.Lists` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# More list operations in polynomial time

Certificates, in the compositional form of complexitylib, for list operations that the
algorithms of the papers use and that complexitylib does not certify:

* right folds whose accumulator grows by a bounded amount per element
  (`Turing.MultiTapeTM.ComputableInPolyTime.foldrWithInput_of_bounded_growth`), by a left fold of
  the reversed list;
* `List.take` with a count in binary (`Turing.MultiTapeTM.ComputableInPolyTime.listTakeBin`);
* `List.dedup` (`Turing.MultiTapeTM.ComputableInPolyTime.listDedup`), as a right fold;
* `List.takeWhile` and `List.dropWhile` (`Turing.MultiTapeTM.ComputableInPolyTime.listTakeWhile`,
  `Turing.MultiTapeTM.ComputableInPolyTime.listDropWhile`), cutting at the first failure;
* `List.mergeSort` for a total and transitive comparison
  (`Turing.MultiTapeTM.ComputableInPolyTime.listMergeSort`): it is the stable insertion sort
  (`List.mergeSort_eq_foldr_insertBy`), a right fold;
* `List.filterMap` (`Turing.MultiTapeTM.ComputableInPolyTime.listFilterMap`).
-/

@[expose] public section

namespace List

variable {α : Type}

/-- Insert `a` before the first element `b` with `le a b`. -/
def insertBy (le : α → α → Bool) (a : α) (l : List α) : List α :=
  l.takeWhile (fun b ↦ !le a b) ++ a :: l.dropWhile (fun b ↦ !le a b)

theorem perm_insertBy (le : α → α → Bool) (a : α) (l : List α) :
    (insertBy le a l).Perm (a :: l) := by
  unfold insertBy
  have h := List.takeWhile_append_dropWhile (p := fun b ↦ !le a b) (l := l)
  calc _ ~ a :: (l.takeWhile (fun b ↦ !le a b) ++ l.dropWhile (fun b ↦ !le a b)) :=
        List.perm_middle
    _ = a :: l := by rw [h]

/-- **`mergeSort` is the stable insertion sort.** -/
theorem mergeSort_eq_foldr_insertBy {le : α → α → Bool}
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (l : List α) : l.mergeSort le = l.foldr (insertBy le) [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨l₁, l₂, h₁, h₂, h₃⟩ := List.mergeSort_cons trans total a l
    rw [List.foldr_cons, ← ih, h₂, h₁]
    have hs := List.pairwise_mergeSort trans total (a :: l)
    rw [h₁, List.pairwise_append, List.pairwise_cons] at hs
    have hl₂ : ∀ b ∈ l₂, le a b := hs.2.1.1
    unfold insertBy
    have ht : (l₁ ++ l₂).takeWhile (fun b ↦ !le a b) = l₁ := by
      rw [List.takeWhile_append_of_pos (fun b hb ↦ by simpa using h₃ b hb)]
      cases l₂ with
      | nil => simp
      | cons b l₂ => simp [hl₂ b List.mem_cons_self]
    have hd : (l₁ ++ l₂).dropWhile (fun b ↦ !le a b) = l₂ := by
      rw [List.dropWhile_append_of_pos (fun b hb ↦ by simpa using h₃ b hb)]
      cases l₂ with
      | nil => simp
      | cons b l₂ => simp [hl₂ b List.mem_cons_self]
    rw [ht, hd]

/-- The prefix kept by `takeWhile` ends at the first failure. -/
theorem takeWhile_eq_take_idxOf (p : α → Bool) (l : List α) :
    l.takeWhile p = l.take ((l.map p).idxOf false) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : p a
    · simp [h]
    · simp [h, ih]

theorem dropWhile_eq_drop_idxOf (p : α → Bool) (l : List α) :
    l.dropWhile p = l.drop ((l.map p).idxOf false) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : p a
    · simp [h]
    · simp [h, ih]

theorem dedup_eq_foldr [DecidableEq α] (l : List α) :
    l.dedup = l.foldr (fun a acc ↦ if a ∈ acc then acc else a :: acc) [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ← ih]
    by_cases h : a ∈ l
    · rw [List.dedup_cons_of_mem h, if_pos (List.mem_dedup.2 h)]
    · rw [List.dedup_cons_of_notMem h, if_neg (fun h' ↦ h (List.mem_dedup.1 h'))]

theorem filterMap_eq_map_filter {β : Type} (f : α → Option β) (d : β) (l : List α) :
    l.filterMap f = ((l.map f).filter Option.isSome).map fun o ↦ o.getD d := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : f a <;> simp [h, ih]

end List

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {γ α β : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- **A right fold with bounded growth**, as a left fold of the reversed list. -/
theorem foldrWithInput_of_bounded_growth {list : γ → List α} {init : γ → β}
    {step : γ → α → β → β} (hlist : ComputableInPolyTime list encIn (encList encA))
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun p : (γ × β) × α ↦ step p.1.1 p.2 p.1.2)
      (encPair (encPair encIn encB) encA) encB)
    {growth : γ → ℕ} (hpoly : PolyBounded (fun x ↦ (encIn x).length) growth)
    (hgrowth : ∀ x state value, value ∈ list x →
      (encB (step x value state)).length ≤ (encB state).length + growth x) :
    ComputableInPolyTime (fun x ↦ (list x).foldr (step x) (init x)) encIn encB := by
  simp only [List.foldr_eq_foldl_reverse]
  exact foldlWith_of_bounded_growth (par := fun x ↦ x) (list := fun x ↦ (list x).reverse)
    (step := fun x state value ↦ step x value state) id' (listReverseWithInput hlist) hinit hstep
    hpoly fun x state value hv ↦ hgrowth x state value (List.mem_reverse.1 hv)

/-- `List.take` with a count in binary: at most the length of the list is taken. -/
theorem listTakeBin {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encNat) :
    ComputableInPolyTime (fun x ↦ (list x).take (count x)) encIn (encList encA) := by
  have hmin : ComputableInPolyTime (fun x ↦ min (list x).length (count x)) encIn encUnary :=
    binary_min_unary' ((length_list encA).comp hlist) hcount
  have h : ComputableInPolyTime (fun x ↦ (list x).take (min (list x).length (count x))) encIn
      (encList encA) := .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hlist.tidy hmin.tidy)
  refine h.of_enc_eq fun x ↦ ?_
  congr 1
  rcases le_total (list x).length (count x) with hc | hc
  · rw [min_eq_left hc, List.take_of_length_le hc, List.take_of_length_le le_rfl]
  · rw [min_eq_right hc]

/-- `List.drop` with a count in binary. -/
theorem listDropBin {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encNat) :
    ComputableInPolyTime (fun x ↦ (list x).drop (count x)) encIn (encList encA) := by
  have hmin : ComputableInPolyTime (fun x ↦ min (list x).length (count x)) encIn encUnary :=
    binary_min_unary' ((length_list encA).comp hlist) hcount
  have h : ComputableInPolyTime (fun x ↦ (list x).drop (min (list x).length (count x))) encIn
      (encList encA) := .of_tidy (ComputableTidilyInPolyTime.listDropWithInput hlist.tidy hmin.tidy)
  refine h.of_enc_eq fun x ↦ ?_
  congr 1
  rcases le_total (list x).length (count x) with hc | hc
  · rw [min_eq_left hc, List.drop_of_length_le hc, List.drop_of_length_le le_rfl]
  · rw [min_eq_right hc]

/-- **`List.dedup`**: keep the last copy of each element. -/
theorem listDedup [DecidableEq α] {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x ↦ (list x).dedup) encIn (encList encA) := by
  simp only [List.dedup_eq_foldr]
  refine foldrWithInput_of_bounded_growth (step := fun _ a acc ↦ if a ∈ acc then acc else a :: acc)
    hlist (const []) ?_ (growth := fun x ↦ 2 * (encList encA (list x)).length + 1)
    (((PolyBounded.const 2).mul hlist.polyBounded_length).add (.const 1)) ?_
  · exact ite_decide (decide_mem ((snd _ _).comp (fst _ _)) (snd _ _))
      ((snd _ _).comp (fst _ _)) (cons' (snd _ _) ((snd _ _).comp (fst _ _)))
  · intro x state value hv
    have h := SizedListEncoding.length_elem_le (encA := encA) (encL := encList encA) _ _ hv
    split_ifs
    · omega
    · simp only [encList_cons, List.length_append, length_frame]
      omega

/-- `List.takeWhile`, for a test with the input. -/
theorem listTakeWhile {list : γ → List α} {test : γ → α → Bool}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α ↦ test p.1 p.2) (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x ↦ (list x).takeWhile (test x)) encIn (encList encA) := by
  simp only [List.takeWhile_eq_take_idxOf]
  exact .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hlist.tidy
    (idxOfWithInput (mapWithInput hlist htest) (const false)).tidy)

/-- `List.dropWhile`, for a test with the input. -/
theorem listDropWhile {list : γ → List α} {test : γ → α → Bool}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α ↦ test p.1 p.2) (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x ↦ (list x).dropWhile (test x)) encIn (encList encA) := by
  simp only [List.dropWhile_eq_drop_idxOf]
  exact .of_tidy (ComputableTidilyInPolyTime.listDropWithInput hlist.tidy
    (idxOfWithInput (mapWithInput hlist htest) (const false)).tidy)

/-- Inserting an element before the first one it is at most. -/
theorem listInsertBy {list : γ → List α} {a : γ → α} {le : γ → α → α → Bool}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (ha : ComputableInPolyTime a encIn encA)
    (hle : ComputableInPolyTime (fun p : γ × α × α ↦ le p.1 p.2.1 p.2.2)
      (encPair encIn (encPair encA encA)) encBool) :
    ComputableInPolyTime (fun x ↦ (list x).insertBy (le x) (a x)) encIn (encList encA) := by
  unfold List.insertBy
  have htest : ComputableInPolyTime (fun p : γ × α ↦ !le p.1 (a p.1) p.2) (encPair encIn encA)
      encBool :=
    bool_not.comp (hle.comp (g := fun p : γ × α ↦ (p.1, a p.1, p.2))
      ((fst _ _).prod ((ha.comp (fst _ _)).prod (snd _ _))))
  exact listAppend' (listTakeWhile (test := fun x b ↦ !le x (a x) b) hlist htest)
    (cons' ha (listDropWhile (test := fun x b ↦ !le x (a x) b) hlist htest))

theorem length_encList_perm {l l' : List α} (h : l.Perm l') :
    (encList encA l).length = (encList encA l').length := by
  rw [length_encList, length_encList]
  exact (h.map _).sum_eq

/-- **`List.mergeSort`** for a total and transitive comparison with the input. -/
theorem listMergeSort {list : γ → List α} {le : γ → α → α → Bool}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hle : ComputableInPolyTime (fun p : γ × α × α ↦ le p.1 p.2.1 p.2.2)
      (encPair encIn (encPair encA encA)) encBool)
    (trans : ∀ x a b c, le x a b → le x b c → le x a c)
    (total : ∀ x a b, le x a b || le x b a) :
    ComputableInPolyTime (fun x ↦ (list x).mergeSort (le x)) encIn (encList encA) := by
  simp only [List.mergeSort_eq_foldr_insertBy (trans _) (total _)]
  refine foldrWithInput_of_bounded_growth (step := fun x a acc ↦ acc.insertBy (le x) a)
    hlist (const []) ?_ (growth := fun x ↦ 2 * (encList encA (list x)).length + 1)
    (((PolyBounded.const 2).mul hlist.polyBounded_length).add (.const 1)) ?_
  · have hle' : ComputableInPolyTime (fun q : ((γ × List α) × α) × α × α ↦
        le q.1.1.1 q.2.1 q.2.2)
        (encPair (encPair (encPair encIn (encList encA)) encA) (encPair encA encA)) encBool :=
      hle.comp (g := fun q : ((γ × List α) × α) × α × α ↦ (q.1.1.1, q.2.1, q.2.2))
        (((fst _ _).comp ((fst _ _).comp (fst _ _))).prod
          (((fst _ _).comp (snd _ _)).prod ((snd _ _).comp (snd _ _))))
    exact listInsertBy (list := fun p : (γ × List α) × α ↦ p.1.2) (a := fun p ↦ p.2)
      (le := fun p ↦ le p.1.1) ((snd _ _).comp (fst _ _)) (snd _ _) hle'
  · intro x state value hv
    have h := SizedListEncoding.length_elem_le (encA := encA) (encL := encList encA) _ _ hv
    rw [length_encList_perm (List.perm_insertBy _ _ _)]
    simp only [encList_cons, List.length_append, length_frame]
    omega

/-- **`List.filterMap`**, for a function with the input. -/
theorem listFilterMap {list : γ → List α} {f : γ → α → Option β} (d : β)
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hf : ComputableInPolyTime (fun p : γ × α ↦ f p.1 p.2) (encPair encIn encA)
      (encOption encB)) :
    ComputableInPolyTime (fun x ↦ (list x).filterMap (f x)) encIn (encList encB) := by
  simp only [List.filterMap_eq_map_filter _ d]
  have hm := mapWithInput hlist hf
  have hfl := filterWithInput (test := fun _ (o : Option β) ↦ o.isSome) hm
    (optionIsSome (snd _ _))
  exact mapWithInput (f := fun _ (o : Option β) ↦ o.getD d) hfl
    ((optionGetD encB).comp ((snd _ _).prod (const d)))

end Turing.MultiTapeTM.ComputableInPolyTime


