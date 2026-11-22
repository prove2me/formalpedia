-- Prove2me | solution 1 for AllocationIndices.Precedence.fi_policy_is_fi_star_policy
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:43:33.734629+00:00
-- url     : https://prove2.me/submissions/654b1a44-624b-42d2-97f9-bbef3a3d72ff

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

namespace AllocationIndices.Precedence

open scoped BigOperators

/-! ### Section 1: Combinatorial DAG and Dynamic Program -/

section Combinatorial

variable {n : ℕ} (prec : Fin n → Fin n → Prop) (hacyc : ∀ i, ¬ Relation.TransGen prec i i)

open Classical in
/-- Available jobs given completed set `D`. -/
noncomputable def availSet (D : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => j ∉ D ∧ ∀ i, prec i j → i ∈ D

lemma mem_availSet {D : Finset (Fin n)} {j : Fin n} :
    j ∈ availSet prec D ↔ j ∉ D ∧ ∀ i, prec i j → i ∈ D := by
  classical
  simp [availSet]

lemma availSet_nonempty (hacyc : ∀ i, ¬ Relation.TransGen prec i i)
    {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    (availSet prec D).Nonempty := by
  have : IsTrans (Fin n) (Relation.TransGen prec) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen prec) := ⟨hacyc⟩
  have hwf : WellFounded (Relation.TransGen prec) :=
    Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen prec)
  have hS : Set.Nonempty {j : Fin n | j ∉ D} := by
    by_contra h
    apply hD
    ext j
    simp only [Finset.mem_univ, iff_true]
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨j, hj, hmin⟩ := hwf.has_min {j : Fin n | j ∉ D} hS
  refine ⟨j, (mem_availSet prec).2 ⟨hj, fun i hij => ?_⟩⟩
  by_contra hi
  exact hmin i hi (Relation.TransGen.single hij)

lemma card_sub_insert_lt {D : Finset (Fin n)} {j : Fin n} (hj : j ∉ D) :
    n - (insert j D).card < n - D.card := by
  have hcard : D.card < n := by
    have hlt : D.card < (Finset.univ : Finset (Fin n)).card :=
      Finset.card_lt_card (Finset.ssubset_univ_iff.2 fun h => hj (h ▸ Finset.mem_univ j))
    simpa using hlt
  rw [Finset.card_insert_of_notMem hj]
  omega

/-- Optimal value over all full topological orderings of `Dᶜ`. -/
noncomputable def dpU (r φ : Fin n → ℝ) (D : Finset (Fin n)) : ℝ :=
  if hD : D = Finset.univ then 0
  else
    ((availSet prec D).attach).sup' ((availSet_nonempty prec hacyc hD).attach) fun ⟨j, hj⟩ =>
      have : n - (insert j D).card < n - D.card :=
        card_sub_insert_lt ((mem_availSet prec).1 hj).1
      r j + φ j * dpU r φ (insert j D)
termination_by n - D.card

/-- Optimal value over all valid prefixes (possibly empty) of `Dᶜ`. -/
noncomputable def dpG (r φ : Fin n → ℝ) (D : Finset (Fin n)) : ℝ :=
  if hD : D = Finset.univ then 0
  else
    max 0 (((availSet prec D).attach).sup' ((availSet_nonempty prec hacyc hD).attach) fun ⟨j, hj⟩ =>
      have : n - (insert j D).card < n - D.card :=
        card_sub_insert_lt ((mem_availSet prec).1 hj).1
      r j + φ j * dpG r φ (insert j D))
termination_by n - D.card

/-- Optimal value over all nonempty valid prefixes of `Dᶜ` (0 if `D = univ`). -/
noncomputable def dpH (r φ : Fin n → ℝ) (D : Finset (Fin n)) : ℝ :=
  if hD : D = Finset.univ then 0
  else
    (availSet prec D).sup' (availSet_nonempty prec hacyc hD) fun j =>
      r j + φ j * dpG prec hacyc r φ (insert j D)

lemma dpU_univ (r φ : Fin n → ℝ) : dpU prec hacyc r φ Finset.univ = 0 := by
  rw [dpU]
  simp

lemma dpU_eq_sup' (r φ : Fin n → ℝ) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    dpU prec hacyc r φ D =
      (availSet prec D).sup' (availSet_nonempty prec hacyc hD)
        (fun j => r j + φ j * dpU prec hacyc r φ (insert j D)) := by
  rw [dpU, dif_neg hD]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun ⟨j, hj⟩ _ => ?_
    exact Finset.le_sup' (fun j => r j + φ j * dpU prec hacyc r φ (insert j D)) hj
  · refine Finset.sup'_le _ _ fun j hj => ?_
    exact Finset.le_sup'
      (fun x : {x // x ∈ availSet prec D} => r x.1 + φ x.1 * dpU prec hacyc r φ (insert x.1 D))
      (Finset.mem_attach _ ⟨j, hj⟩)

lemma dpG_univ (r φ : Fin n → ℝ) : dpG prec hacyc r φ Finset.univ = 0 := by
  rw [dpG]
  simp

lemma dpH_univ (r φ : Fin n → ℝ) : dpH prec hacyc r φ Finset.univ = 0 := by
  rw [dpH]
  simp

lemma dpH_eq_sup' (r φ : Fin n → ℝ) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    dpH prec hacyc r φ D =
      (availSet prec D).sup' (availSet_nonempty prec hacyc hD)
        (fun j => r j + φ j * dpG prec hacyc r φ (insert j D)) := by
  rw [dpH, dif_neg hD]

lemma dpG_eq_max (r φ : Fin n → ℝ) (D : Finset (Fin n)) :
    dpG prec hacyc r φ D = max 0 (dpH prec hacyc r φ D) := by
  by_cases hD : D = Finset.univ
  · subst hD
    simp [dpG_univ, dpH_univ]
  · rw [dpG, dif_neg hD, dpH_eq_sup' prec hacyc r φ hD]
    congr 1
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun ⟨j, hj⟩ _ => ?_
      exact Finset.le_sup' (fun j => r j + φ j * dpG prec hacyc r φ (insert j D)) hj
    · refine Finset.sup'_le _ _ fun j hj => ?_
      exact Finset.le_sup'
        (fun x : {x // x ∈ availSet prec D} => r x.1 + φ x.1 * dpG prec hacyc r φ (insert x.1 D))
        (Finset.mem_attach _ ⟨j, hj⟩)

lemma dpG_nonneg (r φ : Fin n → ℝ) (D : Finset (Fin n)) :
    0 ≤ dpG prec hacyc r φ D := by
  rw [dpG_eq_max]
  exact le_max_left _ _

lemma dpH_le_dpG (r φ : Fin n → ℝ) (D : Finset (Fin n)) :
    dpH prec hacyc r φ D ≤ dpG prec hacyc r φ D := by
  rw [dpG_eq_max]
  exact le_max_right _ _

lemma le_dpU (r φ : Fin n → ℝ) {D : Finset (Fin n)} {j : Fin n} (hj : j ∈ availSet prec D) :
    r j + φ j * dpU prec hacyc r φ (insert j D) ≤ dpU prec hacyc r φ D := by
  have hD : D ≠ Finset.univ := fun h => ((mem_availSet prec).1 hj).1 (h ▸ Finset.mem_univ j)
  rw [dpU_eq_sup' prec hacyc r φ hD]
  exact Finset.le_sup' (fun j => r j + φ j * dpU prec hacyc r φ (insert j D)) hj

lemma le_dpH (r φ : Fin n → ℝ) {D : Finset (Fin n)} {j : Fin n} (hj : j ∈ availSet prec D) :
    r j + φ j * dpG prec hacyc r φ (insert j D) ≤ dpH prec hacyc r φ D := by
  have hD : D ≠ Finset.univ := fun h => ((mem_availSet prec).1 hj).1 (h ▸ Finset.mem_univ j)
  rw [dpH_eq_sup' prec hacyc r φ hD]
  exact Finset.le_sup' (fun j => r j + φ j * dpG prec hacyc r φ (insert j D)) hj

lemma le_dpG (r φ : Fin n → ℝ) {D : Finset (Fin n)} {j : Fin n} (hj : j ∈ availSet prec D) :
    r j + φ j * dpG prec hacyc r φ (insert j D) ≤ dpG prec hacyc r φ D :=
  (le_dpH prec hacyc r φ hj).trans (dpH_le_dpG prec hacyc r φ D)

lemma exists_dpU_maximizer (r φ : Fin n → ℝ) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    ∃ j ∈ availSet prec D, r j + φ j * dpU prec hacyc r φ (insert j D) = dpU prec hacyc r φ D := by
  rw [dpU_eq_sup' prec hacyc r φ hD]
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' (availSet_nonempty prec hacyc hD)
    (fun j => r j + φ j * dpU prec hacyc r φ (insert j D))
  exact ⟨j, hj, heq.symm⟩

lemma exists_dpH_maximizer (r φ : Fin n → ℝ) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    ∃ j ∈ availSet prec D, r j + φ j * dpG prec hacyc r φ (insert j D) = dpH prec hacyc r φ D := by
  rw [dpH_eq_sup' prec hacyc r φ hD]
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' (availSet_nonempty prec hacyc hD)
    (fun j => r j + φ j * dpG prec hacyc r φ (insert j D))
  exact ⟨j, hj, heq.symm⟩

/-- Valid prefix of a topological ordering of `Dᶜ`. -/
def ValidPrefix : Finset (Fin n) → List (Fin n) → Prop
  | _, [] => True
  | D, j :: w => j ∈ availSet prec D ∧ ValidPrefix (insert j D) w

/-- Valid full topological ordering of `Dᶜ`. -/
def ValidFull (D : Finset (Fin n)) (w : List (Fin n)) : Prop :=
  ValidPrefix prec D w ∧ D ∪ w.toFinset = Finset.univ

def listDisc (φ : Fin n → ℝ) : List (Fin n) → ℝ
  | [] => 1
  | j :: w => φ j * listDisc φ w

def listVal (r φ : Fin n → ℝ) : List (Fin n) → ℝ
  | [] => 0
  | j :: w => r j + φ j * listVal r φ w

def listValIn (W : Finset (Fin n)) (r φ : Fin n → ℝ) : List (Fin n) → ℝ
  | [] => 0
  | x :: xs => (if x ∈ W then r x else 0) + φ x * listValIn W r φ xs

def listValOut (W : Finset (Fin n)) (r φ : Fin n → ℝ) : List (Fin n) → ℝ
  | [] => 0
  | x :: xs => (if x ∉ W then r x else 0) + φ x * listValOut W r φ xs

lemma listVal_eq_add (W : Finset (Fin n)) (r φ : Fin n → ℝ) (w : List (Fin n)) :
    listVal r φ w = listValIn W r φ w + listValOut W r φ w := by
  induction w with
  | nil => simp [listVal, listValIn, listValOut]
  | cons x xs ih =>
    simp only [listVal, listValIn, listValOut, ih]
    by_cases hx : x ∈ W <;> simp [hx] <;> ring

lemma listDisc_pos {φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) (w : List (Fin n)) :
    0 < listDisc φ w := by
  induction w with
  | nil => simp [listDisc]
  | cons x xs ih => exact mul_pos (hφ₀ x) ih

lemma listDisc_le_one {φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) (hφ₁ : ∀ i, φ i < 1)
    (w : List (Fin n)) : listDisc φ w ≤ 1 := by
  induction w with
  | nil => simp [listDisc]
  | cons x xs ih =>
    simpa [listDisc] using mul_le_one₀ (hφ₁ x).le (listDisc_pos hφ₀ xs).le ih

lemma listDisc_lt_one_of_ne_nil {φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) (hφ₁ : ∀ i, φ i < 1)
    {w : List (Fin n)} (hw : w ≠ []) : listDisc φ w < 1 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons x xs =>
    calc φ x * listDisc φ xs ≤ φ x * 1 :=
          mul_le_mul_of_nonneg_left (listDisc_le_one hφ₀ hφ₁ xs) (hφ₀ x).le
      _ = φ x := mul_one _
      _ < 1 := hφ₁ x

lemma listDisc_append (φ : Fin n → ℝ) (w₁ w₂ : List (Fin n)) :
    listDisc φ (w₁ ++ w₂) = listDisc φ w₁ * listDisc φ w₂ := by
  induction w₁ with
  | nil => simp [listDisc]
  | cons x xs ih => simp [listDisc, ih, mul_assoc]

lemma listVal_append (r φ : Fin n → ℝ) (w₁ w₂ : List (Fin n)) :
    listVal r φ (w₁ ++ w₂) = listVal r φ w₁ + listDisc φ w₁ * listVal r φ w₂ := by
  induction w₁ with
  | nil => simp [listVal, listDisc]
  | cons x xs ih =>
    simp only [List.cons_append, listVal, listDisc, ih]
    ring

lemma listDisc_eq_prod_toFinset (φ : Fin n → ℝ) {w : List (Fin n)} (hnd : w.Nodup) :
    listDisc φ w = ∏ x ∈ w.toFinset, φ x := by
  induction w with
  | nil => simp [listDisc]
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [listDisc, List.toFinset_cons]
    rw [Finset.prod_insert (by simpa using hnd.1), ih hnd.2]

lemma ValidPrefix.disjoint {D : Finset (Fin n)} {w : List (Fin n)}
    (hw : ValidPrefix prec D w) : Disjoint D w.toFinset := by
  induction w generalizing D with
  | nil => simp
  | cons x xs ih =>
    rcases hw with ⟨hx, hxs⟩
    have hxD : x ∉ D := ((mem_availSet prec).1 hx).1
    have hdisj := ih hxs
    rw [Finset.disjoint_left] at hdisj ⊢
    intro a haD haMem
    simp only [List.toFinset_cons, Finset.mem_insert] at haMem
    rcases haMem with rfl | haxs
    · exact hxD haD
    · exact hdisj (Finset.mem_insert_of_mem haD) haxs

lemma ValidPrefix.nodup {D : Finset (Fin n)} {w : List (Fin n)}
    (hw : ValidPrefix prec D w) : w.Nodup := by
  induction w generalizing D with
  | nil => simp
  | cons x xs ih =>
    rcases hw with ⟨_, hxs⟩
    rw [List.nodup_cons]
    refine ⟨?_, ih hxs⟩
    intro hmem
    exact (Finset.disjoint_left.1 hxs.disjoint) (Finset.mem_insert_self x D)
      (List.mem_toFinset.2 hmem)

lemma ValidPrefix.append_iff {D : Finset (Fin n)} {w₁ w₂ : List (Fin n)} :
    ValidPrefix prec D (w₁ ++ w₂) ↔
      ValidPrefix prec D w₁ ∧ ValidPrefix prec (D ∪ w₁.toFinset) w₂ := by
  induction w₁ generalizing D with
  | nil => simp [ValidPrefix]
  | cons x xs ih =>
    simp only [List.cons_append, ValidPrefix, List.toFinset_cons]
    have hset : insert x D ∪ xs.toFinset = D ∪ insert x xs.toFinset := by
      ext a; simp
    rw [ih, hset, and_assoc]

lemma ValidPrefix.downwardClosed {D : Finset (Fin n)} {w : List (Fin n)}
    (hw : ValidPrefix prec D w) :
    ∀ x ∈ w.toFinset, ∀ y, prec y x → y ∈ D ∪ w.toFinset := by
  induction w generalizing D with
  | nil => simp
  | cons a as ih =>
    rcases hw with ⟨ha, has⟩
    intro x hx y hyx
    simp only [List.toFinset_cons, Finset.mem_insert] at hx ⊢
    have hset : insert a D ∪ as.toFinset = D ∪ insert a as.toFinset := by
      ext z; simp
    rcases hx with rfl | hxa
    · exact Finset.mem_union_left _ (((mem_availSet prec).1 ha).2 y hyx)
    · rw [← hset]
      exact ih has x hxa y hyx

lemma ValidPrefix.filter_not_mem {D : Finset (Fin n)} (W : Finset (Fin n)) {π : List (Fin n)}
    (hπ : ValidPrefix prec D π) :
    ValidPrefix prec (D ∪ W) (π.filter (· ∉ W)) := by
  induction π generalizing D with
  | nil => simp [ValidPrefix]
  | cons x xs ih =>
    rcases hπ with ⟨hx, hxs⟩
    have hx' := (mem_availSet prec).1 hx
    by_cases hxW : x ∈ W
    · simp only [List.filter_cons, hxW, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      have heq : insert x D ∪ W = D ∪ W := by
        ext a; simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ((rfl | h) | h)
          · exact Or.inr hxW
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
      rw [← heq]
      exact ih hxs
    · simp only [List.filter_cons, hxW, not_false_eq_true, decide_true, ↓reduceIte,
        ValidPrefix]
      refine ⟨(mem_availSet prec).2 ⟨?_, fun i hi => Finset.mem_union_left _ (hx'.2 i hi)⟩, ?_⟩
      · simp [hx'.1, hxW]
      · rw [← Finset.insert_union]
        exact ih hxs

lemma ValidPrefix.filter_mem_aux {D B W : Finset (Fin n)} {π : List (Fin n)}
    (hπ : ValidPrefix prec (D ∪ B) π)
    (hBW : Disjoint B W)
    (hW : ∀ x ∈ W, ∀ y, prec y x → y ∈ D ∪ W) :
    ValidPrefix prec D (π.filter (· ∈ W)) := by
  induction π generalizing D B with
  | nil => simp [ValidPrefix]
  | cons x xs ih =>
    rcases hπ with ⟨hx, hxs⟩
    have hx' := (mem_availSet prec).1 hx
    by_cases hxW : x ∈ W
    · simp only [List.filter_cons, hxW, decide_true, ↓reduceIte, ValidPrefix]
      refine ⟨(mem_availSet prec).2 ⟨fun h => hx'.1 (Finset.mem_union_left _ h), fun y hyx => ?_⟩,
        ?_⟩
      · have hy1 := hx'.2 y hyx
        have hy2 := hW x hxW y hyx
        simp only [Finset.mem_union] at hy1 hy2
        rcases hy1 with h | h
        · exact h
        · rcases hy2 with h2 | h2
          · exact h2
          · exact absurd h2 (Finset.disjoint_left.1 hBW h)
      · rw [← Finset.insert_union] at hxs
        exact ih hxs hBW fun z hz y hyz =>
          Finset.mem_union.2 <| (Finset.mem_union.1 (hW z hz y hyz)).imp
            (Finset.mem_insert_of_mem) id
    · simp only [List.filter_cons, hxW, decide_false, Bool.false_eq_true, ↓reduceIte]
      have heq : insert x (D ∪ B) = D ∪ insert x B := by
        ext a; simp
      rw [heq] at hxs
      exact ih hxs (Finset.disjoint_insert_left.2 ⟨hxW, hBW⟩) hW

lemma ValidPrefix.filter_mem {D W : Finset (Fin n)} {π : List (Fin n)}
    (hπ : ValidPrefix prec D π)
    (hW : ∀ x ∈ W, ∀ y, prec y x → y ∈ D ∪ W) :
    ValidPrefix prec D (π.filter (· ∈ W)) :=
  ValidPrefix.filter_mem_aux prec (by simpa using hπ) (Finset.disjoint_empty_left W) hW

lemma listVal_le_dpU {r φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) {D : Finset (Fin n)} {w : List (Fin n)}
    (hw : ValidFull prec D w) : listVal r φ w ≤ dpU prec hacyc r φ D := by
  induction w generalizing D with
  | nil =>
    have hD : D = Finset.univ := by simpa [ValidFull] using hw.2
    subst hD
    simp [listVal, dpU_univ]
  | cons x xs ih =>
    rcases hw with ⟨⟨hx, hxs⟩, huniv⟩
    have huniv' : insert x D ∪ xs.toFinset = Finset.univ := by
      simpa [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using huniv
    have hle := ih ⟨hxs, huniv'⟩
    calc listVal r φ (x :: xs) = r x + φ x * listVal r φ xs := rfl
      _ ≤ r x + φ x * dpU prec hacyc r φ (insert x D) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hle (hφ₀ x).le)
      _ ≤ dpU prec hacyc r φ D := le_dpU prec hacyc r φ hx

lemma exists_validFull_eq_dpU (r φ : Fin n → ℝ) (D : Finset (Fin n)) :
    ∃ w : List (Fin n), ValidFull prec D w ∧ listVal r φ w = dpU prec hacyc r φ D := by
  by_cases hD : D = Finset.univ
  · subst hD
    exact ⟨[], ⟨trivial, by simp⟩, by simp [listVal, dpU_univ]⟩
  · obtain ⟨j, hj, hopt⟩ := exists_dpU_maximizer prec hacyc r φ hD
    have : n - (insert j D).card < n - D.card :=
      card_sub_insert_lt ((mem_availSet prec).1 hj).1
    obtain ⟨w, ⟨hw, huniv⟩, hval⟩ := exists_validFull_eq_dpU r φ (insert j D)
    refine ⟨j :: w, ⟨⟨hj, hw⟩, ?_⟩, ?_⟩
    · simpa [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using huniv
    · simp [listVal, hval, hopt]
termination_by n - D.card

lemma exists_validFull_head_eq_dpU (r φ : Fin n → ℝ) {D : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ availSet prec D)
    (hopt : r j + φ j * dpU prec hacyc r φ (insert j D) = dpU prec hacyc r φ D) :
    ∃ w : List (Fin n), ValidFull prec D (j :: w) ∧ listVal r φ (j :: w) = dpU prec hacyc r φ D := by
  obtain ⟨w, ⟨hw, huniv⟩, hval⟩ := exists_validFull_eq_dpU prec hacyc r φ (insert j D)
  refine ⟨w, ⟨⟨hj, hw⟩, ?_⟩, ?_⟩
  · simpa [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using huniv
  · simp [listVal, hval, hopt]

lemma listVal_le_dpG {r φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) {D : Finset (Fin n)} {w : List (Fin n)}
    (hw : ValidPrefix prec D w) : listVal r φ w ≤ dpG prec hacyc r φ D := by
  induction w generalizing D with
  | nil =>
    simp [listVal, dpG_nonneg]
  | cons x xs ih =>
    rcases hw with ⟨hx, hxs⟩
    calc listVal r φ (x :: xs) = r x + φ x * listVal r φ xs := rfl
      _ ≤ r x + φ x * dpG prec hacyc r φ (insert x D) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih hxs) (hφ₀ x).le)
      _ ≤ dpG prec hacyc r φ D := le_dpG prec hacyc r φ hx

lemma exists_validPrefix_eq_dpG (r φ : Fin n → ℝ) (D : Finset (Fin n)) :
    ∃ w : List (Fin n), ValidPrefix prec D w ∧ listVal r φ w = dpG prec hacyc r φ D := by
  by_cases hD : D = Finset.univ
  · subst hD
    exact ⟨[], trivial, by simp [listVal, dpG_univ]⟩
  · rw [dpG_eq_max]
    by_cases hpos : dpH prec hacyc r φ D ≤ 0
    · refine ⟨[], trivial, ?_⟩
      simp [listVal, max_eq_left hpos]
    · push Not at hpos
      obtain ⟨j, hj, hopt⟩ := exists_dpH_maximizer prec hacyc r φ hD
      have : n - (insert j D).card < n - D.card :=
        card_sub_insert_lt ((mem_availSet prec).1 hj).1
      obtain ⟨w, hw, hval⟩ := exists_validPrefix_eq_dpG r φ (insert j D)
      refine ⟨j :: w, ⟨hj, hw⟩, ?_⟩
      rw [max_eq_right hpos.le]
      simp [listVal, hval, hopt]
termination_by n - D.card

lemma exists_validPrefix_ne_nil_eq_dpH (r φ : Fin n → ℝ) {D : Finset (Fin n)}
    (hD : D ≠ Finset.univ) :
    ∃ w : List (Fin n), ValidPrefix prec D w ∧ w ≠ [] ∧ listVal r φ w = dpH prec hacyc r φ D := by
  obtain ⟨j, hj, hopt⟩ := exists_dpH_maximizer prec hacyc r φ hD
  obtain ⟨w, hw, hval⟩ := exists_validPrefix_eq_dpG prec hacyc r φ (insert j D)
  exact ⟨j :: w, ⟨hj, hw⟩, List.cons_ne_nil _ _, by simp [listVal, hval, hopt]⟩

lemma dpG_union_eq_zero_of_eq_dpG {r φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i)
    {D : Finset (Fin n)} {w : List (Fin n)}
    (hw : ValidPrefix prec D w) (heq : listVal r φ w = dpG prec hacyc r φ D) :
    dpG prec hacyc r φ (D ∪ w.toFinset) = 0 := by
  apply le_antisymm _ (dpG_nonneg prec hacyc r φ _)
  obtain ⟨w', hw', hval'⟩ := exists_validPrefix_eq_dpG prec hacyc r φ (D ∪ w.toFinset)
  have hww' : ValidPrefix prec D (w ++ w') := (ValidPrefix.append_iff prec).2 ⟨hw, hw'⟩
  have hle : listVal r φ (w ++ w') ≤ dpG prec hacyc r φ D :=
    listVal_le_dpG prec hacyc hφ₀ hww'
  rw [listVal_append, heq, hval'] at hle
  have hmul : listDisc φ w * dpG prec hacyc r φ (D ∪ w.toFinset) ≤ 0 := by linarith
  exact nonpos_of_mul_nonpos_right hmul (listDisc_pos hφ₀ w)

/-- Master inequality (part 1): contribution of elements inside `W`. -/
lemma listValIn_le_dpG {r φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) (hφ₁ : ∀ i, φ i < 1)
    {D W : Finset (Fin n)} {π : List (Fin n)}
    (hπ : ValidPrefix prec D (π.filter (· ∈ W))) :
    listValIn W r φ π ≤ dpG prec hacyc r φ D := by
  induction π generalizing D with
  | nil => simp [listValIn, dpG_nonneg]
  | cons x xs ih =>
    by_cases hx : x ∈ W
    · simp only [List.filter_cons, hx, decide_true, ↓reduceIte, ValidPrefix] at hπ
      simp only [listValIn, hx, ↓reduceIte]
      calc r x + φ x * listValIn W r φ xs
          ≤ r x + φ x * dpG prec hacyc r φ (insert x D) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih hπ.2) (hφ₀ x).le)
        _ ≤ dpG prec hacyc r φ D := le_dpG prec hacyc r φ hπ.1
    · simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, ↓reduceIte] at hπ
      simp only [listValIn, hx, ↓reduceIte, zero_add]
      calc φ x * listValIn W r φ xs
          ≤ φ x * dpG prec hacyc r φ D :=
            mul_le_mul_of_nonneg_left (ih hπ) (hφ₀ x).le
        _ ≤ 1 * dpG prec hacyc r φ D :=
            mul_le_mul_of_nonneg_right (hφ₁ x).le (dpG_nonneg prec hacyc r φ D)
        _ = dpG prec hacyc r φ D := one_mul _

/-- Master inequality (part 2): excess contribution of elements outside `W`. -/
lemma listValOut_sub_le {r φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) (hφ₁ : ∀ i, φ i < 1)
    {E W : Finset (Fin n)} {π : List (Fin n)}
    (hπ : ValidPrefix prec E (π.filter (· ∉ W))) :
    listValOut W r φ π -
        listDisc φ (π.filter (· ∈ W)) * listVal r φ (π.filter (· ∉ W)) ≤
      (1 - listDisc φ (π.filter (· ∈ W))) * dpG prec hacyc r φ E := by
  induction π generalizing E with
  | nil => simp [listValOut, listDisc, listVal]
  | cons x xs ih =>
    by_cases hx : x ∈ W
    · simp only [List.filter_cons, hx, not_true_eq_false, decide_true, decide_false,
        Bool.false_eq_true, ↓reduceIte] at hπ ⊢
      simp only [listValOut, hx, not_true_eq_false, ↓reduceIte, zero_add, listDisc]
      have h1 : φ x * listValOut W r φ xs -
            φ x * listDisc φ (xs.filter (· ∈ W)) * listVal r φ (xs.filter (· ∉ W)) =
          φ x * (listValOut W r φ xs -
            listDisc φ (xs.filter (· ∈ W)) * listVal r φ (xs.filter (· ∉ W))) := by ring
      rw [h1]
      have hih := ih hπ
      have hstep : φ x * (1 - listDisc φ (xs.filter (· ∈ W))) ≤
          1 - φ x * listDisc φ (xs.filter (· ∈ W)) := by
        have := hφ₁ x
        linarith
      calc φ x * (listValOut W r φ xs -
              listDisc φ (xs.filter (· ∈ W)) * listVal r φ (xs.filter (· ∉ W)))
          ≤ φ x * ((1 - listDisc φ (xs.filter (· ∈ W))) * dpG prec hacyc r φ E) :=
            mul_le_mul_of_nonneg_left hih (hφ₀ x).le
        _ = (φ x * (1 - listDisc φ (xs.filter (· ∈ W)))) * dpG prec hacyc r φ E := by ring
        _ ≤ (1 - φ x * listDisc φ (xs.filter (· ∈ W))) * dpG prec hacyc r φ E :=
            mul_le_mul_of_nonneg_right hstep (dpG_nonneg prec hacyc r φ E)
    · simp only [List.filter_cons, hx, not_false_eq_true, decide_false, decide_true,
        Bool.false_eq_true, ↓reduceIte, ValidPrefix] at hπ ⊢
      simp only [listValOut, hx, not_false_eq_true, ↓reduceIte, listVal]
      have h1 : r x + φ x * listValOut W r φ xs -
            listDisc φ (xs.filter (· ∈ W)) * (r x + φ x * listVal r φ (xs.filter (· ∉ W))) =
          (1 - listDisc φ (xs.filter (· ∈ W))) * r x +
            φ x * (listValOut W r φ xs -
              listDisc φ (xs.filter (· ∈ W)) * listVal r φ (xs.filter (· ∉ W))) := by ring
      rw [h1]
      have hih := ih hπ.2
      have h1md : 0 ≤ 1 - listDisc φ (xs.filter (· ∈ W)) :=
        sub_nonneg.2 (listDisc_le_one hφ₀ hφ₁ _)
      calc (1 - listDisc φ (xs.filter (· ∈ W))) * r x +
              φ x * (listValOut W r φ xs -
                listDisc φ (xs.filter (· ∈ W)) * listVal r φ (xs.filter (· ∉ W)))
          ≤ (1 - listDisc φ (xs.filter (· ∈ W))) * r x +
              φ x * ((1 - listDisc φ (xs.filter (· ∈ W))) * dpG prec hacyc r φ (insert x E)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hih (hφ₀ x).le)
        _ = (1 - listDisc φ (xs.filter (· ∈ W))) *
              (r x + φ x * dpG prec hacyc r φ (insert x E)) := by ring
        _ ≤ (1 - listDisc φ (xs.filter (· ∈ W))) * dpG prec hacyc r φ E :=
            mul_le_mul_of_nonneg_left (le_dpG prec hacyc r φ hπ.1) h1md

/-- Equality analysis in `listValOut_sub_le` when the head is outside `W`. -/
lemma listValOut_eq_imp {r φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) (hφ₁ : ∀ i, φ i < 1)
    {D W : Finset (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (hπ : ValidPrefix prec D (x :: xs))
    (hxW : x ∉ W)
    (hlt : listDisc φ ((x :: xs).filter (· ∈ W)) < 1)
    (heq : listValOut W r φ (x :: xs) -
        listDisc φ ((x :: xs).filter (· ∈ W)) * listVal r φ ((x :: xs).filter (· ∉ W)) =
      (1 - listDisc φ ((x :: xs).filter (· ∈ W))) * dpG prec hacyc r φ (D ∪ W)) :
    dpG prec hacyc r φ (D ∪ W) ≤ r x + φ x * dpG prec hacyc r φ (insert x D) := by
  induction xs generalizing D x with
  | nil =>
    simp [hxW, listDisc] at hlt
  | cons y ys ih =>
    rcases hπ with ⟨hxD, hxs⟩
    have hxDW : x ∈ availSet prec (D ∪ W) := by
      have hx' := (mem_availSet prec).1 hxD
      exact (mem_availSet prec).2 ⟨by simp [hx'.1, hxW], fun i hi => Finset.mem_union_left _ (hx'.2 i hi)⟩
    have hfilt_out : ValidPrefix prec (insert x D ∪ W) ((y :: ys).filter (· ∉ W)) :=
      ValidPrefix.filter_not_mem prec W hxs
    have hfilt_in : (x :: y :: ys).filter (· ∈ W) = (y :: ys).filter (· ∈ W) := by
      simp [hxW]
    have hfilt_not : (x :: y :: ys).filter (· ∉ W) = x :: (y :: ys).filter (· ∉ W) := by
      simp [hxW]
    rw [hfilt_in] at hlt heq
    rw [hfilt_not] at heq
    rw [listValOut, if_pos hxW, listVal] at heq
    set d := listDisc φ ((y :: ys).filter (· ∈ W))
    set Q := listValOut W r φ (y :: ys) - d * listVal r φ ((y :: ys).filter (· ∉ W))
    have h1md : 0 < 1 - d := sub_pos.2 hlt
    have hQle : Q ≤ (1 - d) * dpG prec hacyc r φ (insert x D ∪ W) :=
      listValOut_sub_le prec hacyc hφ₀ hφ₁ hfilt_out
    have hrle : r x + φ x * dpG prec hacyc r φ (insert x D ∪ W) ≤ dpG prec hacyc r φ (D ∪ W) := by
      rw [Finset.insert_union]
      exact le_dpG prec hacyc r φ hxDW
    have hheq : (1 - d) * r x + φ x * Q = (1 - d) * dpG prec hacyc r φ (D ∪ W) := by
      dsimp only [Q]
      linarith
    have hQeq : Q = (1 - d) * dpG prec hacyc r φ (insert x D ∪ W) := by
      by_contra hne
      have hQlt : Q < (1 - d) * dpG prec hacyc r φ (insert x D ∪ W) := lt_of_le_of_ne hQle hne
      have h1 : (1 - d) * r x + φ x * Q <
          (1 - d) * (r x + φ x * dpG prec hacyc r φ (insert x D ∪ W)) := by
        have := mul_lt_mul_of_pos_left hQlt (hφ₀ x)
        linarith
      have h2 : (1 - d) * (r x + φ x * dpG prec hacyc r φ (insert x D ∪ W)) ≤
          (1 - d) * dpG prec hacyc r φ (D ∪ W) :=
        mul_le_mul_of_nonneg_left hrle h1md.le
      linarith
    have hreq : r x + φ x * dpG prec hacyc r φ (insert x D ∪ W) = dpG prec hacyc r φ (D ∪ W) := by
      have : (1 - d) * (r x + φ x * dpG prec hacyc r φ (insert x D ∪ W)) =
          (1 - d) * dpG prec hacyc r φ (D ∪ W) := by
        rw [hQeq] at hheq
        linarith
      exact mul_left_cancel₀ h1md.ne' this
    -- Now show dpG (insert x D ∪ W) ≤ dpG (insert x D)
    have hGcmp : dpG prec hacyc r φ (insert x D ∪ W) ≤ dpG prec hacyc r φ (insert x D) := by
      by_cases hyW : y ∈ W
      · have hfilt_ys : ValidPrefix prec (insert x D ∪ W) (ys.filter (· ∉ W)) := by
          simpa [List.filter_cons, hyW] using hfilt_out
        have hQys : listValOut W r φ ys -
            listDisc φ (ys.filter (· ∈ W)) * listVal r φ (ys.filter (· ∉ W)) ≤
            (1 - listDisc φ (ys.filter (· ∈ W))) * dpG prec hacyc r φ (insert x D ∪ W) :=
          listValOut_sub_le prec hacyc hφ₀ hφ₁ hfilt_ys
        have hQ_eq : Q = φ y * (listValOut W r φ ys -
            listDisc φ (ys.filter (· ∈ W)) * listVal r φ (ys.filter (· ∉ W))) := by
          simp only [Q, d, listValOut, hyW, not_true_eq_false, ↓reduceIte, zero_add,
            List.filter_cons, decide_true, listDisc, decide_false, Bool.false_eq_true]
          ring
        have hd_eq : d = φ y * listDisc φ (ys.filter (· ∈ W)) := by
          simp [d, hyW, listDisc]
        have hle1 : (1 - φ y * listDisc φ (ys.filter (· ∈ W))) *
              dpG prec hacyc r φ (insert x D ∪ W) ≤
            φ y * ((1 - listDisc φ (ys.filter (· ∈ W))) *
              dpG prec hacyc r φ (insert x D ∪ W)) := by
          rw [← hd_eq, ← hQeq, hQ_eq]
          exact mul_le_mul_of_nonneg_left hQys (hφ₀ y).le
        have hzero : (1 - φ y) * dpG prec hacyc r φ (insert x D ∪ W) ≤ 0 := by linarith
        have hG0 : dpG prec hacyc r φ (insert x D ∪ W) ≤ 0 :=
          nonpos_of_mul_nonpos_right hzero (sub_pos.2 (hφ₁ y))
        exact hG0.trans (dpG_nonneg prec hacyc r φ _)
      · have hstep := ih hxs hyW hlt hQeq
        exact hstep.trans (le_dpG prec hacyc r φ hxs.1)
    rw [← hreq]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hGcmp (hφ₀ x).le)

/-- Claim 1: `φ j * Δ(insert j D) ≤ Δ(D)` for every available `j`. -/
lemma mul_delta_le_delta {r φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) (hφ₁ : ∀ i, φ i < 1)
    {D : Finset (Fin n)} {j : Fin n} (hj : j ∈ availSet prec D) :
    φ j * (dpG prec hacyc r φ (insert j D) - dpU prec hacyc r φ (insert j D)) ≤
      dpG prec hacyc r φ D - dpU prec hacyc r φ D := by
  obtain ⟨τ, hτ, hτval⟩ := exists_validPrefix_eq_dpG prec hacyc r φ (insert j D)
  have hw : ValidPrefix prec D (j :: τ) := ⟨hj, hτ⟩
  set W : Finset (Fin n) := (j :: τ).toFinset
  have hDW : D ∪ W = insert j D ∪ τ.toFinset := by
    ext a; simp [W]
  have hGE0 : dpG prec hacyc r φ (D ∪ W) = 0 := by
    rw [hDW]
    exact dpG_union_eq_zero_of_eq_dpG prec hacyc hφ₀ hτ hτval
  -- Lower bound on dpU (insert j D): run τ then optimal completion of D ∪ W
  obtain ⟨σE, hσE, hσEval⟩ := exists_validFull_eq_dpU prec hacyc r φ (D ∪ W)
  have hτσ : ValidFull prec (insert j D) (τ ++ σE) := by
    refine ⟨(ValidPrefix.append_iff prec).2 ⟨hτ, ?_⟩, ?_⟩
    · rw [← hDW]; exact hσE.1
    · rw [List.toFinset_append, ← Finset.union_assoc, ← hDW, hσE.2]
  have hU_j : dpG prec hacyc r φ (insert j D) + listDisc φ τ * dpU prec hacyc r φ (D ∪ W) ≤
      dpU prec hacyc r φ (insert j D) := by
    calc dpG prec hacyc r φ (insert j D) + listDisc φ τ * dpU prec hacyc r φ (D ∪ W)
        = listVal r φ τ + listDisc φ τ * listVal r φ σE := by rw [hτval, hσEval]
      _ = listVal r φ (τ ++ σE) := (listVal_append r φ τ σE).symm
      _ ≤ dpU prec hacyc r φ (insert j D) := listVal_le_dpU prec hacyc hφ₀ hτσ
  -- Upper bound on dpU D via Master Inequality on an optimal full ordering π of Dᶜ
  obtain ⟨π, hπ, hπval⟩ := exists_validFull_eq_dpU prec hacyc r φ D
  have hπ_in : ValidPrefix prec D (π.filter (· ∈ W)) :=
    ValidPrefix.filter_mem prec hπ.1 hw.downwardClosed
  have hπ_out : ValidFull prec (D ∪ W) (π.filter (· ∉ W)) := by
    refine ⟨ValidPrefix.filter_not_mem prec W hπ.1, ?_⟩
    ext a
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_not, Bool.not_eq_true',
      decide_eq_false_iff_not, Finset.mem_univ, iff_true]
    by_cases haD : a ∈ D
    · exact Or.inl (Or.inl haD)
    · by_cases haW : a ∈ W
      · exact Or.inl (Or.inr haW)
      · have haπ : a ∈ π := by
          have := Finset.mem_univ a
          rw [← hπ.2, Finset.mem_union, List.mem_toFinset] at this
          exact this.resolve_left haD
        exact Or.inr ⟨haπ, haW⟩
  have hdisc_eq : listDisc φ (π.filter (· ∈ W)) = φ j * listDisc φ τ := by
    have hto : (π.filter (· ∈ W)).toFinset = W := by
      ext a
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
      intro haW
      have haD : a ∉ D := Finset.disjoint_right.1 hw.disjoint haW
      have := Finset.mem_univ a
      rw [← hπ.2, Finset.mem_union, List.mem_toFinset] at this
      exact this.resolve_left haD
    rw [listDisc_eq_prod_toFinset φ hπ_in.nodup, hto, ← listDisc_eq_prod_toFinset φ hw.nodup]
    rfl
  have h1 : listValIn W r φ π ≤ dpG prec hacyc r φ D :=
    listValIn_le_dpG prec hacyc hφ₀ hφ₁ hπ_in
  have h2 : listValOut W r φ π -
      listDisc φ (π.filter (· ∈ W)) * listVal r φ (π.filter (· ∉ W)) ≤
      (1 - listDisc φ (π.filter (· ∈ W))) * dpG prec hacyc r φ (D ∪ W) :=
    listValOut_sub_le prec hacyc hφ₀ hφ₁ hπ_out.1
  rw [hGE0, mul_zero] at h2
  have h3 : listVal r φ (π.filter (· ∉ W)) ≤ dpU prec hacyc r φ (D ∪ W) :=
    listVal_le_dpU prec hacyc hφ₀ hπ_out
  have hU_D : dpU prec hacyc r φ D ≤
      dpG prec hacyc r φ D + (φ j * listDisc φ τ) * dpU prec hacyc r φ (D ∪ W) := by
    rw [← hπval, listVal_eq_add W r φ π]
    have hmul : listDisc φ (π.filter (· ∈ W)) * listVal r φ (π.filter (· ∉ W)) ≤
        (φ j * listDisc φ τ) * dpU prec hacyc r φ (D ∪ W) := by
      rw [hdisc_eq]
      exact mul_le_mul_of_nonneg_left h3 (mul_pos (hφ₀ j) (listDisc_pos hφ₀ τ)).le
    linarith
  have hmul_j : φ j * (dpG prec hacyc r φ (insert j D) - dpU prec hacyc r φ (insert j D)) ≤
      -(φ j * listDisc φ τ * dpU prec hacyc r φ (D ∪ W)) := by
    have : dpG prec hacyc r φ (insert j D) - dpU prec hacyc r φ (insert j D) ≤
        -(listDisc φ τ * dpU prec hacyc r φ (D ∪ W)) := by linarith
    have := mul_le_mul_of_nonneg_left this (hφ₀ j).le
    linarith
  linarith

/-- The Combinatorial Equivalence Theorem: when `dpH D ≥ 0`, the maximizers of `dpH D` are
    exactly the maximizers of `dpU D`. -/
theorem dpH_maximizer_iff_dpU_maximizer {r φ : Fin n → ℝ} (hφ₀ : ∀ i, 0 < φ i) (hφ₁ : ∀ i, φ i < 1)
    {D : Finset (Fin n)} (hD : D ≠ Finset.univ) (hH : 0 ≤ dpH prec hacyc r φ D)
    {j : Fin n} (hj : j ∈ availSet prec D) :
    r j + φ j * dpG prec hacyc r φ (insert j D) = dpH prec hacyc r φ D ↔
      r j + φ j * dpU prec hacyc r φ (insert j D) = dpU prec hacyc r φ D := by
  have hGD : dpG prec hacyc r φ D = dpH prec hacyc r φ D := by
    rw [dpG_eq_max, max_eq_right hH]
  constructor
  · intro hopt
    apply le_antisymm (le_dpU prec hacyc r φ hj)
    have hΔ : φ j * (dpG prec hacyc r φ (insert j D) - dpU prec hacyc r φ (insert j D)) ≤
        dpG prec hacyc r φ D - dpU prec hacyc r φ D :=
      mul_delta_le_delta prec hacyc hφ₀ hφ₁ hj
    linarith
  · intro hopt
    apply le_antisymm (le_dpH prec hacyc r φ hj)
    -- Choose an optimal full ordering `j :: xs` of `Dᶜ` attaining `dpU D`
    obtain ⟨xs, hπ, hπval⟩ := exists_validFull_head_eq_dpU prec hacyc r φ hj hopt
    -- Choose a nonempty valid prefix `τ` of `Dᶜ` attaining `dpH D = dpG D`
    obtain ⟨τ, hτ, hτne, hτval⟩ := exists_validPrefix_ne_nil_eq_dpH prec hacyc r φ hD
    set W : Finset (Fin n) := τ.toFinset
    have hτG : listVal r φ τ = dpG prec hacyc r φ D := by rw [hτval, hGD]
    have hGE0 : dpG prec hacyc r φ (D ∪ W) = 0 :=
      dpG_union_eq_zero_of_eq_dpG prec hacyc hφ₀ hτ hτG
    -- Lower bound: dpU D ≥ dpG D + listDisc φ τ * dpU (D ∪ W)
    obtain ⟨σE, hσE, hσEval⟩ := exists_validFull_eq_dpU prec hacyc r φ (D ∪ W)
    have hτσ : ValidFull prec D (τ ++ σE) := by
      refine ⟨(ValidPrefix.append_iff prec).2 ⟨hτ, hσE.1⟩, ?_⟩
      rw [List.toFinset_append, ← Finset.union_assoc, hσE.2]
    have hU_lb : dpG prec hacyc r φ D + listDisc φ τ * dpU prec hacyc r φ (D ∪ W) ≤
        dpU prec hacyc r φ D := by
      calc dpG prec hacyc r φ D + listDisc φ τ * dpU prec hacyc r φ (D ∪ W)
          = listVal r φ τ + listDisc φ τ * listVal r φ σE := by rw [hτG, hσEval]
        _ = listVal r φ (τ ++ σE) := (listVal_append r φ τ σE).symm
        _ ≤ dpU prec hacyc r φ D := listVal_le_dpU prec hacyc hφ₀ hτσ
    -- Upper bound on `π = j :: xs` via Master Inequalities
    have hπ_in : ValidPrefix prec D ((j :: xs).filter (· ∈ W)) :=
      ValidPrefix.filter_mem prec hπ.1 hτ.downwardClosed
    have hπ_out : ValidFull prec (D ∪ W) ((j :: xs).filter (· ∉ W)) := by
      refine ⟨ValidPrefix.filter_not_mem prec W hπ.1, ?_⟩
      ext a
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_not, Bool.not_eq_true',
        decide_eq_false_iff_not, Finset.mem_univ, iff_true]
      by_cases haD : a ∈ D
      · exact Or.inl (Or.inl haD)
      · by_cases haW : a ∈ W
        · exact Or.inl (Or.inr haW)
        · have haπ : a ∈ j :: xs := by
            have := Finset.mem_univ a
            rw [← hπ.2, Finset.mem_union, List.mem_toFinset] at this
            exact this.resolve_left haD
          exact Or.inr ⟨haπ, haW⟩
    have hdisc_eq : listDisc φ ((j :: xs).filter (· ∈ W)) = listDisc φ τ := by
      have hto : ((j :: xs).filter (· ∈ W)).toFinset = W := by
        ext a
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
        intro haW
        have haD : a ∉ D := Finset.disjoint_right.1 hτ.disjoint haW
        have := Finset.mem_univ a
        rw [← hπ.2, Finset.mem_union, List.mem_toFinset] at this
        exact this.resolve_left haD
      rw [listDisc_eq_prod_toFinset φ hπ_in.nodup, hto, ← listDisc_eq_prod_toFinset φ hτ.nodup]
    have h1 : listValIn W r φ (j :: xs) ≤ dpG prec hacyc r φ D :=
      listValIn_le_dpG prec hacyc hφ₀ hφ₁ hπ_in
    have h2 : listValOut W r φ (j :: xs) -
        listDisc φ ((j :: xs).filter (· ∈ W)) * listVal r φ ((j :: xs).filter (· ∉ W)) ≤
        (1 - listDisc φ ((j :: xs).filter (· ∈ W))) * dpG prec hacyc r φ (D ∪ W) :=
      listValOut_sub_le prec hacyc hφ₀ hφ₁ hπ_out.1
    rw [hGE0, mul_zero] at h2
    have h3 : listVal r φ ((j :: xs).filter (· ∉ W)) ≤ dpU prec hacyc r φ (D ∪ W) :=
      listVal_le_dpU prec hacyc hφ₀ hπ_out
    have hmul : listDisc φ ((j :: xs).filter (· ∈ W)) * listVal r φ ((j :: xs).filter (· ∉ W)) ≤
        listDisc φ τ * dpU prec hacyc r φ (D ∪ W) := by
      rw [hdisc_eq]
      exact mul_le_mul_of_nonneg_left h3 (listDisc_pos hφ₀ τ).le
    -- Squeeze: all inequalities are equalities!
    have hsplit := listVal_eq_add W r φ (j :: xs)
    have h1_eq : listValIn W r φ (j :: xs) = dpG prec hacyc r φ D := by linarith
    have h2_eq : listValOut W r φ (j :: xs) -
        listDisc φ ((j :: xs).filter (· ∈ W)) * listVal r φ ((j :: xs).filter (· ∉ W)) = 0 := by
      linarith
    by_cases hjW : j ∈ W
    · -- Head `j ∈ W`: `listValIn` immediately gives `r j + φ j * dpG (insert j D) = dpG D`
      simp only [List.filter_cons, hjW, decide_true, ↓reduceIte, ValidPrefix] at hπ_in
      simp only [listValIn, hjW, ↓reduceIte] at h1_eq
      have hxs_le : listValIn W r φ xs ≤ dpG prec hacyc r φ (insert j D) :=
        listValIn_le_dpG prec hacyc hφ₀ hφ₁ hπ_in.2
      have := mul_le_mul_of_nonneg_left hxs_le (hφ₀ j).le
      linarith
    · -- Head `j ∉ W`:
      by_cases hGpos : 0 < dpG prec hacyc r φ D
      · -- Contradiction: `listValIn` shrinks by `φ j < 1`
        simp only [List.filter_cons, hjW, decide_false, Bool.false_eq_true, ↓reduceIte] at hπ_in
        simp only [listValIn, hjW, ↓reduceIte, zero_add] at h1_eq
        have hxs_le : listValIn W r φ xs ≤ dpG prec hacyc r φ D :=
          listValIn_le_dpG prec hacyc hφ₀ hφ₁ hπ_in
        have hlt1 : φ j * listValIn W r φ xs ≤ φ j * dpG prec hacyc r φ D :=
          mul_le_mul_of_nonneg_left hxs_le (hφ₀ j).le
        have hlt2 : φ j * dpG prec hacyc r φ D < 1 * dpG prec hacyc r φ D :=
          mul_lt_mul_of_pos_right (hφ₁ j) hGpos
        linarith
      · -- `dpG D = 0`, hence `dpH D = 0`; use `listValOut_eq_imp`!
        have hGD0 : dpG prec hacyc r φ D = 0 := le_antisymm (not_lt.1 hGpos) (dpG_nonneg prec hacyc r φ D)
        have hlt_disc : listDisc φ ((j :: xs).filter (· ∈ W)) < 1 := by
          rw [hdisc_eq]
          exact listDisc_lt_one_of_ne_nil hφ₀ hφ₁ hτne
        have heq_out : listValOut W r φ (j :: xs) -
            listDisc φ ((j :: xs).filter (· ∈ W)) * listVal r φ ((j :: xs).filter (· ∉ W)) =
          (1 - listDisc φ ((j :: xs).filter (· ∈ W))) * dpG prec hacyc r φ (D ∪ W) := by
          rw [hGE0, mul_zero, h2_eq]
        have hstep := listValOut_eq_imp prec hacyc hφ₀ hφ₁ hπ.1 hjW hlt_disc heq_out
        rw [hGE0] at hstep
        linarith

/-! ### Section 2: Shifting Rewards by `-λ c_j` -/

lemma dpU_shift (a φ : Fin n → ℝ) (γ : ℝ) (hγ : γ ≠ 0) (lam : ℝ) (D : Finset (Fin n)) :
    dpU prec hacyc (fun j => a j - lam * (γ⁻¹ * (1 - φ j))) φ D =
      dpU prec hacyc a φ D - lam * γ⁻¹ * (1 - ∏ i ∈ Dᶜ, φ i) := by
  by_cases hD : D = Finset.univ
  · subst hD
    simp [dpU_univ]
  · rw [dpU_eq_sup' prec hacyc _ φ hD, dpU_eq_sup' prec hacyc a φ hD]
    have hterm : ∀ j ∈ availSet prec D,
        (a j - lam * (γ⁻¹ * (1 - φ j))) +
            φ j * dpU prec hacyc (fun j => a j - lam * (γ⁻¹ * (1 - φ j))) φ (insert j D) =
          (a j + φ j * dpU prec hacyc a φ (insert j D)) -
            lam * γ⁻¹ * (1 - ∏ i ∈ Dᶜ, φ i) := by
      intro j hj
      have hjD : j ∉ D := ((mem_availSet prec).1 hj).1
      have : n - (insert j D).card < n - D.card := card_sub_insert_lt hjD
      rw [dpU_shift a φ γ hγ lam (insert j D)]
      have hprod : ∏ i ∈ Dᶜ, φ i = φ j * ∏ i ∈ (insert j D)ᶜ, φ i := by
        have hcompl : Dᶜ = insert j (insert j D)ᶜ := by
          ext i
          simp only [Finset.mem_compl, Finset.mem_insert]
          by_cases hij : i = j
          · subst hij; simp [hjD]
          · simp [hij]
        have hnotmem : j ∉ (insert j D)ᶜ := by simp
        rw [hcompl, Finset.prod_insert hnotmem]
      rw [hprod]
      ring
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j hj => ?_
      rw [hterm j hj]
      exact sub_le_sub_right
        (Finset.le_sup' (fun j => a j + φ j * dpU prec hacyc a φ (insert j D)) hj) _
    · rw [sub_le_iff_le_add]
      refine Finset.sup'_le _ _ fun j hj => ?_
      have := Finset.le_sup'
        (fun j => (a j - lam * (γ⁻¹ * (1 - φ j))) +
          φ j * dpU prec hacyc (fun j => a j - lam * (γ⁻¹ * (1 - φ j))) φ (insert j D)) hj
      rw [hterm j hj] at this
      linarith
termination_by n - D.card

lemma dpU_shift_maximizer_iff (a φ : Fin n → ℝ) (γ : ℝ) (hγ : γ ≠ 0) (lam : ℝ)
    {D : Finset (Fin n)} {j : Fin n} (hj : j ∈ availSet prec D) :
    (a j - lam * (γ⁻¹ * (1 - φ j))) +
        φ j * dpU prec hacyc (fun j => a j - lam * (γ⁻¹ * (1 - φ j))) φ (insert j D) =
      dpU prec hacyc (fun j => a j - lam * (γ⁻¹ * (1 - φ j))) φ D ↔
    a j + φ j * dpU prec hacyc a φ (insert j D) = dpU prec hacyc a φ D := by
  rw [dpU_shift prec hacyc a φ γ hγ lam (insert j D),
      dpU_shift prec hacyc a φ γ hγ lam D]
  have hjD : j ∉ D := ((mem_availSet prec).1 hj).1
  have hprod : ∏ i ∈ Dᶜ, φ i = φ j * ∏ i ∈ (insert j D)ᶜ, φ i := by
    have hcompl : Dᶜ = insert j (insert j D)ᶜ := by
      ext i
      simp only [Finset.mem_compl, Finset.mem_insert]
      by_cases hij : i = j
      · subst hij; simp [hjD]
      · simp [hij]
    rw [hcompl, Finset.prod_insert (by simp)]
  rw [hprod]
  constructor <;> intro h <;> linarith

end Combinatorial

/-! ### Section 3: Probability, Measure Theory, and Stage Telescoping Identity -/

section Probability

open scoped Classical

variable {n : ℕ}

noncomputable def phi (F : JobFamily n) (i : Fin n) : ℝ :=
  ∫ x, Real.exp (-F.γ * x) ∂(F.service i : Measure ℝ)

noncomputable def jobA (F : JobFamily n) (i : Fin n) : ℝ :=
  F.reward i * phi F i

noncomputable def jobC (F : JobFamily n) (i : Fin n) : ℝ :=
  F.γ⁻¹ * (1 - phi F i)

noncomputable def jobR (F : JobFamily n) (lam : ℝ) (i : Fin n) : ℝ :=
  jobA F i - lam * jobC F i

noncomputable def famG (F : JobFamily n) (lam : ℝ) (D : Finset (Fin n)) : ℝ :=
  dpG F.prec F.prec_acyclic (jobR F lam) (phi F) D

noncomputable def famH (F : JobFamily n) (lam : ℝ) (D : Finset (Fin n)) : ℝ :=
  dpH F.prec F.prec_acyclic (jobR F lam) (phi F) D

lemma famG_univ (F : JobFamily n) (lam : ℝ) : famG F lam Finset.univ = 0 :=
  dpG_univ _ _ _ _

lemma famG_eq_max (F : JobFamily n) (lam : ℝ) (D : Finset (Fin n)) :
    famG F lam D = max 0 (famH F lam D) :=
  dpG_eq_max _ _ _ _ D

lemma famG_nonneg (F : JobFamily n) (lam : ℝ) (D : Finset (Fin n)) :
    0 ≤ famG F lam D :=
  dpG_nonneg _ _ _ _ D

lemma ae_pos_service (F : JobFamily n) (i : Fin n) :
    ∀ᵐ x ∂(F.service i : Measure ℝ), 0 < x := by
  rw [ae_iff]
  have hsub : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by ext x; simp
  rw [hsub]
  exact F.service_pos i

lemma integrable_exp_service (F : JobFamily n) (i : Fin n) :
    Integrable (fun x : ℝ => Real.exp (-F.γ * x)) (F.service i : Measure ℝ) := by
  refine Integrable.of_bound
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) 1 ?_
  filter_upwards [ae_pos_service F i] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos])

lemma phi_pos (F : JobFamily n) (i : Fin n) : 0 < phi F i :=
  integral_exp_pos (integrable_exp_service F i)

lemma phi_lt_one (F : JobFamily n) (i : Fin n) : phi F i < 1 := by
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (F.service i : Measure ℝ) := integrable_const 1
  have h2 := integrable_exp_service F i
  have hsub : Integrable (fun x : ℝ => 1 - Real.exp (-F.γ * x)) (F.service i : Measure ℝ) :=
    h1.sub h2
  have hpos_ae : ∀ᵐ x ∂(F.service i : Measure ℝ), 0 < 1 - Real.exp (-F.γ * x) := by
    filter_upwards [ae_pos_service F i] with x hx
    have : Real.exp (-F.γ * x) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [F.γ_pos])
    linarith
  have hnn_ae : 0 ≤ᵐ[(F.service i : Measure ℝ)] fun x => 1 - Real.exp (-F.γ * x) :=
    hpos_ae.mono fun _ h => h.le
  have hsupp : 0 < (F.service i : Measure ℝ) (Function.support fun x => 1 - Real.exp (-F.γ * x)) := by
    have hcompl : (F.service i : Measure ℝ)
        (Function.support fun x => 1 - Real.exp (-F.γ * x))ᶜ = 0 := by
      change (F.service i : Measure ℝ)
        {x : ℝ | ¬ (x ∈ Function.support fun x => 1 - Real.exp (-F.γ * x))} = 0
      rw [← ae_iff]
      filter_upwards [hpos_ae] with x hx
      rw [Function.mem_support]
      exact hx.ne'
    have hmeas : (F.service i : Measure ℝ) Set.univ = 1 := measure_univ
    by_contra h0
    have h0' : (F.service i : Measure ℝ) (Function.support fun x => 1 - Real.exp (-F.γ * x)) = 0 :=
      le_antisymm (not_lt.1 h0) bot_le
    have hsum : (F.service i : Measure ℝ) Set.univ ≤
        (F.service i : Measure ℝ) (Function.support fun x => 1 - Real.exp (-F.γ * x)) +
        (F.service i : Measure ℝ) (Function.support fun x => 1 - Real.exp (-F.γ * x))ᶜ := by
      calc (F.service i : Measure ℝ) Set.univ
          = (F.service i : Measure ℝ)
              ((Function.support fun x => 1 - Real.exp (-F.γ * x)) ∪
               (Function.support fun x => 1 - Real.exp (-F.γ * x))ᶜ) := by rw [Set.union_compl_self]
        _ ≤ _ := measure_union_le _ _
    rw [hmeas, h0', hcompl, add_zero] at hsum
    exact absurd hsum (by norm_num)
  have hint_pos : 0 < ∫ x, (1 - Real.exp (-F.γ * x)) ∂(F.service i : Measure ℝ) :=
    (integral_pos_iff_support_of_nonneg_ae hnn_ae hsub).2 hsupp
  rw [integral_sub h1 h2, integral_const, smul_eq_mul, mul_one,
      probReal_univ] at hint_pos
  unfold phi
  linarith

lemma jobA_pos (F : JobFamily n) (i : Fin n) : 0 < jobA F i :=
  mul_pos (F.reward_pos i) (phi_pos F i)

lemma jobC_pos (F : JobFamily n) (i : Fin n) : 0 < jobC F i :=
  mul_pos (inv_pos.2 F.γ_pos) (sub_pos.2 (phi_lt_one F i))

instance serviceLaw_isProbabilityMeasure (F : JobFamily n) :
    IsProbabilityMeasure (serviceLaw F) := by
  unfold serviceLaw
  infer_instance

lemma ae_pos_serviceLaw (F : JobFamily n) :
    ∀ᵐ ω ∂serviceLaw F, ∀ i : Fin n, 0 < ω i := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have hpre : {ω : Fin n → ℝ | ¬ 0 < ω i} =
      Set.univ.pi (Function.update (fun _ => Set.univ) i (Set.Iic 0)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, not_lt, Set.mem_univ_pi]
    constructor
    · intro h j
      by_cases hij : j = i
      · subst hij; simpa using h
      · simp [hij]
    · intro h
      simpa using h i
  rw [hpre, serviceLaw, Measure.pi_pi]
  have hzero : ∏ j : Fin n, (F.service j : Measure ℝ)
      (Function.update (fun _ => Set.univ) i (Set.Iic 0) j) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [F.service_pos i]
  exact hzero

/-! #### Measurability of policy and stage trajectories -/

lemma Policy.hist_length (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    (π.hist ω k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Policy.hist, ih]

/-- View `π.hist ω k` as a function `Fin k → Fin n × ℝ`. -/
def Policy.histFn (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) : Fin k → Fin n × ℝ :=
  fun i => (π.hist ω k).get (i.cast (π.hist_length ω k).symm)

lemma Policy.ofFn_histFn (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    List.ofFn (π.histFn ω k) = π.hist ω k := by
  apply List.ext_getElem
  · simp [π.hist_length]
  · intro i h1 h2
    simp [Policy.histFn]

lemma Policy.measurable_histFn (π : Policy n) (k : ℕ) :
    Measurable (fun ω : Fin n → ℝ => π.histFn ω k) := by
  induction k with
  | zero =>
    rw [measurable_pi_iff]
    intro i; exact Fin.elim0 i
  | succ k ih =>
    have hjob : Measurable (fun ω => π.job ω k) := by
      have hcomp := (π.measurable_next k).comp ih
      have heq : (fun ω => π.job ω k) = (fun h => π.next (List.ofFn h)) ∘ fun ω => π.histFn ω k := by
        funext ω; simp [Policy.job, Policy.ofFn_histFn]
      rw [heq]; exact hcomp
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i.val < k
    · have heq : (fun ω => π.histFn ω (k + 1) i) = (fun ω => π.histFn ω k ⟨i.val, hi⟩) := by
        funext ω
        simp only [Policy.histFn, Policy.hist, Fin.cast_mk]
        exact List.getElem_append_left (by rw [π.hist_length]; exact hi)
      rw [heq]
      exact (measurable_pi_apply ⟨i.val, hi⟩).comp ih
    · have hik : i.val = k := by omega
      have heq : (fun ω => π.histFn ω (k + 1) i) = (fun ω => (π.job ω k, ω (π.job ω k))) := by
        funext ω
        have hlen : (π.hist ω k).length = k := π.hist_length ω k
        have hge : (π.hist ω k).length ≤ i.val := by omega
        change (π.hist ω (k + 1))[i.val]'(by rw [π.hist_length]; exact i.isLt) =
          (π.job ω k, ω (π.job ω k))
        simp only [Policy.hist, Policy.job]
        rw [List.getElem_append_right hge]
        have hsub : i.val - (π.hist ω k).length = 0 := by omega
        simp [hsub]
      rw [heq]
      refine Measurable.prodMk hjob ?_
      have heval : Measurable (fun p : Fin n × (Fin n → ℝ) => p.2 p.1) :=
        measurable_from_prod_countable_right (f := fun p : Fin n × (Fin n → ℝ) => p.2 p.1)
          fun j => measurable_pi_apply j
      exact heval.comp (hjob.prodMk measurable_id)

lemma Policy.measurable_job (π : Policy n) (k : ℕ) :
    Measurable (fun ω : Fin n → ℝ => π.job ω k) := by
  have hcomp := (π.measurable_next k).comp (π.measurable_histFn k)
  have heq : (fun ω => π.job ω k) = (fun h => π.next (List.ofFn h)) ∘ fun ω => π.histFn ω k := by
    funext ω; simp [Policy.job, Policy.ofFn_histFn]
  rw [heq]; exact hcomp

lemma Policy.measurable_hist_jobs (π : Policy n) (k : ℕ) :
    Measurable (fun ω : Fin n → ℝ => (π.hist ω k).jobs) := by
  have hf : Measurable (fun u : Fin k → Fin n × ℝ => History.jobs (List.ofFn u)) := by
    have h1 : Measurable (fun u : Fin k → Fin n × ℝ => fun i => (u i).1) :=
      measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
    have h2 : Measurable (fun v : Fin k → Fin n => (List.ofFn v).toFinset) :=
      measurable_of_countable _
    have heq : (fun u : Fin k → Fin n × ℝ => History.jobs (List.ofFn u)) =
        (fun v : Fin k → Fin n => (List.ofFn v).toFinset) ∘ fun u i => (u i).1 := by
      funext u; simp [History.jobs, List.map_ofFn]; rfl
    rw [heq]; exact h2.comp h1
  have heq : (fun ω : Fin n → ℝ => (π.hist ω k).jobs) =
      (fun u => History.jobs (List.ofFn u)) ∘ fun ω => π.histFn ω k := by
    funext ω; simp [Policy.ofFn_histFn]
  rw [heq]; exact hf.comp (π.measurable_histFn k)

lemma Policy.measurable_startTime (π : Policy n) (k : ℕ) :
    Measurable (fun ω : Fin n → ℝ => π.startTime ω k) := by
  have hf : Measurable (fun u : Fin k → Fin n × ℝ => History.elapsed (List.ofFn u)) := by
    have hsum : (fun u : Fin k → Fin n × ℝ => History.elapsed (List.ofFn u)) =
        fun u => ∑ i : Fin k, (u i).2 := by
      funext u
      simp [History.elapsed, List.map_ofFn, List.sum_ofFn]
    rw [hsum]
    exact Finset.measurable_sum _ fun i _ => measurable_snd.comp (measurable_pi_apply i)
  have heq : (fun ω : Fin n → ℝ => π.startTime ω k) =
      (fun u => History.elapsed (List.ofFn u)) ∘ fun ω => π.histFn ω k := by
    funext ω; simp [Policy.startTime, Policy.ofFn_histFn]
  rw [heq]; exact hf.comp (π.measurable_histFn k)

lemma Policy.measurable_completionTime (π : Policy n) (k : ℕ) :
    Measurable (fun ω : Fin n → ℝ => π.completionTime ω k) :=
  π.measurable_startTime (k + 1)

lemma Stage.measurableSet_inStage (B : Finset (Fin n)) (p : Stage n) (k : ℕ) :
    MeasurableSet {ω : Fin n → ℝ | p.InStage B ω k} := by
  have heq : {ω : Fin n → ℝ | p.InStage B ω k} =
      {ω : Fin n → ℝ | k < numRemaining B} ∩
        ⋂ l ∈ Finset.Icc 1 k, {ω : Fin n → ℝ | p.stop (p.toPolicy.hist ω l) = false} := by
    ext ω; simp [Stage.InStage]
  rw [heq]
  refine (MeasurableSet.const _).inter (Finset.measurableSet_biInter _ fun l _ => ?_)
  have hstop : Measurable (fun ω => p.stop (p.toPolicy.hist ω l)) := by
    have hcomp := (p.measurable_stop l).comp (p.toPolicy.measurable_histFn l)
    have hfun : (fun ω => p.stop (p.toPolicy.hist ω l)) =
        (fun h => p.stop (List.ofFn h)) ∘ fun ω => p.toPolicy.histFn ω l := by
      funext ω; simp [Policy.ofFn_histFn]
    rw [hfun]; exact hcomp
  exact hstop (measurableSet_singleton false)

lemma Policy.startTime_nonneg (π : Policy n) {ω : Fin n → ℝ} (hω : ∀ i, 0 < ω i) (k : ℕ) :
    0 ≤ π.startTime ω k := by
  induction k with
  | zero => simp [Policy.startTime, Policy.hist, History.elapsed]
  | succ k ih =>
    simp only [Policy.startTime, Policy.hist, History.elapsed, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ih ⊢
    linarith [hω (π.next (π.hist ω k))]

lemma Policy.completionTime_eq (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    π.completionTime ω k = π.startTime ω k + ω (π.job ω k) := by
  simp [Policy.completionTime, Policy.startTime, Policy.hist, Policy.job, History.elapsed]

lemma Policy.completionTime_nonneg (π : Policy n) {ω : Fin n → ℝ} (hω : ∀ i, 0 < ω i) (k : ℕ) :
    0 ≤ π.completionTime ω k :=
  π.startTime_nonneg hω (k + 1)

/-! #### Coordinate independence and Fubini factorization -/

lemma Policy.hist_jobs_mono (π : Policy n) (ω : Fin n → ℝ) {m k : ℕ} (hmk : m ≤ k) :
    (π.hist ω m).jobs ⊆ (π.hist ω k).jobs := by
  induction hmk with
  | refl => exact Finset.Subset.refl _
  | step _ ih =>
    intro x hx
    have h1 := ih hx
    simp only [Policy.hist, History.jobs, List.map_append, List.toFinset_append, Finset.mem_union]
    exact Or.inl h1

lemma Policy.job_mem_hist_jobs (π : Policy n) (ω : Fin n → ℝ) {m k : ℕ} (hmk : m < k) :
    π.job ω m ∈ (π.hist ω k).jobs := by
  have h1 : π.job ω m ∈ (π.hist ω (m + 1)).jobs := by
    simp [Policy.hist, Policy.job, History.jobs]
  exact π.hist_jobs_mono ω hmk h1

lemma Policy.hist_update_eq_of_not_mem (π : Policy n) (ω : Fin n → ℝ) (j : Fin n) (x : ℝ)
    {k : ℕ} (hj : j ∉ (π.hist ω k).jobs) :
    ∀ m ≤ k, π.hist (Function.update ω j x) m = π.hist ω m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hmk
    have hm := ih (Nat.le_of_succ_le hmk)
    simp only [Policy.hist, hm]
    have hne : π.next (π.hist ω m) ≠ j := by
      intro heq
      apply hj
      rw [← heq]
      exact π.job_mem_hist_jobs ω hmk
    rw [Function.update_of_ne hne]

lemma Policy.hist_update_not_mem_iff (π : Policy n) (ω : Fin n → ℝ) (j : Fin n) (x : ℝ) (k : ℕ) :
    j ∉ (π.hist (Function.update ω j x) k).jobs ↔ j ∉ (π.hist ω k).jobs := by
  constructor
  · intro h
    have hback := π.hist_update_eq_of_not_mem (Function.update ω j x) j (ω j) h k le_rfl
    have hupd : Function.update (Function.update ω j x) j (ω j) = ω := by
      ext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    rw [hupd] at hback
    rw [hback]
    exact h
  · intro h
    rw [π.hist_update_eq_of_not_mem ω j x h k le_rfl]
    exact h

lemma integral_mul_exp_of_indep_succ {m : ℕ} (F : JobFamily (m + 1)) (j : Fin (m + 1))
    (g : (Fin (m + 1) → ℝ) → ℝ)
    (hg : ∀ ω x, g (Function.update ω j x) = g ω) :
    ∫ ω, Real.exp (-F.γ * ω j) * g ω ∂serviceLaw F =
      phi F j * ∫ ω, g ω ∂serviceLaw F := by
  set μ : Fin (m + 1) → Measure ℝ := fun i => (F.service i : Measure ℝ)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
  have hmp := (measurePreserving_piFinSuccAbove μ j).symm
  have hupd : ∀ (x : ℝ) (y : Fin m → ℝ),
      e.symm (x, y) = Function.update (e.symm (0, y)) j x := by
    intro x y
    ext i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      change Fin.insertNth (α := fun _ : Fin (m + 1) => ℝ) i x y i = x
      simp
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [Function.update_of_ne hi]
      change Fin.insertNth (α := fun _ : Fin (m + 1) => ℝ) j x y (j.succAbove k) =
        Fin.insertNth (α := fun _ : Fin (m + 1) => ℝ) j 0 y (j.succAbove k)
      simp
  have h1 : ∫ ω, Real.exp (-F.γ * ω j) * g ω ∂serviceLaw F =
      ∫ z : ℝ × (Fin m → ℝ), Real.exp (-F.γ * z.1) * g (e.symm (0, z.2))
        ∂((μ j).prod (Measure.pi fun k => μ (j.succAbove k))) := by
    rw [serviceLaw, ← hmp.integral_comp']
    congr 1 with ⟨x, y⟩
    have hjx : e.symm (x, y) j = x := by
      change Fin.insertNth (α := fun _ : Fin (m + 1) => ℝ) j x y j = x
      simp
    rw [hjx, hupd x y, hg]
  have h2 : ∫ ω, g ω ∂serviceLaw F =
      ∫ y : Fin m → ℝ, g (e.symm (0, y)) ∂(Measure.pi fun k => μ (j.succAbove k)) := by
    rw [serviceLaw, ← hmp.integral_comp']
    have hconst : (fun z : ℝ × (Fin m → ℝ) => g (e.symm z)) =
        fun z => (1 : ℝ) * g (e.symm (0, z.2)) := by
      funext ⟨x, y⟩
      rw [one_mul, hupd x y, hg]
    rw [hconst,
        integral_prod_mul (f := fun _ : ℝ => (1 : ℝ)) (g := fun y : Fin m → ℝ => g (e.symm (0, y))),
        integral_const, smul_eq_mul, mul_one, probReal_univ, one_mul]
  rw [h1,
      integral_prod_mul (f := fun x : ℝ => Real.exp (-F.γ * x))
        (g := fun y : Fin m → ℝ => g (e.symm (0, y))),
      h2]
  rfl

lemma integral_mul_exp_of_indep (F : JobFamily n) (j : Fin n)
    (g : (Fin n → ℝ) → ℝ)
    (hg : ∀ ω x, g (Function.update ω j x) = g ω) :
    ∫ ω, Real.exp (-F.γ * ω j) * g ω ∂serviceLaw F =
      phi F j * ∫ ω, g ω ∂serviceLaw F := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m => exact integral_mul_exp_of_indep_succ F j g hg

/-! #### Stepwise integrability and telescoping identity for stages -/

lemma Stage.inStage_zero (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ)
    (hB : B ≠ Finset.univ) : p.InStage B ω 0 := by
  refine ⟨?_, by simp⟩
  have hlt : B.card < (Finset.univ : Finset (Fin n)).card :=
    Finset.card_lt_card (Finset.ssubset_univ_iff.2 hB)
  simp only [numRemaining, Finset.card_univ, Fintype.card_fin] at hlt ⊢
  omega

lemma Stage.inStage_succ_imp (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ) {k : ℕ}
    (h : p.InStage B ω (k + 1)) : p.InStage B ω k := by
  refine ⟨Nat.lt_of_succ_lt h.1, fun l hl => h.2 l ?_⟩
  simp only [Finset.mem_Icc] at hl ⊢
  exact ⟨hl.1, by omega⟩

lemma Stage.hist_jobs_card_of_feasible (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n)
    (hp : p.Feasible F B) (ω : Fin n → ℝ) {k : ℕ} (hk : k ≤ numRemaining B) :
    (B ∪ (p.toPolicy.hist ω k).jobs).card = B.card + k := by
  induction k with
  | zero => simp [Policy.hist, History.jobs]
  | succ k ih =>
    have hk' : k < numRemaining B := Nat.lt_of_succ_le hk
    have hav := hp ω k hk'
    have hnotmem : p.toPolicy.job ω k ∉ B ∪ (p.toPolicy.hist ω k).jobs := hav.1
    have hset : B ∪ (p.toPolicy.hist ω (k + 1)).jobs =
        insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs) := by
      ext a
      simp [Policy.hist, Policy.job, History.jobs, or_left_comm]
    rw [hset, Finset.card_insert_of_notMem hnotmem, ih hk'.le]
    omega

lemma Stage.union_hist_jobs_eq_univ (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n)
    (hp : p.Feasible F B) (ω : Fin n → ℝ) :
    B ∪ (p.toPolicy.hist ω (numRemaining B)).jobs = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Stage.hist_jobs_card_of_feasible F B p hp ω le_rfl]
  have hle : B.card ≤ n := by simpa using Finset.card_le_univ B
  simp only [numRemaining, Fintype.card_fin]
  omega

lemma integrable_bounded_stage_term (F : JobFamily n) (f : (Fin n → ℝ) → ℝ)
    (hmeas : Measurable f) (C : ℝ)
    (hbound : ∀ ω, (∀ i, 0 < ω i) → ‖f ω‖ ≤ C) :
    Integrable f (serviceLaw F) := by
  refine Integrable.of_bound hmeas.aestronglyMeasurable C ?_
  filter_upwards [ae_pos_serviceLaw F] with ω hω
  exact hbound ω hω

/-- Step `k` net integrand for `R_{gτ} - λ W_{gτ}`. -/
noncomputable def stepNet (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) (lam : ℝ)
    (k : ℕ) (ω : Fin n → ℝ) : ℝ :=
  if p.InStage B ω k then
    F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k) -
      lam * (F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
        Real.exp (-F.γ * p.toPolicy.completionTime ω k)))
  else 0

/-- Telescoping martingale-like term `M k ω`. -/
noncomputable def teleM (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) (lam : ℝ)
    (k : ℕ) (ω : Fin n → ℝ) : ℝ :=
  if k = 0 then famH F lam B
  else if p.InStage B ω k then
    Real.exp (-F.γ * p.toPolicy.startTime ω k) * famG F lam (B ∪ (p.toPolicy.hist ω k).jobs)
  else 0

lemma integrable_stepReward (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) (k : ℕ) :
    Integrable (fun ω => if p.InStage B ω k then
      F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k) else 0)
      (serviceLaw F) := by
  refine integrable_bounded_stage_term F _ ?_ (∑ i : Fin n, F.reward i) fun ω hω => ?_
  · exact Measurable.ite (p.measurableSet_inStage B k)
      (((measurable_of_countable F.reward).comp (p.toPolicy.measurable_job k)).mul
        ((measurable_const.mul (p.toPolicy.measurable_completionTime k)).exp))
      measurable_const
  · split_ifs
    · rw [Real.norm_eq_abs, abs_of_pos (mul_pos (F.reward_pos _) (Real.exp_pos _))]
      have hexp : Real.exp (-F.γ * p.toPolicy.completionTime ω k) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.completionTime_nonneg hω k])
      calc F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k)
          ≤ F.reward (p.toPolicy.job ω k) * 1 :=
            mul_le_mul_of_nonneg_left hexp (F.reward_pos _).le
        _ = F.reward (p.toPolicy.job ω k) := mul_one _
        _ ≤ ∑ i : Fin n, F.reward i :=
            Finset.single_le_sum (fun i _ => (F.reward_pos i).le) (Finset.mem_univ _)
    · rw [norm_zero]
      exact Finset.sum_nonneg fun i _ => (F.reward_pos i).le

lemma integrable_stepTime (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) (k : ℕ) :
    Integrable (fun ω => if p.InStage B ω k then
      F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
        Real.exp (-F.γ * p.toPolicy.completionTime ω k)) else 0)
      (serviceLaw F) := by
  refine integrable_bounded_stage_term F _ ?_ (2 * F.γ⁻¹) fun ω hω => ?_
  · exact Measurable.ite (p.measurableSet_inStage B k)
      (measurable_const.mul
        (((measurable_const.mul (p.toPolicy.measurable_startTime k)).exp).sub
          ((measurable_const.mul (p.toPolicy.measurable_completionTime k)).exp)))
      measurable_const
  · split_ifs
    · have hs : Real.exp (-F.γ * p.toPolicy.startTime ω k) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.startTime_nonneg hω k])
      have hc : Real.exp (-F.γ * p.toPolicy.completionTime ω k) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.completionTime_nonneg hω k])
      have hdiff : |Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k)| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith [Real.exp_pos (-F.γ * p.toPolicy.startTime ω k),
          Real.exp_pos (-F.γ * p.toPolicy.completionTime ω k)]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 F.γ_pos)]
      nlinarith [inv_pos.2 F.γ_pos]
    · rw [norm_zero]
      exact mul_nonneg (by norm_num) (inv_pos.2 F.γ_pos).le

lemma integrable_teleM (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) (lam : ℝ) (k : ℕ) :
    Integrable (teleM F B p lam k) (serviceLaw F) := by
  unfold teleM
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    set C : ℝ := ∑ D : Finset (Fin n), famG F lam D
    refine integrable_bounded_stage_term F _ ?_ C fun ω hω => ?_
    · exact Measurable.ite (p.measurableSet_inStage B k)
        (((measurable_const.mul (p.toPolicy.measurable_startTime k)).exp).mul
          ((measurable_of_countable (fun D => famG F lam (B ∪ D))).comp
            (p.toPolicy.measurable_hist_jobs k)))
        measurable_const
    · split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (famG_nonneg F lam _))]
        have hexp : Real.exp (-F.γ * p.toPolicy.startTime ω k) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.startTime_nonneg hω k])
        calc Real.exp (-F.γ * p.toPolicy.startTime ω k) * famG F lam (B ∪ (p.toPolicy.hist ω k).jobs)
            ≤ 1 * famG F lam (B ∪ (p.toPolicy.hist ω k).jobs) :=
              mul_le_mul_of_nonneg_right hexp (famG_nonneg F lam _)
          _ = famG F lam (B ∪ (p.toPolicy.hist ω k).jobs) := one_mul _
          _ ≤ C := Finset.single_le_sum (fun D _ => famG_nonneg F lam D) (Finset.mem_univ _)
      · rw [norm_zero]
        exact Finset.sum_nonneg fun D _ => famG_nonneg F lam D

/-- Key single-step identity expressing `∫ (M k - M (k+1) - stepNet k)` as two nonnegative
    slack integrals. -/
lemma stage_step_identity (F : JobFamily n) {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    (p : Stage n) (hp : p.Feasible F B) (lam : ℝ) {k : ℕ} (hk : k < numRemaining B) :
    (∫ ω, teleM F B p lam k ω ∂serviceLaw F) -
        (∫ ω, teleM F B p lam (k + 1) ω ∂serviceLaw F) -
        (∫ ω, stepNet F B p lam k ω ∂serviceLaw F) =
      (∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            ((if k = 0 then famH F lam B else famG F lam (B ∪ (p.toPolicy.hist ω k).jobs)) -
              (jobR F lam (p.toPolicy.job ω k) +
                phi F (p.toPolicy.job ω k) *
                  famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))))
        else 0) ∂serviceLaw F) +
      (∫ ω, (if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
            famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
        else 0) ∂serviceLaw F) := by
  -- Helper: compute `∫` of `1_{InStage k} * exp(-γ C_k) * f(D_k, J_k)` by splitting on `J_k = j`
  have hfactor : ∀ (f : Finset (Fin n) → Fin n → ℝ),
      ∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
            f (B ∪ (p.toPolicy.hist ω k).jobs) (p.toPolicy.job ω k) else 0) ∂serviceLaw F =
      ∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (phi F (p.toPolicy.job ω k) * f (B ∪ (p.toPolicy.hist ω k).jobs) (p.toPolicy.job ω k))
        else 0) ∂serviceLaw F := by
    intro f
    set C_f : ℝ := ∑ D : Finset (Fin n), ∑ j : Fin n, |f D j|
    have hC_f : ∀ D j, |f D j| ≤ C_f := fun D j =>
      (Finset.single_le_sum (f := fun j' => |f D j'|) (fun j' _ => abs_nonneg _)
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun D' => ∑ j' : Fin n, |f D' j'|)
          (fun D' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ D))
    have hint_lhs : ∀ j : Fin n, Integrable (fun ω =>
        if p.InStage B ω k ∧ p.toPolicy.job ω k = j then
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
            f (B ∪ (p.toPolicy.hist ω k).jobs) j
        else 0) (serviceLaw F) := by
      intro j
      refine integrable_bounded_stage_term F _ ?_ C_f fun ω hω => ?_
      · exact Measurable.ite
          ((p.measurableSet_inStage B k).inter ((p.toPolicy.measurable_job k) (measurableSet_singleton j)))
          (((measurable_const.mul (p.toPolicy.measurable_completionTime k)).exp).mul
            ((measurable_of_countable (fun D => f (B ∪ D) j)).comp (p.toPolicy.measurable_hist_jobs k)))
          measurable_const
      · split_ifs
        · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp : Real.exp (-F.γ * p.toPolicy.completionTime ω k) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.completionTime_nonneg hω k])
          calc Real.exp (-F.γ * p.toPolicy.completionTime ω k) * |f _ j|
              ≤ 1 * C_f := mul_le_mul hexp (hC_f _ _) (abs_nonneg _) zero_le_one
            _ = C_f := one_mul _
        · rw [norm_zero]
          exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hint_rhs : ∀ j : Fin n, Integrable (fun ω =>
        if p.InStage B ω k ∧ p.toPolicy.job ω k = j then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (phi F j * f (B ∪ (p.toPolicy.hist ω k).jobs) j)
        else 0) (serviceLaw F) := by
      intro j
      refine integrable_bounded_stage_term F _ ?_ C_f fun ω hω => ?_
      · exact Measurable.ite
          ((p.measurableSet_inStage B k).inter ((p.toPolicy.measurable_job k) (measurableSet_singleton j)))
          (((measurable_const.mul (p.toPolicy.measurable_startTime k)).exp).mul
            (measurable_const.mul
              ((measurable_of_countable (fun D => f (B ∪ D) j)).comp (p.toPolicy.measurable_hist_jobs k))))
          measurable_const
      · split_ifs
        · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
            abs_of_pos (phi_pos F j)]
          have hexp : Real.exp (-F.γ * p.toPolicy.startTime ω k) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.startTime_nonneg hω k])
          have hphi : phi F j * |f (B ∪ (p.toPolicy.hist ω k).jobs) j| ≤ C_f := by
            calc phi F j * |f _ j| ≤ 1 * C_f :=
                  mul_le_mul (phi_lt_one F j).le (hC_f _ _) (abs_nonneg _) zero_le_one
              _ = C_f := one_mul _
          calc Real.exp (-F.γ * p.toPolicy.startTime ω k) * (phi F j * |f _ j|)
              ≤ 1 * C_f := mul_le_mul hexp hphi (mul_nonneg (phi_pos F j).le (abs_nonneg _)) zero_le_one
            _ = C_f := one_mul _
        · rw [norm_zero]
          exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsum_lhs : (fun ω => if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
            f (B ∪ (p.toPolicy.hist ω k).jobs) (p.toPolicy.job ω k) else 0) =
        fun ω => ∑ j : Fin n, if p.InStage B ω k ∧ p.toPolicy.job ω k = j then
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
            f (B ∪ (p.toPolicy.hist ω k).jobs) j else 0 := by
      funext ω
      by_cases hIn : p.InStage B ω k
      · simp [hIn]
      · simp [hIn]
    have hsum_rhs : (fun ω => if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (phi F (p.toPolicy.job ω k) * f (B ∪ (p.toPolicy.hist ω k).jobs) (p.toPolicy.job ω k))
        else 0) =
        fun ω => ∑ j : Fin n, if p.InStage B ω k ∧ p.toPolicy.job ω k = j then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (phi F j * f (B ∪ (p.toPolicy.hist ω k).jobs) j) else 0 := by
      funext ω
      by_cases hIn : p.InStage B ω k
      · simp [hIn]
      · simp [hIn]
    rw [hsum_lhs, hsum_rhs, integral_finsetSum _ (fun j _ => hint_lhs j),
        integral_finsetSum _ (fun j _ => hint_rhs j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    set g : (Fin n → ℝ) → ℝ := fun ω =>
      if p.InStage B ω k ∧ p.toPolicy.job ω k = j then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * f (B ∪ (p.toPolicy.hist ω k).jobs) j
      else 0
    have hg_indep : ∀ ω x, g (Function.update ω j x) = g ω := by
      intro ω x
      by_cases hj : j ∉ (p.toPolicy.hist ω k).jobs
      · have hhist : ∀ m ≤ k, p.toPolicy.hist (Function.update ω j x) m = p.toPolicy.hist ω m :=
          p.toPolicy.hist_update_eq_of_not_mem ω j x hj
        have hIn : p.InStage B (Function.update ω j x) k ↔ p.InStage B ω k := by
          unfold Stage.InStage
          refine and_congr_right fun _ => forall₂_congr fun l hl => ?_
          rw [hhist l (Finset.mem_Icc.1 hl).2]
        have hjob : p.toPolicy.job (Function.update ω j x) k = p.toPolicy.job ω k := by
          simp [Policy.job, hhist k le_rfl]
        have hst : p.toPolicy.startTime (Function.update ω j x) k = p.toPolicy.startTime ω k := by
          simp [Policy.startTime, hhist k le_rfl]
        simp only [g, hIn, hjob, hst, hhist k le_rfl]
      · have hj' : ¬ (j ∉ (p.toPolicy.hist (Function.update ω j x) k).jobs) := by
          rwa [p.toPolicy.hist_update_not_mem_iff]
        have hneq1 : p.toPolicy.job ω k ≠ j := by
          intro heq
          have hav := hp ω k hk
          rw [heq] at hav
          exact hj fun h => hav.1 (Finset.mem_union_right _ h)
        have hneq2 : p.toPolicy.job (Function.update ω j x) k ≠ j := by
          intro heq
          have hav := hp (Function.update ω j x) k hk
          rw [heq] at hav
          exact hj' fun h => hav.1 (Finset.mem_union_right _ h)
        simp [g, hneq1, hneq2]
    have hlhs_eq : (fun ω => if p.InStage B ω k ∧ p.toPolicy.job ω k = j then
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
            f (B ∪ (p.toPolicy.hist ω k).jobs) j else 0) =
        fun ω => Real.exp (-F.γ * ω j) * g ω := by
      funext ω
      by_cases hcond : p.InStage B ω k ∧ p.toPolicy.job ω k = j
      · dsimp only [g]
        rw [if_pos hcond, if_pos hcond, Policy.completionTime_eq, hcond.2, mul_add, Real.exp_add]
        ring
      · simp [g, hcond]
    have hrhs_eq : (fun ω => if p.InStage B ω k ∧ p.toPolicy.job ω k = j then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (phi F j * f (B ∪ (p.toPolicy.hist ω k).jobs) j) else 0) =
        fun ω => phi F j * g ω := by
      funext ω
      by_cases hcond : p.InStage B ω k ∧ p.toPolicy.job ω k = j
      · simp only [g, if_pos hcond]; ring
      · simp [g, hcond]
    rw [hlhs_eq, hrhs_eq, integral_mul_exp_of_indep F j g hg_indep, integral_const_mul]
  -- Apply `hfactor` to `f₁ D j = F.reward j + lam * F.γ⁻¹` and `f₂ D j = famG F lam (insert j D)`
  have hf1 := hfactor (fun _ j => F.reward j + lam * F.γ⁻¹)
  have hf2 := hfactor (fun D j => famG F lam (insert j D))
  -- Express `∫ M (k + 1)` via `InStage k` minus stopping slack!
  have hMsucc_eq : ∀ ω, teleM F B p lam (k + 1) ω =
      (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
      else 0) -
      (if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
      else 0) := by
    intro ω
    have hset : B ∪ (p.toPolicy.hist ω (k + 1)).jobs =
        insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs) := by
      ext a; simp [Policy.hist, Policy.job, History.jobs, or_left_comm]
    simp only [teleM, Nat.succ_ne_zero, ↓reduceIte, Policy.completionTime, Policy.startTime, hset]
    by_cases h1 : p.InStage B ω (k + 1)
    · have h0 := p.inStage_succ_imp B ω h1
      simp [h1, h0]
    · by_cases h0 : p.InStage B ω k
      · simp [h1, h0]
      · simp [h1, h0]
  -- Express `teleM k ω` uniformly using `if p.InStage B ω k`
  have hMk_eq : ∀ ω, teleM F B p lam k ω =
      if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (if k = 0 then famH F lam B else famG F lam (B ∪ (p.toPolicy.hist ω k).jobs))
      else 0 := by
    intro ω
    by_cases hk0 : k = 0
    · subst hk0
      simp [teleM, p.inStage_zero B ω hB, Policy.startTime, Policy.hist, History.elapsed]
    · simp [teleM, hk0]
  -- Helper integrability for the decomposed terms
  have hC_G : ∀ D, 0 ≤ famG F lam D := fun D => dpG_nonneg _ _ _ _ D
  set CG : ℝ := ∑ D : Finset (Fin n), famG F lam D
  have hCG_le : ∀ D, famG F lam D ≤ CG := fun D =>
    Finset.single_le_sum (fun D' _ => hC_G D') (Finset.mem_univ D)
  have hint_Gcomp : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
      else 0) (serviceLaw F) := by
    refine integrable_bounded_stage_term F _ ?_ CG fun ω hω => ?_
    · exact Measurable.ite (p.measurableSet_inStage B k)
        (((measurable_const.mul (p.toPolicy.measurable_completionTime k)).exp).mul
          ((measurable_of_countable (fun p' : Fin n × Finset (Fin n) =>
              famG F lam (insert p'.1 (B ∪ p'.2)))).comp
            ((p.toPolicy.measurable_job k).prodMk (p.toPolicy.measurable_hist_jobs k))))
        measurable_const
    · split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hC_G _))]
        have hexp : Real.exp (-F.γ * p.toPolicy.completionTime ω k) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.completionTime_nonneg hω k])
        calc _ ≤ 1 * CG := mul_le_mul hexp (hCG_le _) (hC_G _) zero_le_one
          _ = CG := one_mul _
      · rw [norm_zero]; exact Finset.sum_nonneg fun D _ => hC_G D
  have hint_stop : Integrable (fun ω => if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
      Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
      else 0) (serviceLaw F) := by
    refine integrable_bounded_stage_term F _ ?_ CG fun ω hω => ?_
    · exact Measurable.ite
        ((p.measurableSet_inStage B k).inter (p.measurableSet_inStage B (k + 1)).compl)
        (((measurable_const.mul (p.toPolicy.measurable_completionTime k)).exp).mul
          ((measurable_of_countable (fun p' : Fin n × Finset (Fin n) =>
              famG F lam (insert p'.1 (B ∪ p'.2)))).comp
            ((p.toPolicy.measurable_job k).prodMk (p.toPolicy.measurable_hist_jobs k))))
        measurable_const
    · split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hC_G _))]
        have hexp : Real.exp (-F.γ * p.toPolicy.completionTime ω k) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.completionTime_nonneg hω k])
        calc _ ≤ 1 * CG := mul_le_mul hexp (hCG_le _) (hC_G _) zero_le_one
          _ = CG := one_mul _
      · rw [norm_zero]; exact Finset.sum_nonneg fun D _ => hC_G D
  have hint_f1_lhs : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        (F.reward (p.toPolicy.job ω k) + lam * F.γ⁻¹) else 0) (serviceLaw F) := by
    set C1 := ∑ i : Fin n, |F.reward i + lam * F.γ⁻¹|
    refine integrable_bounded_stage_term F _ ?_ C1 fun ω hω => ?_
    · exact Measurable.ite (p.measurableSet_inStage B k)
        (((measurable_const.mul (p.toPolicy.measurable_completionTime k)).exp).mul
          ((measurable_of_countable (fun j => F.reward j + lam * F.γ⁻¹)).comp
            (p.toPolicy.measurable_job k)))
        measurable_const
    · split_ifs
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hexp : Real.exp (-F.γ * p.toPolicy.completionTime ω k) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.completionTime_nonneg hω k])
        have hle : |F.reward (p.toPolicy.job ω k) + lam * F.γ⁻¹| ≤ C1 :=
          Finset.single_le_sum (f := fun i => |F.reward i + lam * F.γ⁻¹|)
            (fun i _ => abs_nonneg _) (Finset.mem_univ _)
        calc _ ≤ 1 * C1 := mul_le_mul hexp hle (abs_nonneg _) zero_le_one
          _ = C1 := one_mul _
      · rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hint_f1_rhs : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (phi F (p.toPolicy.job ω k) * (F.reward (p.toPolicy.job ω k) + lam * F.γ⁻¹))
      else 0) (serviceLaw F) := by
    set C1 := ∑ i : Fin n, |F.reward i + lam * F.γ⁻¹|
    refine integrable_bounded_stage_term F _ ?_ C1 fun ω hω => ?_
    · exact Measurable.ite (p.measurableSet_inStage B k)
        (((measurable_const.mul (p.toPolicy.measurable_startTime k)).exp).mul
          ((measurable_of_countable (fun j => phi F j * (F.reward j + lam * F.γ⁻¹))).comp
            (p.toPolicy.measurable_job k)))
        measurable_const
    · split_ifs
      · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_pos (phi_pos F _)]
        have hexp : Real.exp (-F.γ * p.toPolicy.startTime ω k) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.startTime_nonneg hω k])
        have hle : |F.reward (p.toPolicy.job ω k) + lam * F.γ⁻¹| ≤ C1 :=
          Finset.single_le_sum (f := fun i => |F.reward i + lam * F.γ⁻¹|)
            (fun i _ => abs_nonneg _) (Finset.mem_univ _)
        have h2 : phi F (p.toPolicy.job ω k) * |F.reward (p.toPolicy.job ω k) + lam * F.γ⁻¹| ≤ C1 := by
          calc _ ≤ 1 * C1 := mul_le_mul (phi_lt_one F _).le hle (abs_nonneg _) zero_le_one
            _ = C1 := one_mul _
        calc _ ≤ 1 * C1 := mul_le_mul hexp h2 (mul_nonneg (phi_pos F _).le (abs_nonneg _)) zero_le_one
          _ = C1 := one_mul _
      · rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hint_st : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) * (lam * F.γ⁻¹) else 0) (serviceLaw F) := by
    refine integrable_bounded_stage_term F _ ?_ |lam * F.γ⁻¹| fun ω hω => ?_
    · exact Measurable.ite (p.measurableSet_inStage B k)
        (((measurable_const.mul (p.toPolicy.measurable_startTime k)).exp).mul measurable_const)
        measurable_const
    · split_ifs
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hexp : Real.exp (-F.γ * p.toPolicy.startTime ω k) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.startTime_nonneg hω k])
        calc _ ≤ 1 * |lam * F.γ⁻¹| := mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
          _ = |lam * F.γ⁻¹| := one_mul _
      · rw [norm_zero]; exact abs_nonneg _
  have hint_Gstart : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (phi F (p.toPolicy.job ω k) *
          famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
      else 0) (serviceLaw F) := by
    refine integrable_bounded_stage_term F _ ?_ CG fun ω hω => ?_
    · exact Measurable.ite (p.measurableSet_inStage B k)
        (((measurable_const.mul (p.toPolicy.measurable_startTime k)).exp).mul
          ((measurable_of_countable (fun p' : Fin n × Finset (Fin n) =>
              phi F p'.1 * famG F lam (insert p'.1 (B ∪ p'.2)))).comp
            ((p.toPolicy.measurable_job k).prodMk (p.toPolicy.measurable_hist_jobs k))))
        measurable_const
    · split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (phi_pos F _).le (hC_G _)))]
        have hexp : Real.exp (-F.γ * p.toPolicy.startTime ω k) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, p.toPolicy.startTime_nonneg hω k])
        have h2 : phi F (p.toPolicy.job ω k) *
            famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)) ≤ CG := by
          calc _ ≤ 1 * CG := mul_le_mul (phi_lt_one F _).le (hCG_le _) (hC_G _) zero_le_one
            _ = CG := one_mul _
        calc _ ≤ 1 * CG := mul_le_mul hexp h2 (mul_nonneg (phi_pos F _).le (hC_G _)) zero_le_one
          _ = CG := one_mul _
      · rw [norm_zero]; exact Finset.sum_nonneg fun D _ => hC_G D
  -- Rewrite `∫ stepNet` using `hf1`
  have hstepNet_eq : ∀ ω, stepNet F B p lam k ω =
      (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          (F.reward (p.toPolicy.job ω k) + lam * F.γ⁻¹) else 0) -
      (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * (lam * F.γ⁻¹) else 0) := by
    intro ω
    unfold stepNet
    split_ifs <;> ring
  have hstepNet_int : ∫ ω, stepNet F B p lam k ω ∂serviceLaw F =
      ∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobR F lam (p.toPolicy.job ω k) else 0)
        ∂serviceLaw F := by
    rw [show stepNet F B p lam k = _ from funext hstepNet_eq,
        integral_sub hint_f1_lhs hint_st, hf1, ← integral_sub hint_f1_rhs hint_st]
    congr 1 with ω
    split_ifs
    · simp only [jobR, jobA, jobC]; ring
    · ring
  have hMsucc_int : ∫ ω, teleM F B p lam (k + 1) ω ∂serviceLaw F =
      (∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (phi F (p.toPolicy.job ω k) *
            famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
        else 0) ∂serviceLaw F) -
      (∫ ω, (if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
        else 0) ∂serviceLaw F) := by
    rw [show teleM F B p lam (k + 1) = _ from funext hMsucc_eq,
        integral_sub hint_Gcomp hint_stop, hf2]
  have hint_jobR : Integrable (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobR F lam (p.toPolicy.job ω k) else 0)
      (serviceLaw F) := by
    have heq : (fun ω => if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobR F lam (p.toPolicy.job ω k) else 0) =
        fun ω =>
          (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (phi F (p.toPolicy.job ω k) * (F.reward (p.toPolicy.job ω k) + lam * F.γ⁻¹)) else 0) -
          (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.startTime ω k) * (lam * F.γ⁻¹) else 0) := by
      funext ω; split_ifs <;> simp [jobR, jobA, jobC] <;> ring
    rw [heq]
    exact hint_f1_rhs.sub hint_st
  rw [hMsucc_int, hstepNet_int]
  have hcomb :
      (∫ ω, teleM F B p lam k ω ∂serviceLaw F) -
        ((∫ ω, (if p.InStage B ω k then
            Real.exp (-F.γ * p.toPolicy.startTime ω k) *
              (phi F (p.toPolicy.job ω k) *
                famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
            else 0) ∂serviceLaw F) -
          (∫ ω, (if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
            Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
              famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
            else 0) ∂serviceLaw F)) -
        (∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobR F lam (p.toPolicy.job ω k) else 0)
          ∂serviceLaw F) =
      ((∫ ω, teleM F B p lam k ω ∂serviceLaw F) -
        (∫ ω, (if p.InStage B ω k then
            Real.exp (-F.γ * p.toPolicy.startTime ω k) *
              (phi F (p.toPolicy.job ω k) *
                famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
            else 0) ∂serviceLaw F) -
        (∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * jobR F lam (p.toPolicy.job ω k) else 0)
          ∂serviceLaw F)) +
      (∫ ω, (if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
        else 0) ∂serviceLaw F) := by ring
  rw [hcomb]
  congr 1
  have hsub1 : Integrable (fun ω => teleM F B p lam k ω -
      (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (phi F (p.toPolicy.job ω k) *
            famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
      else 0)) (serviceLaw F) :=
    (integrable_teleM F B p lam k).sub hint_Gstart
  rw [← integral_sub (integrable_teleM F B p lam k) hint_Gstart,
      ← integral_sub hsub1 hint_jobR]
  congr 1 with ω
  rw [hMk_eq ω]
  split_ifs <;> ring

/-- Full telescoping identity for `famH F lam B - (p.reward F B - lam * p.time F B)`. -/
lemma stage_telescoping (F : JobFamily n) {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    (p : Stage n) (hp : p.Feasible F B) (lam : ℝ) :
    famH F lam B - (p.reward F B - lam * p.time F B) =
      ∑ k ∈ Finset.range (numRemaining B),
        ((∫ ω, (if p.InStage B ω k then
            Real.exp (-F.γ * p.toPolicy.startTime ω k) *
              ((if k = 0 then famH F lam B else famG F lam (B ∪ (p.toPolicy.hist ω k).jobs)) -
                (jobR F lam (p.toPolicy.job ω k) +
                  phi F (p.toPolicy.job ω k) *
                    famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))))
          else 0) ∂serviceLaw F) +
        (∫ ω, (if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
            Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
              famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
          else 0) ∂serviceLaw F)) := by
  have hsum_step :
      ∑ k ∈ Finset.range (numRemaining B),
        ((∫ ω, teleM F B p lam k ω ∂serviceLaw F) -
         (∫ ω, teleM F B p lam (k + 1) ω ∂serviceLaw F) -
         (∫ ω, stepNet F B p lam k ω ∂serviceLaw F)) =
      ∑ k ∈ Finset.range (numRemaining B),
        ((∫ ω, (if p.InStage B ω k then
            Real.exp (-F.γ * p.toPolicy.startTime ω k) *
              ((if k = 0 then famH F lam B else famG F lam (B ∪ (p.toPolicy.hist ω k).jobs)) -
                (jobR F lam (p.toPolicy.job ω k) +
                  phi F (p.toPolicy.job ω k) *
                    famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))))
          else 0) ∂serviceLaw F) +
        (∫ ω, (if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
            Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
              famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
          else 0) ∂serviceLaw F)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    exact stage_step_identity F hB p hp lam (Finset.mem_range.1 hk)
  rw [← hsum_step]
  have htele :
      ∑ k ∈ Finset.range (numRemaining B),
        ((∫ ω, teleM F B p lam k ω ∂serviceLaw F) -
         (∫ ω, teleM F B p lam (k + 1) ω ∂serviceLaw F)) =
      (∫ ω, teleM F B p lam 0 ω ∂serviceLaw F) -
        (∫ ω, teleM F B p lam (numRemaining B) ω ∂serviceLaw F) := by
    have := Finset.sum_range_sub' (fun k => ∫ ω, teleM F B p lam k ω ∂serviceLaw F) (numRemaining B)
    simpa using this
  have hM0 : ∫ ω, teleM F B p lam 0 ω ∂serviceLaw F = famH F lam B := by
    simp [teleM, probReal_univ]
  have hMm : ∫ ω, teleM F B p lam (numRemaining B) ω ∂serviceLaw F = 0 := by
    have hpos : 0 < numRemaining B := (p.inStage_zero B (fun _ => 0) hB).1
    have hzero : teleM F B p lam (numRemaining B) = 0 := by
      funext ω
      simp [teleM, hpos.ne', Stage.InStage]
    simp [hzero]
  have hnet : ∑ k ∈ Finset.range (numRemaining B), (∫ ω, stepNet F B p lam k ω ∂serviceLaw F) =
      p.reward F B - lam * p.time F B := by
    unfold Stage.reward Stage.time
    rw [integral_finsetSum _ (fun k _ => integrable_stepReward F B p k),
        integral_finsetSum _ (fun k _ => integrable_stepTime F B p k),
        Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul, ← integral_sub (integrable_stepReward F B p k)
      ((integrable_stepTime F B p k).const_mul lam)]
    congr 1 with ω
    unfold stepNet
    split_ifs <;> ring
  rw [Finset.sum_sub_distrib, htele, hM0, hMm, sub_zero, hnet]

lemma stage_reward_sub_mul_time_le_famH (F : JobFamily n) {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    (p : Stage n) (hp : p.Feasible F B) (lam : ℝ) :
    p.reward F B - lam * p.time F B ≤ famH F lam B := by
  have hdiff := stage_telescoping F hB p hp lam
  have hnn : 0 ≤ famH F lam B - (p.reward F B - lam * p.time F B) := by
    rw [hdiff]
    refine Finset.sum_nonneg fun k hk => add_nonneg ?_ ?_
    · refine integral_nonneg fun ω => ?_
      split_ifs with hIn hk0
      · refine mul_nonneg (Real.exp_pos _).le ?_
        subst hk0
        have hav : p.toPolicy.job ω 0 ∈ availSet F.prec B := by
          have := hp ω 0 (Finset.mem_range.1 hk)
          simpa [Policy.hist, History.jobs, mem_availSet, IsAvailable] using this
        have hle := le_dpH F.prec F.prec_acyclic (jobR F lam) (phi F) hav
        simpa [Policy.hist, History.jobs, famH, famG] using sub_nonneg.2 hle
      · refine mul_nonneg (Real.exp_pos _).le ?_
        have hav : p.toPolicy.job ω k ∈ availSet F.prec (B ∪ (p.toPolicy.hist ω k).jobs) := by
          have := hp ω k (Finset.mem_range.1 hk)
          simpa [mem_availSet, IsAvailable] using this
        exact sub_nonneg.2 (le_dpG F.prec F.prec_acyclic (jobR F lam) (phi F) hav)
      · exact le_rfl
    · refine integral_nonneg fun ω => ?_
      split_ifs
      · exact mul_nonneg (Real.exp_pos _).le (dpG_nonneg _ _ _ _ _)
      · exact le_rfl
  linarith

lemma stage_next_maximizer_of_eq_famH (F : JobFamily n) {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    (p : Stage n) (hp : p.Feasible F B) (lam : ℝ)
    (heq : p.reward F B - lam * p.time F B = famH F lam B) :
    jobR F lam (p.next []) + phi F (p.next []) * famG F lam (insert (p.next []) B) =
      famH F lam B := by
  have hdiff := stage_telescoping F hB p hp lam
  rw [heq, sub_self] at hdiff
  have h0_mem : 0 ∈ Finset.range (numRemaining B) :=
    Finset.mem_range.2 (p.inStage_zero B (fun _ => 0) hB).1
  have hterm_nn : ∀ k ∈ Finset.range (numRemaining B),
      0 ≤ (∫ ω, (if p.InStage B ω k then
            Real.exp (-F.γ * p.toPolicy.startTime ω k) *
              ((if k = 0 then famH F lam B else famG F lam (B ∪ (p.toPolicy.hist ω k).jobs)) -
                (jobR F lam (p.toPolicy.job ω k) +
                  phi F (p.toPolicy.job ω k) *
                    famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))))
          else 0) ∂serviceLaw F) +
        (∫ ω, (if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
            Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
              famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
          else 0) ∂serviceLaw F) := by
    intro k hk
    refine add_nonneg (integral_nonneg fun ω => ?_) (integral_nonneg fun ω => ?_)
    · split_ifs with hIn hk0
      · subst hk0
        have hav : p.toPolicy.job ω 0 ∈ availSet F.prec B := by
          simpa [Policy.hist, History.jobs, mem_availSet, IsAvailable] using hp ω 0 (Finset.mem_range.1 hk)
        exact mul_nonneg (Real.exp_pos _).le (by
          simpa [Policy.hist, History.jobs, famH, famG] using
            sub_nonneg.2 (le_dpH F.prec F.prec_acyclic (jobR F lam) (phi F) hav))
      · have hav : p.toPolicy.job ω k ∈ availSet F.prec (B ∪ (p.toPolicy.hist ω k).jobs) := by
          simpa [mem_availSet, IsAvailable] using hp ω k (Finset.mem_range.1 hk)
        exact mul_nonneg (Real.exp_pos _).le
          (sub_nonneg.2 (le_dpG F.prec F.prec_acyclic (jobR F lam) (phi F) hav))
      · exact le_rfl
    · split_ifs
      · exact mul_nonneg (Real.exp_pos _).le (dpG_nonneg _ _ _ _ _)
      · exact le_rfl
  have h0_eq := (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).1 hdiff.symm 0 h0_mem
  have hstop_nn : 0 ≤ ∫ ω, (if p.InStage B ω 0 ∧ ¬ p.InStage B ω 1 then
      Real.exp (-F.γ * p.toPolicy.completionTime ω 0) *
        famG F lam (insert (p.toPolicy.job ω 0) (B ∪ (p.toPolicy.hist ω 0).jobs))
      else 0) ∂serviceLaw F := by
    refine integral_nonneg fun ω => ?_
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (dpG_nonneg _ _ _ _ _)
    · exact le_rfl
  have hfirst_nn : 0 ≤ ∫ ω, (if p.InStage B ω 0 then
      Real.exp (-F.γ * p.toPolicy.startTime ω 0) *
        (famH F lam B -
          (jobR F lam (p.toPolicy.job ω 0) +
            phi F (p.toPolicy.job ω 0) *
              famG F lam (insert (p.toPolicy.job ω 0) (B ∪ (p.toPolicy.hist ω 0).jobs))))
      else 0) ∂serviceLaw F := by
    refine integral_nonneg fun ω => ?_
    split_ifs
    · have hav : p.toPolicy.job ω 0 ∈ availSet F.prec B := by
        simpa [Policy.hist, History.jobs, mem_availSet, IsAvailable] using
          hp ω 0 (Finset.mem_range.1 h0_mem)
      exact mul_nonneg (Real.exp_pos _).le (by
        simpa [Policy.hist, History.jobs, famH, famG] using
          sub_nonneg.2 (le_dpH F.prec F.prec_acyclic (jobR F lam) (phi F) hav))
    · exact le_rfl
  have hfirst_zero : ∫ ω, (if p.InStage B ω 0 then
      Real.exp (-F.γ * p.toPolicy.startTime ω 0) *
        (famH F lam B -
          (jobR F lam (p.toPolicy.job ω 0) +
            phi F (p.toPolicy.job ω 0) *
              famG F lam (insert (p.toPolicy.job ω 0) (B ∪ (p.toPolicy.hist ω 0).jobs))))
      else 0) ∂serviceLaw F = 0 := by
    simp only [↓reduceIte] at h0_eq
    linarith
  have hconst : (fun ω : Fin n → ℝ => if p.InStage B ω 0 then
      Real.exp (-F.γ * p.toPolicy.startTime ω 0) *
        (famH F lam B -
          (jobR F lam (p.toPolicy.job ω 0) +
            phi F (p.toPolicy.job ω 0) *
              famG F lam (insert (p.toPolicy.job ω 0) (B ∪ (p.toPolicy.hist ω 0).jobs))))
      else 0) =
      fun _ => famH F lam B -
        (jobR F lam (p.next []) + phi F (p.next []) * famG F lam (insert (p.next []) B)) := by
    funext ω
    simp [p.inStage_zero B ω hB, Policy.startTime, Policy.hist, Policy.job, History.elapsed,
      History.jobs]
  rw [hconst, integral_const, smul_eq_mul, probReal_univ, one_mul] at hfirst_zero
  linarith

lemma stage_eq_famH_of_greedy (F : JobFamily n) {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    (p : Stage n) (hp : p.Feasible F B) (lam : ℝ)
    (h0 : jobR F lam (p.next []) + phi F (p.next []) * famG F lam (insert (p.next []) B) =
      famH F lam B)
    (hstep : ∀ ω k, 1 ≤ k → k < numRemaining B → p.InStage B ω k →
      jobR F lam (p.toPolicy.job ω k) +
        phi F (p.toPolicy.job ω k) *
          famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)) =
        famG F lam (B ∪ (p.toPolicy.hist ω k).jobs))
    (hstop : ∀ ω k, k < numRemaining B → p.InStage B ω k → ¬ p.InStage B ω (k + 1) →
      famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)) = 0) :
    p.reward F B - lam * p.time F B = famH F lam B := by
  have hdiff := stage_telescoping F hB p hp lam
  suffices hzero : famH F lam B - (p.reward F B - lam * p.time F B) = 0 by linarith
  rw [hdiff]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkr : k < numRemaining B := Finset.mem_range.1 hk
  have h1 : (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        ((if k = 0 then famH F lam B else famG F lam (B ∪ (p.toPolicy.hist ω k).jobs)) -
          (jobR F lam (p.toPolicy.job ω k) +
            phi F (p.toPolicy.job ω k) *
              famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))))
      else 0) = 0 := by
    funext ω
    simp only [Pi.zero_apply]
    split_ifs with hIn hk0
    · subst hk0
      simp only [Policy.job, Policy.hist, History.jobs, List.map_nil, List.toFinset_nil,
        Finset.union_empty]
      rw [h0, sub_self, mul_zero]
    · rw [hstep ω k (Nat.one_le_iff_ne_zero.2 hk0) hkr hIn, sub_self, mul_zero]
    · rfl
  have h2 : (fun ω => if p.InStage B ω k ∧ ¬ p.InStage B ω (k + 1) then
      Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        famG F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs))
      else 0) = 0 := by
    funext ω
    simp only [Pi.zero_apply]
    split_ifs with hcond
    · rw [hstop ω k hkr hcond.1 hcond.2, mul_zero]
    · rfl
  rw [h1, h2]
  simp

lemma stage_time_pos (F : JobFamily n) {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    (p : Stage n) : 0 < p.time F B := by
  unfold Stage.time
  rw [integral_finsetSum _ (fun k _ => integrable_stepTime F B p k)]
  have h0_mem : 0 ∈ Finset.range (numRemaining B) :=
    Finset.mem_range.2 (p.inStage_zero B (fun _ => 0) hB).1
  have hnn : ∀ k ∈ Finset.range (numRemaining B),
      0 ≤ ∫ ω, (if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k)) else 0) ∂serviceLaw F := by
    intro k _
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_pos_serviceLaw F] with ω hω
    split_ifs
    · refine mul_nonneg (inv_pos.2 F.γ_pos).le (sub_nonneg.2 (Real.exp_le_exp.2 ?_))
      rw [Policy.completionTime_eq]
      nlinarith [F.γ_pos, hω (p.toPolicy.job ω k)]
    · exact le_rfl
  have h0_val : ∫ ω, (if p.InStage B ω 0 then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω 0) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω 0)) else 0) ∂serviceLaw F =
      jobC F (p.next []) := by
    have heq : (fun ω => if p.InStage B ω 0 then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω 0) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω 0)) else 0) =
        fun ω => F.γ⁻¹ * (1 - Real.exp (-F.γ * ω (p.next [])) * 1) := by
      funext ω
      simp [p.inStage_zero B ω hB, Policy.startTime, Policy.completionTime_eq,
        Policy.hist, Policy.job, History.elapsed]
    rw [heq, integral_const_mul]
    have hexp_int : Integrable (fun ω : Fin n → ℝ => Real.exp (-F.γ * ω (p.next [])))
        (serviceLaw F) := by
      refine integrable_bounded_stage_term F _
        ((measurable_const.mul (measurable_pi_apply _)).exp) 1 fun ω hω => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith [F.γ_pos, hω (p.next [])])
    have hexp_val : ∫ ω, Real.exp (-F.γ * ω (p.next [])) ∂serviceLaw F = phi F (p.next []) := by
      simpa [probReal_univ] using integral_mul_exp_of_indep F (p.next []) (fun _ => 1) (fun _ _ => rfl)
    simp only [mul_one]
    rw [integral_sub (integrable_const 1) hexp_int, integral_const, smul_eq_mul, mul_one,
        probReal_univ, hexp_val]
    rfl
  have hle : jobC F (p.next []) ≤ ∑ k ∈ Finset.range (numRemaining B),
      ∫ ω, (if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k)) else 0) ∂serviceLaw F := by
    rw [← h0_val]
    exact Finset.single_le_sum hnn h0_mem
  exact lt_of_lt_of_le (jobC_pos F (p.next [])) hle

/-! ### Section 4: Characterization of `familyIndex F B` -/

lemma continuous_finset_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => s.sup' hs (fun i => f i x)) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hf a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    have heq : (fun x => (Finset.cons a s ha).sup' (Finset.cons_nonempty ha) (fun i => f i x)) =
        fun x => max (f a x) (s.sup' hs (fun i => f i x)) := by
      funext x; rw [Finset.sup'_cons]
    rw [heq]
    exact (hf a (Finset.mem_cons_self a s)).max
      (ih fun i hi => hf i (Finset.mem_cons_of_mem hi))

lemma famG_continuous (F : JobFamily n) (D : Finset (Fin n)) :
    Continuous (fun lam : ℝ => famG F lam D) := by
  by_cases hD : D = Finset.univ
  · subst hD
    simp only [famG, dpG_univ]
    exact continuous_const
  · rw [show (fun lam => famG F lam D) = fun lam => max 0 (famH F lam D) from
      funext fun lam => dpG_eq_max _ _ _ _ D]
    refine continuous_const.max ?_
    rw [show (fun lam => famH F lam D) = fun lam =>
        (availSet F.prec D).sup' (availSet_nonempty F.prec F.prec_acyclic hD)
          (fun j => jobR F lam j + phi F j * famG F lam (insert j D)) from
      funext fun lam => dpH_eq_sup' _ _ _ _ hD]
    refine continuous_finset_sup' (availSet_nonempty F.prec F.prec_acyclic hD) fun j hj => ?_
    have : n - (insert j D).card < n - D.card :=
      card_sub_insert_lt ((mem_availSet F.prec).1 hj).1
    have hR : Continuous (fun lam : ℝ => jobR F lam j) :=
      continuous_const.sub (continuous_id.mul continuous_const)
    exact hR.add (continuous_const.mul (famG_continuous F (insert j D)))
termination_by n - D.card

lemma famH_continuous (F : JobFamily n) (D : Finset (Fin n)) :
    Continuous (fun lam : ℝ => famH F lam D) := by
  by_cases hD : D = Finset.univ
  · subst hD
    simp only [famH, dpH_univ]
    exact continuous_const
  · rw [show (fun lam => famH F lam D) = fun lam =>
        (availSet F.prec D).sup' (availSet_nonempty F.prec F.prec_acyclic hD)
          (fun j => jobR F lam j + phi F j * famG F lam (insert j D)) from
      funext fun lam => dpH_eq_sup' _ _ _ _ hD]
    refine continuous_finset_sup' (availSet_nonempty F.prec F.prec_acyclic hD) fun j _ => ?_
    exact (continuous_const.sub (continuous_id.mul continuous_const)).add
      (continuous_const.mul (famG_continuous F (insert j D)))

lemma famH_zero_pos (F : JobFamily n) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    0 < famH F 0 D := by
  obtain ⟨j, hj⟩ := availSet_nonempty F.prec F.prec_acyclic hD
  have h1 : 0 < jobR F 0 j + phi F j * famG F 0 (insert j D) := by
    have hR : jobR F 0 j = jobA F j := by simp [jobR]
    rw [hR]
    exact add_pos_of_pos_of_nonneg (jobA_pos F j)
      (mul_nonneg (phi_pos F j).le (dpG_nonneg _ _ _ _ _))
  exact lt_of_lt_of_le h1 (le_dpH F.prec F.prec_acyclic (jobR F 0) (phi F) hj)

lemma famH_neg_of_large (F : JobFamily n) (lam : ℝ)
    (hlam : ∀ j : Fin n, jobR F lam j < 0) (D : Finset (Fin n)) :
    (D ≠ Finset.univ → famH F lam D < 0) ∧ famG F lam D = 0 := by
  by_cases hD : D = Finset.univ
  · subst hD
    exact ⟨fun h => absurd rfl h, dpG_univ _ _ _ _⟩
  · have hH : famH F lam D < 0 := by
      rw [famH, dpH_eq_sup' _ _ _ _ hD]
      rw [Finset.sup'_lt_iff]
      intro j hj
      have : n - (insert j D).card < n - D.card :=
        card_sub_insert_lt ((mem_availSet F.prec).1 hj).1
      have hG0 := (famH_neg_of_large F lam hlam (insert j D)).2
      rw [show dpG F.prec F.prec_acyclic (jobR F lam) (phi F) (insert j D) = 0 from hG0,
          mul_zero, add_zero]
      exact hlam j
    refine ⟨fun _ => hH, ?_⟩
    rw [famG, dpG_eq_max]
    exact max_eq_left hH.le
termination_by n - D.card

lemma exists_famH_eq_zero (F : JobFamily n) {B : Finset (Fin n)} (hB : B ≠ Finset.univ) :
    ∃ lam : ℝ, famH F lam B = 0 := by
  have h0 : 0 < famH F 0 B := famH_zero_pos F hB
  set Λ : ℝ := 1 + ∑ i : Fin n, jobA F i / jobC F i
  have hΛpos : 0 ≤ Λ := by
    refine add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => div_nonneg (jobA_pos F i).le (jobC_pos F i).le)
  have hΛneg : famH F Λ B < 0 := by
    refine (famH_neg_of_large F Λ (fun j => ?_) B).1 hB
    have hle : jobA F j / jobC F j ≤ ∑ i : Fin n, jobA F i / jobC F i :=
      Finset.single_le_sum (fun i _ => div_nonneg (jobA_pos F i).le (jobC_pos F i).le) (Finset.mem_univ j)
    have hgt : jobA F j / jobC F j < Λ := by linarith
    have hmul : jobA F j < Λ * jobC F j := (div_lt_iff₀ (jobC_pos F j)).1 hgt
    unfold jobR
    linarith
  have hmem : (0 : ℝ) ∈ Set.Icc (famH F Λ B) (famH F 0 B) := ⟨hΛneg.le, h0.le⟩
  obtain ⟨lam, _, hlam⟩ :=
    intermediate_value_Icc' hΛpos (famH_continuous F B).continuousOn hmem
  exact ⟨lam, hlam⟩

open Classical in
/-- Canonical `famH`-maximizing job at completed set `D` (or `dummy` if `D = univ`). -/
noncomputable def canonNext (F : JobFamily n) (dummy : Fin n) (lam : ℝ)
    (D : Finset (Fin n)) : Fin n :=
  if hD : D = Finset.univ then dummy
  else Classical.choose (exists_dpH_maximizer F.prec F.prec_acyclic (jobR F lam) (phi F) hD)

lemma canonNext_spec (F : JobFamily n) (dummy : Fin n) (lam : ℝ)
    {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    canonNext F dummy lam D ∈ availSet F.prec D ∧
      jobR F lam (canonNext F dummy lam D) +
        phi F (canonNext F dummy lam D) * famG F lam (insert (canonNext F dummy lam D) D) =
      famH F lam D := by
  classical
  simp only [canonNext, dif_neg hD]
  exact Classical.choose_spec (exists_dpH_maximizer F.prec F.prec_acyclic (jobR F lam) (phi F) hD)

open Classical in
/-- Canonical deterministic `famH`-optimal stage from `B` at threshold `lam`. -/
noncomputable def canonStage (F : JobFamily n) (dummy : Fin n) (B : Finset (Fin n)) (lam : ℝ) :
    Stage n where
  next l := canonNext F dummy lam (B ∪ l.jobs)
  measurable_next k := by
    have h1 : Measurable (fun u : Fin k → Fin n × ℝ => fun i => (u i).1) :=
      measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
    have h2 : Measurable (fun v : Fin k → Fin n => canonNext F dummy lam (B ∪ (List.ofFn v).toFinset)) :=
      measurable_of_countable _
    have heq : (fun u : Fin k → Fin n × ℝ => canonNext F dummy lam (B ∪ History.jobs (List.ofFn u))) =
        (fun v : Fin k → Fin n => canonNext F dummy lam (B ∪ (List.ofFn v).toFinset)) ∘
          fun u i => (u i).1 := by
      funext u; simp [History.jobs, List.map_ofFn]; rfl
    rw [heq]; exact h2.comp h1
  stop l := decide (B ∪ l.jobs = Finset.univ ∨ famH F lam (B ∪ l.jobs) ≤ 0)
  measurable_stop k := by
    have h1 : Measurable (fun u : Fin k → Fin n × ℝ => fun i => (u i).1) :=
      measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
    have h2 : Measurable (fun v : Fin k → Fin n =>
        decide (B ∪ (List.ofFn v).toFinset = Finset.univ ∨
          famH F lam (B ∪ (List.ofFn v).toFinset) ≤ 0)) :=
      measurable_of_countable _
    have heq : (fun u : Fin k → Fin n × ℝ =>
        decide (B ∪ History.jobs (List.ofFn u) = Finset.univ ∨
          famH F lam (B ∪ History.jobs (List.ofFn u)) ≤ 0)) =
        (fun v : Fin k → Fin n =>
          decide (B ∪ (List.ofFn v).toFinset = Finset.univ ∨
            famH F lam (B ∪ (List.ofFn v).toFinset) ≤ 0)) ∘ fun u i => (u i).1 := by
      funext u; simp [History.jobs, List.map_ofFn]; rfl
    rw [heq]; exact h2.comp h1

lemma canonStage_feasible (F : JobFamily n) (dummy : Fin n) (B : Finset (Fin n)) (lam : ℝ) :
    (canonStage F dummy B lam).Feasible F B := by
  intro ω k hk
  -- Prove by strong induction on `k` that `(B ∪ hist.jobs).card = B.card + k` and available
  suffices h : ∀ m ≤ numRemaining B,
      (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω m).jobs).card = B.card + m ∧
      (m < numRemaining B →
        IsAvailable F (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω m).jobs)
          ((canonStage F dummy B lam).toPolicy.job ω m)) from
    (h k hk.le).2 hk
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨by simp [Policy.hist, History.jobs], fun h0 => ?_⟩
    have hB : B ≠ Finset.univ := by
      intro heq; subst heq; simp [numRemaining] at h0
    have hspec := (canonNext_spec F dummy lam hB).1
    simpa [canonStage, Policy.job, Policy.hist, History.jobs, mem_availSet, IsAvailable] using hspec
  | succ m ih =>
    intro hle
    have hm_lt : m < numRemaining B := Nat.lt_of_succ_le hle
    obtain ⟨hcard, hav⟩ := ih hm_lt.le
    have hav_m := hav hm_lt
    have hset : B ∪ ((canonStage F dummy B lam).toPolicy.hist ω (m + 1)).jobs =
        insert ((canonStage F dummy B lam).toPolicy.job ω m)
          (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω m).jobs) := by
      ext a; simp [Policy.hist, Policy.job, History.jobs, or_left_comm]
    have hcard' : (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω (m + 1)).jobs).card =
        B.card + (m + 1) := by
      rw [hset, Finset.card_insert_of_notMem hav_m.1, hcard]
      omega
    refine ⟨hcard', fun hlt => ?_⟩
    have hne : B ∪ ((canonStage F dummy B lam).toPolicy.hist ω (m + 1)).jobs ≠ Finset.univ := by
      intro heq
      rw [heq, Finset.card_univ, Fintype.card_fin] at hcard'
      have hBle : B.card ≤ n := by simpa using Finset.card_le_univ B
      simp only [numRemaining] at hlt
      omega
    have hspec := (canonNext_spec F dummy lam hne).1
    simpa [canonStage, Policy.job, mem_availSet, IsAvailable] using hspec

lemma famH_familyIndex_eq_zero (F : JobFamily n) (dummy : Fin n)
    {B : Finset (Fin n)} (hB : B ≠ Finset.univ) :
    famH F (familyIndex F B) B = 0 := by
  obtain ⟨lam, hlam⟩ := exists_famH_eq_zero F hB
  suffices hidx : familyIndex F B = lam by rw [hidx, hlam]
  unfold familyIndex
  set S : Set ℝ := {x : ℝ | ∃ p : Stage n, p.Feasible F B ∧ x = p.ratio F B}
  have hcanon_feas : (canonStage F dummy B lam).Feasible F B := canonStage_feasible F dummy B lam
  have hcanon_eq : (canonStage F dummy B lam).reward F B -
      lam * (canonStage F dummy B lam).time F B = famH F lam B := by
    refine stage_eq_famH_of_greedy F hB (canonStage F dummy B lam) hcanon_feas lam ?_ ?_ ?_
    · simpa [canonStage, History.jobs] using (canonNext_spec F dummy lam hB).2
    · intro ω k hk1 hkr hIn
      have hstop_false : (canonStage F dummy B lam).stop
          ((canonStage F dummy B lam).toPolicy.hist ω k) = false :=
        hIn.2 k (Finset.mem_Icc.2 ⟨hk1, le_rfl⟩)
      have hstop_def : (canonStage F dummy B lam).stop ((canonStage F dummy B lam).toPolicy.hist ω k) =
          decide (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω k).jobs = Finset.univ ∨
            famH F lam (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω k).jobs) ≤ 0) := rfl
      rw [hstop_def, decide_eq_false_iff_not, not_or, not_le] at hstop_false
      have hG : famG F lam (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω k).jobs) =
          famH F lam (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω k).jobs) := by
        rw [famG_eq_max, max_eq_right hstop_false.2.le]
      rw [hG]
      exact (canonNext_spec F dummy lam hstop_false.1).2
    · intro ω k hkr hIn hnotIn
      have hset : insert ((canonStage F dummy B lam).toPolicy.job ω k)
          (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω k).jobs) =
          B ∪ ((canonStage F dummy B lam).toPolicy.hist ω (k + 1)).jobs := by
        ext a; simp [Policy.hist, Policy.job, History.jobs, or_left_comm]
      rw [hset]
      by_cases hlast : k + 1 < numRemaining B
      · have hstop_true : (canonStage F dummy B lam).stop
            ((canonStage F dummy B lam).toPolicy.hist ω (k + 1)) = true := by
          by_contra hf
          have hbf : (canonStage F dummy B lam).stop
              ((canonStage F dummy B lam).toPolicy.hist ω (k + 1)) = false :=
            Bool.eq_false_iff.2 hf
          apply hnotIn
          refine ⟨hlast, fun l hl => ?_⟩
          rcases (Finset.mem_Icc.1 hl).2.eq_or_lt with rfl | hlt
          · exact hbf
          · exact hIn.2 l (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hl).1, Nat.lt_succ_iff.1 hlt⟩)
        have hstop_def : (canonStage F dummy B lam).stop
            ((canonStage F dummy B lam).toPolicy.hist ω (k + 1)) =
            decide (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω (k + 1)).jobs = Finset.univ ∨
              famH F lam (B ∪ ((canonStage F dummy B lam).toPolicy.hist ω (k + 1)).jobs) ≤ 0) := rfl
        rw [hstop_def, decide_eq_true_eq] at hstop_true
        rcases hstop_true with huniv | hle0
        · rw [huniv]; exact famG_univ F lam
        · rw [famG_eq_max, max_eq_left hle0]
      · have heq : k + 1 = numRemaining B := by omega
        rw [heq, Stage.union_hist_jobs_eq_univ F B _ hcanon_feas ω]
        exact famG_univ F lam
  have hcanon_ratio : (canonStage F dummy B lam).ratio F B = lam := by
    have htime := stage_time_pos F hB (canonStage F dummy B lam)
    unfold Stage.ratio
    rw [div_eq_iff htime.ne']
    linarith
  have hmem : lam ∈ S := ⟨canonStage F dummy B lam, hcanon_feas, hcanon_ratio.symm⟩
  have hub : ∀ x ∈ S, x ≤ lam := by
    rintro x ⟨p, hp, rfl⟩
    have htime := stage_time_pos F hB p
    have hle := stage_reward_sub_mul_time_le_famH F hB p hp lam
    rw [hlam] at hle
    unfold Stage.ratio
    rw [div_le_iff₀ htime]
    linarith
  exact le_antisymm (csSup_le ⟨lam, hmem⟩ hub) (le_csSup ⟨lam, hub⟩ hmem)

lemma isFIStarStage_next_maximizer (F : JobFamily n) (dummy : Fin n)
    {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    {p : Stage n} (hp : IsFIStarStage F B p) :
    p.next [] ∈ availSet F.prec B ∧
      jobR F (familyIndex F B) (p.next []) +
        phi F (p.next []) * famG F (familyIndex F B) (insert (p.next []) B) =
      famH F (familyIndex F B) B := by
  have h0_lt : 0 < numRemaining B := (p.inStage_zero B (fun _ => 0) hB).1
  have hav : p.next [] ∈ availSet F.prec B := by
    simpa [Policy.job, Policy.hist, History.jobs, mem_availSet, IsAvailable] using
      hp.1 (fun _ => 0) 0 h0_lt
  refine ⟨hav, ?_⟩
  have hH0 := famH_familyIndex_eq_zero F dummy hB
  have htime := stage_time_pos F hB p
  have heq : p.reward F B - familyIndex F B * p.time F B = famH F (familyIndex F B) B := by
    have hrat : p.reward F B / p.time F B = familyIndex F B := hp.2
    rw [div_eq_iff htime.ne'] at hrat
    linarith
  exact stage_next_maximizer_of_eq_famH F hB p hp.1 (familyIndex F B) heq

/-! ### Section 5: Construction of `ρ` and Main Proof -/

open Classical in
/-- Given a policy `π`, construct the FI* stage rule `ρ h` from history `h`:
    follow `π` after `h` whenever `π` picks an available `famH`-maximizing job,
    otherwise fall back to `canonNext`, and stop as soon as `famH ≤ 0` or all jobs are done. -/
noncomputable def fiStageRule (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n)
    (h : History n) : Stage n :=
  let B := A ∪ h.jobs
  let lam := familyIndex F B
  { next := fun l =>
      let D := B ∪ l.jobs
      let j := π.next (h ++ l)
      if IsAvailable F D j ∧
          jobR F lam j + phi F j * famG F lam (insert j D) = famH F lam D then
        j
      else
        canonNext F (π.next []) lam D
    measurable_next := fun k => by
      -- Map `v : Fin k → Fin n × ℝ` to `u : Fin (h.length + k) → Fin n × ℝ` representing `h ++ ofFn v`
      let cat : (Fin k → Fin n × ℝ) → (Fin (h.length + k) → Fin n × ℝ) := fun v i =>
        if hi : i.val < h.length then h.get ⟨i.val, hi⟩
        else v ⟨i.val - h.length, by omega⟩
      have hcat_meas : Measurable cat := by
        rw [measurable_pi_iff]
        intro i
        by_cases hi : i.val < h.length
        · simp only [cat, dif_pos hi]; exact measurable_const
        · simp only [cat, dif_neg hi]; exact measurable_pi_apply _
      have hcat_ofFn : ∀ v, List.ofFn (cat v) = h ++ List.ofFn v := by
        intro v
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp only [List.getElem_ofFn, cat]
          by_cases hi : i < h.length
          · rw [dif_pos hi, List.getElem_append_left hi]; rfl
          · rw [dif_neg hi, List.getElem_append_right (Nat.not_lt.1 hi), List.getElem_ofFn]
      have hj_meas : Measurable (fun v : Fin k → Fin n × ℝ => π.next (h ++ List.ofFn v)) := by
        have hcomp := (π.measurable_next (h.length + k)).comp hcat_meas
        have heq : (fun v : Fin k → Fin n × ℝ => π.next (h ++ List.ofFn v)) =
            (fun u => π.next (List.ofFn u)) ∘ cat := by
          funext v; simp [hcat_ofFn]
        rw [heq]; exact hcomp
      have hD_meas : Measurable (fun v : Fin k → Fin n × ℝ => B ∪ History.jobs (List.ofFn v)) := by
        have h1 : Measurable (fun v : Fin k → Fin n × ℝ => fun i => (v i).1) :=
          measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
        have h2 : Measurable (fun w : Fin k → Fin n => B ∪ (List.ofFn w).toFinset) :=
          measurable_of_countable _
        have heq : (fun v : Fin k → Fin n × ℝ => B ∪ History.jobs (List.ofFn v)) =
            (fun w : Fin k → Fin n => B ∪ (List.ofFn w).toFinset) ∘ fun v i => (v i).1 := by
          funext v; simp [History.jobs, List.map_ofFn]; rfl
        rw [heq]; exact h2.comp h1
      have hcomb : Measurable (fun p : Finset (Fin n) × Fin n =>
          if IsAvailable F p.1 p.2 ∧
              jobR F lam p.2 + phi F p.2 * famG F lam (insert p.2 p.1) = famH F lam p.1 then
            p.2
          else
            canonNext F (π.next []) lam p.1) :=
        measurable_of_countable _
      exact hcomb.comp (hD_meas.prodMk hj_meas)
    stop := fun l => decide (B ∪ l.jobs = Finset.univ ∨ famH F lam (B ∪ l.jobs) ≤ 0)
    measurable_stop := fun k => by
      have h1 : Measurable (fun v : Fin k → Fin n × ℝ => fun i => (v i).1) :=
        measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
      have h2 : Measurable (fun w : Fin k → Fin n =>
          decide (B ∪ (List.ofFn w).toFinset = Finset.univ ∨
            famH F lam (B ∪ (List.ofFn w).toFinset) ≤ 0)) :=
        measurable_of_countable _
      have heq : (fun v : Fin k → Fin n × ℝ =>
          decide (B ∪ History.jobs (List.ofFn v) = Finset.univ ∨
            famH F lam (B ∪ History.jobs (List.ofFn v)) ≤ 0)) =
          (fun w : Fin k → Fin n =>
            decide (B ∪ (List.ofFn w).toFinset = Finset.univ ∨
              famH F lam (B ∪ (List.ofFn w).toFinset) ≤ 0)) ∘ fun v i => (v i).1 := by
        funext v; simp [History.jobs, List.map_ofFn]; rfl
      rw [heq]; exact h2.comp h1 }

lemma fiStageRule_next_spec (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n)
    (h l : History n) (hne : A ∪ h.jobs ∪ l.jobs ≠ Finset.univ) :
    let B := A ∪ h.jobs
    let lam := familyIndex F B
    let D := B ∪ l.jobs
    let j := (fiStageRule F A π h).next l
    IsAvailable F D j ∧
      jobR F lam j + phi F j * famG F lam (insert j D) = famH F lam D := by
  classical
  dsimp only [fiStageRule]
  split_ifs with hcond
  · exact hcond
  · have hspec := canonNext_spec F (π.next []) (familyIndex F (A ∪ h.jobs)) hne
    exact ⟨(mem_availSet F.prec).1 hspec.1, hspec.2⟩

lemma fiStageRule_isFIStarStage (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n)
    (h : History n) (hB : A ∪ h.jobs ≠ Finset.univ) :
    IsFIStarStage F (A ∪ h.jobs) (fiStageRule F A π h) := by
  set B := A ∪ h.jobs
  set lam := familyIndex F B
  set p := fiStageRule F A π h
  -- First prove feasibility by induction on `k`
  have hfeas : p.Feasible F B := by
    intro ω k hk
    suffices hs : ∀ m ≤ numRemaining B,
        (B ∪ (p.toPolicy.hist ω m).jobs).card = B.card + m ∧
        (m < numRemaining B → IsAvailable F (B ∪ (p.toPolicy.hist ω m).jobs) (p.toPolicy.job ω m)) from
      (hs k hk.le).2 hk
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨by simp [Policy.hist, History.jobs], fun _ => ?_⟩
      have hnil : History.jobs ([] : History n) = ∅ := rfl
      have hne : B ∪ History.jobs [] ≠ Finset.univ := by rw [hnil, Finset.union_empty]; exact hB
      have hspec := (fiStageRule_next_spec F A π h [] hne).1
      change IsAvailable F (B ∪ History.jobs []) (p.next []) at hspec
      rw [hnil, Finset.union_empty] at hspec
      simpa only [Policy.job, Policy.hist, hnil, Finset.union_empty] using hspec
    | succ m ih =>
      intro hle
      have hm_lt : m < numRemaining B := Nat.lt_of_succ_le hle
      obtain ⟨hcard, hav⟩ := ih hm_lt.le
      have hav_m := hav hm_lt
      have hset : B ∪ (p.toPolicy.hist ω (m + 1)).jobs =
          insert (p.toPolicy.job ω m) (B ∪ (p.toPolicy.hist ω m).jobs) := by
        ext a; simp [Policy.hist, Policy.job, History.jobs, or_left_comm]
      have hcard' : (B ∪ (p.toPolicy.hist ω (m + 1)).jobs).card = B.card + (m + 1) := by
        rw [hset, Finset.card_insert_of_notMem hav_m.1, hcard]
        omega
      refine ⟨hcard', fun hlt => ?_⟩
      have hne : B ∪ (p.toPolicy.hist ω (m + 1)).jobs ≠ Finset.univ := by
        intro heq
        rw [heq, Finset.card_univ, Fintype.card_fin] at hcard'
        have hBle : B.card ≤ n := by simpa using Finset.card_le_univ B
        simp only [numRemaining] at hlt
        omega
      exact (fiStageRule_next_spec F A π h (p.toPolicy.hist ω (m + 1)) hne).1
  refine ⟨hfeas, ?_⟩
  have hH0 : famH F lam B = 0 := famH_familyIndex_eq_zero F (π.next []) hB
  have heq : p.reward F B - lam * p.time F B = famH F lam B := by
    refine stage_eq_famH_of_greedy F hB p hfeas lam ?_ ?_ ?_
    · have hnil : History.jobs ([] : History n) = ∅ := rfl
      have hne : B ∪ History.jobs [] ≠ Finset.univ := by rw [hnil, Finset.union_empty]; exact hB
      have hspec := (fiStageRule_next_spec F A π h [] hne).2
      change jobR F lam (p.next []) + phi F (p.next []) *
          famG F lam (insert (p.next []) (B ∪ History.jobs [])) =
        famH F lam (B ∪ History.jobs []) at hspec
      rw [hnil, Finset.union_empty] at hspec
      exact hspec
    · intro ω k hk1 hkr hIn
      have hstop_false : p.stop (p.toPolicy.hist ω k) = false :=
        hIn.2 k (Finset.mem_Icc.2 ⟨hk1, le_rfl⟩)
      have hstop_def : p.stop (p.toPolicy.hist ω k) =
          decide (B ∪ (p.toPolicy.hist ω k).jobs = Finset.univ ∨
            famH F lam (B ∪ (p.toPolicy.hist ω k).jobs) ≤ 0) := rfl
      rw [hstop_def, decide_eq_false_iff_not, not_or, not_le] at hstop_false
      have hG : famG F lam (B ∪ (p.toPolicy.hist ω k).jobs) =
          famH F lam (B ∪ (p.toPolicy.hist ω k).jobs) := by
        rw [famG_eq_max, max_eq_right hstop_false.2.le]
      rw [hG]
      exact (fiStageRule_next_spec F A π h (p.toPolicy.hist ω k) hstop_false.1).2
    · intro ω k hkr hIn hnotIn
      have hset : insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs) =
          B ∪ (p.toPolicy.hist ω (k + 1)).jobs := by
        ext a; simp [Policy.hist, Policy.job, History.jobs, or_left_comm]
      rw [hset]
      by_cases hlast : k + 1 < numRemaining B
      · have hstop_true : p.stop (p.toPolicy.hist ω (k + 1)) = true := by
          by_contra hf
          have hbf : p.stop (p.toPolicy.hist ω (k + 1)) = false := Bool.eq_false_iff.2 hf
          apply hnotIn
          refine ⟨hlast, fun l hl => ?_⟩
          rcases (Finset.mem_Icc.1 hl).2.eq_or_lt with rfl | hlt
          · exact hbf
          · exact hIn.2 l (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hl).1, Nat.lt_succ_iff.1 hlt⟩)
        have hstop_def : p.stop (p.toPolicy.hist ω (k + 1)) =
            decide (B ∪ (p.toPolicy.hist ω (k + 1)).jobs = Finset.univ ∨
              famH F lam (B ∪ (p.toPolicy.hist ω (k + 1)).jobs) ≤ 0) := rfl
        rw [hstop_def, decide_eq_true_eq] at hstop_true
        rcases hstop_true with huniv | hle0
        · rw [huniv]; exact famG_univ F lam
        · rw [famG_eq_max, max_eq_left hle0]
      · have heq : k + 1 = numRemaining B := by omega
        rw [heq, Stage.union_hist_jobs_eq_univ F B p hfeas ω]
        exact famG_univ F lam
  have htime := stage_time_pos F hB p
  unfold Stage.ratio
  rw [div_eq_iff htime.ne']
  linarith

lemma fiStageRule_agrees (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n)
    (hfeas : π.Feasible F A) (ω : Fin n → ℝ)
    (hω : ∀ k < numRemaining A,
      ∃ p : Stage n, IsFIStarStage F (A ∪ (π.hist ω k).jobs) p ∧ p.next [] = π.job ω k) :
    ∀ k < numRemaining A, π.job ω k = stagedJob (fiStageRule F A π) ω k := by
  set ρ := fiStageRule F A π
  suffices hinv : ∀ k ≤ numRemaining A,
      ((stagedState ρ ω k).1 ++ (stagedState ρ ω k).2 = π.hist ω k) ∧
      ((stagedState ρ ω k).2 = [] ∨
        (A ∪ (π.hist ω k).jobs ≠ Finset.univ ∧
          0 < famH F (familyIndex F (A ∪ (stagedState ρ ω k).1.jobs)) (A ∪ (π.hist ω k).jobs))) ∧
      (∀ m < k, π.job ω m = stagedJob ρ ω m) by
    exact (hinv (numRemaining A) le_rfl).2.2
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨by simp [stagedState, Policy.hist], Or.inl rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | succ k ih =>
    intro hle
    have hk : k < numRemaining A := Nat.lt_of_succ_le hle
    obtain ⟨hcat, hstate, hprev⟩ := ih hk.le
    set h₀ := (stagedState ρ ω k).1
    set l := (stagedState ρ ω k).2
    set B := A ∪ h₀.jobs
    set lam := familyIndex F B
    set D := A ∪ (π.hist ω k).jobs
    have hD_eq : B ∪ l.jobs = D := by
      have hjobs : History.jobs (h₀ ++ l) = h₀.jobs ∪ l.jobs := by
        simp [History.jobs, List.map_append, List.toFinset_append]
      dsimp only [B, D]
      rw [← hcat, hjobs, Finset.union_assoc]
    have hav_π : IsAvailable F D (π.job ω k) := hfeas ω k hk
    have hD_ne : D ≠ Finset.univ := fun heq => hav_π.1 (heq ▸ Finset.mem_univ _)
    -- Show `0 ≤ famH F lam D`
    have hH_nn : 0 ≤ famH F lam D := by
      rcases hstate with hl_nil | ⟨_, hH_pos⟩
      · have hDB : D = B := by
          rw [← hD_eq, hl_nil]
          simp [History.jobs]
        have hB_ne : B ≠ Finset.univ := hDB ▸ hD_ne
        rw [hDB, famH_familyIndex_eq_zero F (π.next []) hB_ne]
      · exact hH_pos.le
    -- From FI property at step `k`: `π.job ω k` maximizes `famH F (familyIndex F D) D`, hence `dpU`, hence `famH F lam D`!
    obtain ⟨p_k, hp_k, hp_next⟩ := hω k hk
    have hmax_D := isFIStarStage_next_maximizer F (π.next []) hD_ne hp_k
    rw [hp_next] at hmax_D
    have hH_D0 : famH F (familyIndex F D) D = 0 := famH_familyIndex_eq_zero F (π.next []) hD_ne
    have hU_D : jobR F (familyIndex F D) (π.job ω k) +
        phi F (π.job ω k) * dpU F.prec F.prec_acyclic (jobR F (familyIndex F D)) (phi F) (insert (π.job ω k) D) =
        dpU F.prec F.prec_acyclic (jobR F (familyIndex F D)) (phi F) D :=
      (dpH_maximizer_iff_dpU_maximizer F.prec F.prec_acyclic (phi_pos F) (phi_lt_one F)
        hD_ne (by change 0 ≤ famH F (familyIndex F D) D; rw [hH_D0]) hmax_D.1).1 hmax_D.2
    have hU_a : jobA F (π.job ω k) +
        phi F (π.job ω k) * dpU F.prec F.prec_acyclic (jobA F) (phi F) (insert (π.job ω k) D) =
        dpU F.prec F.prec_acyclic (jobA F) (phi F) D :=
      (dpU_shift_maximizer_iff F.prec F.prec_acyclic (jobA F) (phi F) F.γ F.γ_pos.ne'
        (familyIndex F D) hmax_D.1).1 hU_D
    have hU_lam : jobR F lam (π.job ω k) +
        phi F (π.job ω k) * dpU F.prec F.prec_acyclic (jobR F lam) (phi F) (insert (π.job ω k) D) =
        dpU F.prec F.prec_acyclic (jobR F lam) (phi F) D :=
      (dpU_shift_maximizer_iff F.prec F.prec_acyclic (jobA F) (phi F) F.γ F.γ_pos.ne'
        lam hmax_D.1).2 hU_a
    have hH_lam : jobR F lam (π.job ω k) +
        phi F (π.job ω k) * famG F lam (insert (π.job ω k) D) = famH F lam D :=
      (dpH_maximizer_iff_dpU_maximizer F.prec F.prec_acyclic (phi_pos F) (phi_lt_one F)
        hD_ne hH_nn hmax_D.1).2 hU_lam
    -- Therefore `stagedJob ρ ω k = π.job ω k`!
    have hjob_eq : stagedJob ρ ω k = π.job ω k := by
      unfold stagedJob
      change (fiStageRule F A π h₀).next l = π.job ω k
      dsimp only [fiStageRule]
      rw [hD_eq, hcat]
      have hcond : IsAvailable F D (π.next (π.hist ω k)) ∧
          jobR F lam (π.next (π.hist ω k)) +
            phi F (π.next (π.hist ω k)) * famG F lam (insert (π.next (π.hist ω k)) D) =
          famH F lam D := ⟨hav_π, hH_lam⟩
      rw [if_pos hcond]
      rfl
    -- Advance `stagedState` to `k + 1`
    have hhist_next : h₀ ++ (l ++ [(π.job ω k, ω (π.job ω k))]) = π.hist ω (k + 1) := by
      rw [← List.append_assoc, hcat]
      rfl
    have hprev' : ∀ m < k + 1, π.job ω m = stagedJob ρ ω m := by
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hlt | rfl
      · exact hprev m hlt
      · exact hjob_eq.symm
    have hstep_state : stagedState ρ ω (k + 1) =
        if (ρ h₀).stop (l ++ [(π.job ω k, ω (π.job ω k))]) then
          (h₀ ++ (l ++ [(π.job ω k, ω (π.job ω k))]), [])
        else
          (h₀, l ++ [(π.job ω k, ω (π.job ω k))]) := by
      simp only [stagedState]
      change (let j := stagedJob ρ ω k; let l' := l ++ [(j, ω j)];
          if (ρ h₀).stop l' then (h₀ ++ l', []) else (h₀, l')) = _
      rw [hjob_eq]
    rw [hstep_state]
    by_cases hstop : (ρ h₀).stop (l ++ [(π.job ω k, ω (π.job ω k))]) = true
    · simp only [hstop, ↓reduceIte, List.append_nil]
      exact ⟨hhist_next, Or.inl trivial, hprev'⟩
    · have hstop_f : (ρ h₀).stop (l ++ [(π.job ω k, ω (π.job ω k))]) = false :=
        Bool.eq_false_iff.2 hstop
      simp only [hstop, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hhist_next, Or.inr ?_, hprev'⟩
      simp only [ρ, fiStageRule, decide_eq_false_iff_not, not_or, not_le] at hstop_f
      have hD_next : B ∪ History.jobs (l ++ [(π.job ω k, ω (π.job ω k))]) = A ∪ (π.hist ω (k + 1)).jobs := by
        rw [← hhist_next]
        simp [B, History.jobs, List.map_append, List.toFinset_append, Finset.union_assoc]
      rw [hD_next] at hstop_f
      exact hstop_f

end Probability

end AllocationIndices.Precedence

theorem solution {n : ℕ} (F : AllocationIndices.Precedence.JobFamily n) (A : Finset (Fin n))
    (π : AllocationIndices.Precedence.Policy n)
    (hπ : AllocationIndices.Precedence.IsFIPolicy F A π) :
    AllocationIndices.Precedence.IsFIStarPolicy F A π := by
  refine ⟨hπ.1, AllocationIndices.Precedence.fiStageRule F A π, ?_, ?_⟩
  · intro h hB
    exact AllocationIndices.Precedence.fiStageRule_isFIStarStage F A π h hB
  · filter_upwards [hπ.2] with ω hω
    exact AllocationIndices.Precedence.fiStageRule_agrees F A π hπ.1 ω hω
