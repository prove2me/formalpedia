-- Prove2me | solution 1 for AffirmativeChoice.Reserve.canonical_reserve_represents
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:18:21.981613+00:00
-- url     : https://prove2.me/submissions/54f9784e-d96b-4adb-bcd1-1236515f1215

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace ACInfra
open AffirmativeChoice.Reserve

variable {α : Type*} [DecidableEq α]

/-- number of elements of `F` strictly below `x` -/
def cnt (F : Finset α) (f : α → ℕ) (x : α) : ℕ := (F.filter (fun y => f y < f x)).card

lemma cnt_lt_cnt {F : Finset α} {f : α → ℕ} {x y : α} (hx : x ∈ F) (hxy : f x < f y) :
    cnt F f x < cnt F f y := by
  unfold cnt
  apply Finset.card_lt_card
  refine ⟨fun z hz => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, lt_trans hz.2 hxy⟩
  · have := h (Finset.mem_filter.2 ⟨hx, hxy⟩); simp at this

lemma lt_of_cnt_lt {F : Finset α} {f : α → ℕ} (hinj : Set.InjOn f ↑F) {x y : α}
    (hx : x ∈ F) (hy : y ∈ F) (h : cnt F f x < cnt F f y) : f x < f y := by
  rcases lt_trichotomy (f x) (f y) with h1 | h1 | h1
  · exact h1
  · have := hinj hx hy h1; subst this; omega
  · have := cnt_lt_cnt hy h1; omega

lemma cnt_lt_iff {F : Finset α} {f : α → ℕ} (hinj : Set.InjOn f ↑F) {x y : α}
    (hx : x ∈ F) (hy : y ∈ F) : cnt F f x < cnt F f y ↔ f x < f y :=
  ⟨lt_of_cnt_lt hinj hx hy, cnt_lt_cnt hx⟩

lemma cnt_injOn {F : Finset α} {f : α → ℕ} (hinj : Set.InjOn f ↑F) {x y : α}
    (hx : x ∈ F) (hy : y ∈ F) (h : cnt F f x = cnt F f y) : x = y := by
  rcases lt_trichotomy (f x) (f y) with h1 | h1 | h1
  · have := cnt_lt_cnt hx h1; omega
  · exact hinj hx hy h1
  · have := cnt_lt_cnt hy h1; omega

lemma cnt_lt_card {F : Finset α} {f : α → ℕ} {x : α} (hx : x ∈ F) : cnt F f x < F.card := by
  unfold cnt
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h hx; simp at this

lemma image_cnt {F : Finset α} {f : α → ℕ} (hinj : Set.InjOn f ↑F) :
    F.image (cnt F f) = Finset.range F.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    exact Finset.mem_range.2 (cnt_lt_card hx)
  · rw [Finset.card_range, Finset.card_image_of_injOn]
    intro x hx y hy h; exact cnt_injOn hinj hx hy h

lemma exists_cnt_eq {F : Finset α} {f : α → ℕ} (hinj : Set.InjOn f ↑F) {k : ℕ}
    (hk : k < F.card) : ∃ x ∈ F, cnt F f x = k := by
  have : k ∈ F.image (cnt F f) := by rw [image_cnt hinj]; exact Finset.mem_range.2 hk
  simpa using this

/-- prefix lemma -/
lemma prefix_eq {F D : Finset α} {f : α → ℕ} (hinj : Set.InjOn f ↑F) (hDF : D ⊆ F)
    (hdown : ∀ x ∈ D, ∀ y ∈ F, f y < f x → y ∈ D) :
    D = F.filter (fun x => cnt F f x < D.card) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · intro hx
    refine ⟨hDF hx, ?_⟩
    unfold cnt
    apply Finset.card_lt_card
    refine ⟨fun z hz => ?_, fun h => ?_⟩
    · simp only [Finset.mem_filter] at hz; exact hdown x hx z hz.1 hz.2
    · have := h hx; simp at this
  · rintro ⟨hxF, hlt⟩
    by_contra hxD
    have hsub : D ⊆ F.filter (fun y => f y < f x) := by
      intro y hy
      refine Finset.mem_filter.2 ⟨hDF hy, ?_⟩
      rcases lt_trichotomy (f y) (f x) with h1 | h1 | h1
      · exact h1
      · exact absurd (hinj (hDF hy) hxF h1 ▸ hy) hxD
      · exact absurd (hdown y hy x hxF h1) hxD
    have := Finset.card_le_card hsub
    unfold cnt at hlt; omega

lemma card_filter_cnt_lt {F : Finset α} {f : α → ℕ} (hinj : Set.InjOn f ↑F) (r : ℕ) :
    (F.filter (fun x => cnt F f x < r)).card = min r F.card := by
  have h1 : (F.filter (fun x => cnt F f x < r)).image (cnt F f) = Finset.range (min r F.card) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨x, ⟨hx, hr⟩, rfl⟩; have := cnt_lt_card (f := f) hx; omega
    · intro hk
      obtain ⟨x, hx, hxk⟩ := exists_cnt_eq hinj (k := k) (by omega)
      exact ⟨x, ⟨hx, by omega⟩, hxk⟩
  rw [← Finset.card_range (min r F.card), ← h1, Finset.card_image_of_injOn]
  intro x hx y hy h
  exact cnt_injOn hinj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hy).1 h

lemma filter_cnt_lt_of_le {F : Finset α} {f : α → ℕ} {r : ℕ} (hr : F.card ≤ r) :
    F.filter (fun x => cnt F f x < r) = F := by
  apply Finset.filter_true_of_mem
  intro x hx; have := cnt_lt_card (f := f) hx; omega

lemma filter_cnt_lt_min (F : Finset α) (f : α → ℕ) (r : ℕ) :
    F.filter (fun x => cnt F f x < min r F.card) = F.filter (fun x => cnt F f x < r) := by
  apply Finset.filter_congr
  intro x hx; have := cnt_lt_card (f := f) hx; omega

/-- prefix monotone -/
lemma filter_cnt_mono (F : Finset α) (f : α → ℕ) {r s : ℕ} (h : r ≤ s) :
    F.filter (fun x => cnt F f x < r) ⊆ F.filter (fun x => cnt F f x < s) := by
  intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩

lemma filter_cnt_down {F : Finset α} {f : α → ℕ} (r : ℕ) {x y : α}
    (hx : x ∈ F.filter (fun x => cnt F f x < r)) (hy : y ∈ F) (hyx : f y < f x) :
    y ∈ F.filter (fun x => cnt F f x < r) := by
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hy, lt_of_lt_of_le (cnt_lt_cnt hy hyx) hx.2.le |>.trans_le le_rfl |> fun h => by omega⟩

lemma cnt_sub {F G : Finset α} {f : α → ℕ} {x : α} (hGF : G ⊆ F)
    (hclosed : ∀ y ∈ F, f y < f x → y ∈ G) : cnt G f x = cnt F f x := by
  unfold cnt; congr 1
  ext y; simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨hGF h.1, h.2⟩, fun h => ⟨hclosed y h.1 h.2, h.2⟩⟩

section Prob
variable {𝒮 : Type*} [DecidableEq 𝒮]

lemma rank_eq (P : Problem 𝒮) (s : 𝒮) : rank P s = cnt P.S P.pri s + 1 := rfl

lemma mem_top {q : ℕ} {P : Problem 𝒮} {s : 𝒮} :
    s ∈ top q P ↔ s ∈ P.S ∧ cnt P.S P.pri s < q := by
  unfold top; rw [Finset.mem_filter, rank_eq]; exact and_congr_right (fun _ => by omega)

lemma top_eq_filter (q : ℕ) (P : Problem 𝒮) :
    top q P = P.S.filter (fun s => cnt P.S P.pri s < q) := by
  ext s; rw [mem_top, Finset.mem_filter]

lemma top_card (q : ℕ) (P : Problem 𝒮) : (top q P).card = min q P.S.card := by
  rw [top_eq_filter]; exact card_filter_cnt_lt P.inj q

lemma top_subset (q : ℕ) (P : Problem 𝒮) : top q P ⊆ P.S := Finset.filter_subset _ _

lemma top_down {q : ℕ} {P : Problem 𝒮} {s s' : 𝒮} (hs : s ∈ top q P) (hs' : s' ∈ P.S)
    (h : P.pri s' < P.pri s) : s' ∈ top q P := by
  rw [mem_top] at hs ⊢
  exact ⟨hs', lt_trans (cnt_lt_cnt hs' h) hs.2⟩

lemma top_lt_bottom {q : ℕ} {P : Problem 𝒮} {t b : 𝒮} (ht : t ∈ top q P) (hb : b ∈ P.S)
    (hbt : b ∉ top q P) : P.pri t < P.pri b := by
  rcases lt_trichotomy (P.pri t) (P.pri b) with h | h | h
  · exact h
  · exact absurd (P.inj (top_subset q P ht) hb h ▸ ht) hbt
  · exact absurd (top_down ht hb h) hbt

lemma top_eq_S {q : ℕ} {P : Problem 𝒮} (h : P.S.card ≤ q) : top q P = P.S := by
  rw [top_eq_filter]; exact filter_cnt_lt_of_le h

lemma card_S_gt_of_bottom {q : ℕ} {P : Problem 𝒮} {b : 𝒮} (hb : b ∈ P.S)
    (hbt : b ∉ top q P) : q < P.S.card := by
  by_contra h; rw [not_lt] at h; rw [top_eq_S h] at hbt; exact hbt hb

lemma rank_inj {P : Problem 𝒮} {s s' : 𝒮} (hs : s ∈ P.S) (hs' : s' ∈ P.S)
    (h : rank P s = rank P s') : s = s' := by
  rw [rank_eq, rank_eq] at h; exact cnt_injOn P.inj hs hs' (by omega)

lemma typeAt_some_iff (P : Problem 𝒮) (k : ℕ) (b : Bool) :
    typeAt P k = some b ↔ ∃ s ∈ P.S, rank P s = k ∧ P.τ s = b := by
  unfold typeAt
  cases b with
  | true =>
    split_ifs with h1 h2
    · simpa using h1
    · simp only [Option.some.injEq, Bool.false_eq_true, false_iff]; exact h1
    · simp only [reduceCtorEq, false_iff]; exact h1
  | false =>
    split_ifs with h1 h2
    · simp only [Option.some.injEq, Bool.true_eq_false, false_iff]
      rintro ⟨s, hs, hk, hτ⟩
      obtain ⟨s', hs', hk', hτ'⟩ := h1
      have := rank_inj hs hs' (hk.trans hk'.symm); subst this; simp_all
    · simp only [true_iff]
      obtain ⟨s, hs, hk⟩ := h2
      refine ⟨s, hs, hk, ?_⟩
      by_contra hc; simp at hc; exact h1 ⟨s, hs, hk, hc⟩
    · simp only [reduceCtorEq, false_iff]
      rintro ⟨s, hs, hk, -⟩; exact h2 ⟨s, hs, hk⟩

lemma typeAt_none_iff (P : Problem 𝒮) (k : ℕ) :
    typeAt P k = none ↔ ¬ ∃ s ∈ P.S, rank P s = k := by
  unfold typeAt
  split_ifs with h1 h2
  · simp only [reduceCtorEq, false_iff, not_not]
    obtain ⟨s, hs, hk, -⟩ := h1; exact ⟨s, hs, hk⟩
  · simp only [reduceCtorEq, false_iff, not_not]; exact h2
  · simp only [true_iff]; exact h2

lemma typeAt_eq_of {P P' : Problem 𝒮} {k : ℕ}
    (h : ∀ b, (∃ s ∈ P.S, rank P s = k ∧ P.τ s = b) ↔ (∃ s ∈ P'.S, rank P' s = k ∧ P'.τ s = b)) :
    typeAt P k = typeAt P' k := by
  rcases h1 : typeAt P k with _ | b
  · rw [typeAt_none_iff] at h1
    symm; rw [typeAt_none_iff]
    rintro ⟨s, hs, hk⟩
    obtain ⟨s', hs', hk', -⟩ := (h (P'.τ s)).2 ⟨s, hs, hk, rfl⟩
    exact h1 ⟨s', hs', hk'⟩
  · rw [typeAt_some_iff] at h1
    symm; rw [typeAt_some_iff]; exact (h b).1 h1

lemma rank_le_card {P : Problem 𝒮} {s : 𝒮} (hs : s ∈ P.S) : rank P s ≤ P.S.card := by
  rw [rank_eq]; have := cnt_lt_card (f := P.pri) hs; omega

lemma exists_rank_eq {P : Problem 𝒮} {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ P.S.card) :
    ∃ s ∈ P.S, rank P s = k := by
  obtain ⟨s, hs, h⟩ := exists_cnt_eq P.inj (k := k - 1) (by omega)
  exact ⟨s, hs, by rw [rank_eq]; omega⟩

end Prob

section AA
variable {𝒮 : Type*} [DecidableEq 𝒮] {q : ℕ} (C : ChoiceRule 𝒮 q)

lemma C_card (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    (C.C P).card = min P.S.card q := hAA.1 P

lemma C_eq_S (hAA : IsAffirmativeActionRule C) {P : Problem 𝒮} (h : P.S.card ≤ q) :
    C.C P = P.S := by
  apply Finset.eq_of_subset_of_card_le (C.subset P)
  rw [C_card C hAA]; omega

lemma topMin_sub (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    topMin q P ⊆ C.C P := by
  intro s hs
  unfold topMin at hs; rw [Finset.mem_filter] at hs
  by_contra hsC
  by_cases hle : P.S.card ≤ q
  · rw [C_eq_S C hAA hle] at hsC; exact hsC (top_subset q P hs.1)
  rw [not_le] at hle
  have hnot : ¬ C.C P ⊆ top q P := by
    intro hsub
    have : C.C P = top q P := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [C_card C hAA, top_card]; omega
    exact hsC (this ▸ hs.1)
  obtain ⟨c, hc, hct⟩ := Finset.not_subset.1 hnot
  have hlt := top_lt_bottom hs.1 (C.subset P hc) hct
  have := hAA.2.2 P c hc s (top_subset q P hs.1) hsC hlt
  rw [hs.2] at this; simp at this

lemma bottom_chosen_minor (hAA : IsAffirmativeActionRule C) {P : Problem 𝒮} {c : 𝒮}
    (hc : c ∈ C.C P) (hct : c ∉ top q P) : P.τ c = true := by
  have hcS := C.subset P hc
  have hgt := card_S_gt_of_bottom hcS hct
  have hnot : ¬ top q P ⊆ C.C P := by
    intro hsub
    have h1 : insert c (top q P) ⊆ C.C P := Finset.insert_subset hc hsub
    have h2 := Finset.card_le_card h1
    rw [Finset.card_insert_of_notMem hct, top_card] at h2
    have := C.card_le P; omega
  obtain ⟨t, ht, htC⟩ := Finset.not_subset.1 hnot
  exact (hAA.2.2 P c hc t (top_subset q P ht) htC (top_lt_bottom ht hcS hct)).1

lemma minor_down (hAA : IsAffirmativeActionRule C) {P : Problem 𝒮} {c y : 𝒮}
    (hc : c ∈ C.C P) (hy : y ∈ P.S) (hτy : P.τ y = true) (hlt : P.pri y < P.pri c) :
    y ∈ C.C P := by
  by_contra hyC
  have := (hAA.2.2 P c hc y hy hyC hlt).2; rw [hτy] at this; simp at this

lemma major_down (hAA : IsAffirmativeActionRule C) {P : Problem 𝒮} {c y : 𝒮}
    (hc : c ∈ C.C P) (hτc : P.τ c = false) (hy : y ∈ P.S) (hlt : P.pri y < P.pri c) :
    y ∈ C.C P := by
  by_contra hyC
  have := (hAA.2.2 P c hc y hy hyC hlt).1; rw [hτc] at this; simp at this

lemma restrict_eq (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (P : Problem 𝒮) (S' : Finset 𝒮) (h : S' ⊆ P.S) (hC : C.C P ⊆ S') :
    C.C (P.restrict S' h) = C.C P := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro s hs; exact hsub P s hs S' h (hC hs)
  · rw [C_card C hAA, C_card C hAA]
    have h1 := Finset.card_le_card h
    have h2 := Finset.card_le_card hC
    rw [C_card C hAA] at h2
    show min S'.card q ≤ min P.S.card q
    omega

lemma mem_CA {P : Problem 𝒮} {s : 𝒮} :
    s ∈ CA C P ↔ s ∈ C.C P ∧ P.τ s = true ∧ s ∉ top q P := by
  unfold CA Cm bottom
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, C.subset P h1, h3⟩

end AA

section Sets
variable {𝒮 : Type*} [DecidableEq 𝒮] {q : ℕ}

lemma mem_botMin {P : Problem 𝒮} {s : 𝒮} :
    s ∈ botMin q P ↔ s ∈ P.S ∧ s ∉ top q P ∧ P.τ s = true := by
  unfold botMin bottom; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto

lemma mem_topMin {P : Problem 𝒮} {s : 𝒮} :
    s ∈ topMin q P ↔ s ∈ top q P ∧ P.τ s = true := by
  unfold topMin; simp only [Finset.mem_filter]

lemma mem_topMaj {P : Problem 𝒮} {s : 𝒮} :
    s ∈ topMaj q P ↔ s ∈ top q P ∧ P.τ s = false := by
  unfold topMaj; simp only [Finset.mem_filter]

lemma mem_major {P : Problem 𝒮} {s : 𝒮} :
    s ∈ major P ↔ s ∈ P.S ∧ P.τ s = false := by
  unfold major; simp only [Finset.mem_filter]

lemma mem_minor {P : Problem 𝒮} {s : 𝒮} :
    s ∈ minor P ↔ s ∈ P.S ∧ P.τ s = true := by
  unfold minor; simp only [Finset.mem_filter]

lemma botMin_inj (P : Problem 𝒮) : Set.InjOn P.pri ↑(botMin q P) :=
  P.inj.mono (fun x hx => (mem_botMin.1 hx).1)

lemma major_inj (P : Problem 𝒮) : Set.InjOn P.pri ↑(major P) :=
  P.inj.mono (fun x hx => (mem_major.1 hx).1)

lemma topMin_card_add_topMaj_card (P : Problem 𝒮) :
    (topMin q P).card + (topMaj q P).card = min q P.S.card := by
  rw [← top_card q P]
  unfold topMin topMaj
  have := Finset.card_filter_add_card_filter_not (s := top q P) (fun s => P.τ s = true)
  simp only [Bool.not_eq_true] at this
  exact this

end Sets

section AA2
variable {𝒮 : Type*} [DecidableEq 𝒮] {q : ℕ} (C : ChoiceRule 𝒮 q)

/-- chosen majority students -/
def CM (P : Problem 𝒮) : Finset 𝒮 := (C.C P).filter (fun s => P.τ s = false)

lemma CA_sub_botMin (P : Problem 𝒮) : CA C P ⊆ botMin q P := by
  intro s hs; rw [mem_CA] at hs; rw [mem_botMin]; exact ⟨C.subset P hs.1, hs.2.2, hs.2.1⟩

lemma CA_prefix (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    CA C P = (botMin q P).filter (fun x => cnt (botMin q P) P.pri x < (CA C P).card) := by
  apply prefix_eq (botMin_inj P) (CA_sub_botMin C P)
  intro x hx y hy hlt
  rw [mem_CA] at hx ⊢; rw [mem_botMin] at hy
  exact ⟨minor_down C hAA hx.1 hy.1 hy.2.2 hlt, hy.2.2, hy.2.1⟩

lemma CM_sub_major (P : Problem 𝒮) : CM C P ⊆ major P := by
  intro s hs; unfold CM at hs; rw [Finset.mem_filter] at hs; rw [mem_major]
  exact ⟨C.subset P hs.1, hs.2⟩

lemma CM_prefix (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    CM C P = (major P).filter (fun x => cnt (major P) P.pri x < (CM C P).card) := by
  apply prefix_eq (major_inj P) (CM_sub_major C P)
  intro x hx y hy hlt
  unfold CM at hx ⊢; rw [Finset.mem_filter] at hx ⊢; rw [mem_major] at hy
  exact ⟨major_down C hAA hx.1 hx.2 hy.1 hlt, hy.2⟩

lemma C_decomp (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    C.C P = topMin q P ∪ CA C P ∪ CM C P := by
  ext x
  simp only [Finset.mem_union, mem_CA, mem_topMin, CM, Finset.mem_filter]
  constructor
  · intro hx
    cases h : P.τ x
    · right; exact ⟨hx, rfl⟩
    · by_cases ht : x ∈ top q P
      · left; left; exact ⟨ht, rfl⟩
      · left; right; exact ⟨hx, rfl, ht⟩
  · rintro ((h | h) | h)
    · exact topMin_sub C hAA P (mem_topMin.2 h)
    · exact h.1
    · exact h.1

lemma C_card_decomp (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    (C.C P).card = (topMin q P).card + (CA C P).card + (CM C P).card := by
  conv_lhs => rw [C_decomp C hAA P]
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · rw [Finset.disjoint_left]; intro x h1 h2
    rw [mem_topMin] at h1; rw [mem_CA] at h2; exact h2.2.2 h1.1
  · rw [Finset.disjoint_left]; intro x h1 h2
    unfold CM at h2; rw [Finset.mem_filter] at h2
    rcases Finset.mem_union.1 h1 with h1 | h1
    · rw [mem_topMin] at h1; rw [h1.2] at h2; simp at h2
    · rw [mem_CA] at h1; rw [h1.2.1] at h2; simp at h2

lemma CA_card_le_botMin (P : Problem 𝒮) : (CA C P).card ≤ (botMin q P).card :=
  Finset.card_le_card (CA_sub_botMin C P)

lemma C_eq_reserveChoice (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    C.C P = reserveChoice q P (CA C P).card := by
  have hmin : min (CA C P).card (botMin q P).card = (CA C P).card :=
    min_eq_left (CA_card_le_botMin C P)
  unfold reserveChoice
  rw [hmin]
  have hCA : (botMin q P).filter (fun b => ((botMin q P).filter
      (fun b' => P.pri b' < P.pri b)).card < (CA C P).card) = CA C P :=
    (CA_prefix C hAA P).symm
  have hCM : (major P).filter (fun s => ((major P).filter (fun s' => P.pri s' < P.pri s)).card <
      q - (topMin q P).card - (CA C P).card) = CM C P := by
    have hdec := C_card_decomp C hAA P
    rw [C_card C hAA] at hdec
    by_cases hle : P.S.card ≤ q
    · have hCMe : CM C P = major P := by
        unfold CM major; rw [C_eq_S C hAA hle]
      rw [hCMe]
      apply filter_cnt_lt_of_le
      rw [← hCMe]; omega
    · rw [not_le] at hle
      have : q - (topMin q P).card - (CA C P).card = (CM C P).card := by omega
      rw [this]; exact (CM_prefix C hAA P).symm
  rw [hCA, hCM]; exact C_decomp C hAA P

lemma reserveChoice_min (P : Problem 𝒮) (r : ℕ) :
    reserveChoice q P r = reserveChoice q P (min r (botMin q P).card) := by
  unfold reserveChoice
  have h1 : min (min r (botMin q P).card) (botMin q P).card = min r (botMin q P).card := by omega
  rw [h1]
  congr 2
  exact (filter_cnt_lt_min (botMin q P) P.pri r).symm

lemma CA_card_le_q (P : Problem 𝒮) : (CA C P).card ≤ q := by
  have : CA C P ⊆ C.C P := fun s hs => (mem_CA C |>.1 hs).1
  exact (Finset.card_le_card this).trans (C.card_le P)

lemma CA_card_le_topMaj (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    (CA C P).card ≤ (topMaj q P).card := by
  have h1 := C_card_decomp C hAA P
  have h2 := topMin_card_add_topMaj_card (q := q) P
  rw [C_card C hAA] at h1
  by_cases hle : P.S.card ≤ q
  · have : CA C P = ∅ := by
      ext x; simp only [mem_CA, Finset.notMem_empty, iff_false]
      rintro ⟨hx, -, ht⟩; rw [top_eq_S hle] at ht; exact ht (C.subset P hx)
    rw [this]; simp
  · omega

lemma not_top_iff {P : Problem 𝒮} {s : 𝒮} (hs : s ∈ P.S) : s ∉ top q P ↔ q < rank P s := by
  rw [mem_top, rank_eq]; constructor
  · intro h; by_contra h'; exact h ⟨hs, by omega⟩
  · rintro h ⟨-, h'⟩; omega

lemma CA_image_sub (hAA : IsAffirmativeActionRule C) {P P' : Problem 𝒮}
    (hcard : P.S.card = P'.S.card)
    (htype : ∀ k, 1 ≤ k → k ≤ P.S.card → typeAt P k = typeAt P' k) :
    (CA C P).image (rank P) ⊆ (CA C P').image (rank P') := by
  intro k hk
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hk
  rw [mem_CA] at hs
  have hsS := C.subset P hs.1
  have h1 : typeAt P (rank P s) = some true := (typeAt_some_iff P _ true).2 ⟨s, hsS, rfl, hs.2.1⟩
  rw [htype _ (by rw [rank_eq]; omega) (rank_le_card hsS), typeAt_some_iff] at h1
  obtain ⟨s', hs', hk', hτ'⟩ := h1
  refine Finset.mem_image.2 ⟨s', ?_, hk'⟩
  rw [mem_CA]
  refine ⟨(hAA.2.1 P P' hcard htype s hsS s' hs' hk'.symm).1 hs.1, hτ', ?_⟩
  rw [not_top_iff hs', hk']; exact (not_top_iff hsS).1 hs.2.2

lemma CA_card_eq_of_typeAt (hAA : IsAffirmativeActionRule C) {P P' : Problem 𝒮}
    (hcard : P.S.card = P'.S.card)
    (htype : ∀ k, 1 ≤ k → k ≤ P.S.card → typeAt P k = typeAt P' k) :
    (CA C P).card = (CA C P').card := by
  have hinj : ∀ Q : Problem 𝒮, Set.InjOn (rank Q) ↑(CA C Q) := by
    intro Q x hx y hy h
    exact rank_inj (C.subset Q (mem_CA C |>.1 hx).1) (C.subset Q (mem_CA C |>.1 hy).1) h
  have h1 := CA_image_sub C hAA hcard htype
  have h2 := CA_image_sub C hAA hcard.symm (fun k hk1 hk2 => (htype k hk1 (hcard ▸ hk2)).symm)
  have := Finset.Subset.antisymm h1 h2
  rw [← Finset.card_image_of_injOn (hinj P), ← Finset.card_image_of_injOn (hinj P'), this]

lemma chosen_major_top (hAA : IsAffirmativeActionRule C) {P : Problem 𝒮} {c : 𝒮}
    (hc : c ∈ C.C P) (hτ : P.τ c = false) : c ∈ top q P := by
  by_contra h; have := bottom_chosen_minor C hAA hc h; rw [hτ] at this; simp at this

lemma C_sub_top_botMin (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    C.C P ⊆ top q P ∪ botMin q P := by
  intro c hc
  rw [Finset.mem_union, mem_botMin]
  by_cases ht : c ∈ top q P
  · left; exact ht
  · right; exact ⟨C.subset P hc, ht, bottom_chosen_minor C hAA hc ht⟩

lemma Cm_card (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    (Cm C P).card = (topMin q P).card + (CA C P).card := by
  have h1 := C_card_decomp C hAA P
  have h2 := Finset.card_filter_add_card_filter_not (s := C.C P) (fun s => P.τ s = true)
  simp only [Bool.not_eq_true] at h2
  unfold Cm; unfold CM at h1; omega

end AA2

section Restr
variable {𝒮 : Type*} [DecidableEq 𝒮] {q : ℕ}

lemma top_botMin_sub (P : Problem 𝒮) (X : Finset 𝒮) (hX : X ⊆ botMin q P) :
    top q P ∪ X ⊆ P.S := Finset.union_subset (top_subset q P) (fun x hx => (mem_botMin.1 (hX hx)).1)

lemma rank_restrict_top (P : Problem 𝒮) (S' : Finset 𝒮) (h : S' ⊆ P.S) (hT : top q P ⊆ S')
    {s : 𝒮} (hs : s ∈ top q P) : rank (P.restrict S' h) s = rank P s := by
  rw [rank_eq, rank_eq]; congr 1
  exact cnt_sub h (fun y hy hlt => hT (top_down hs hy hlt))

lemma top_restrict (P : Problem 𝒮) (S' : Finset 𝒮) (h : S' ⊆ P.S) (hT : top q P ⊆ S')
    (hq : q ≤ P.S.card) : top q (P.restrict S' h) = top q P := by
  ext s
  constructor
  · intro hs
    by_contra hsT
    have hsS' : s ∈ S' := top_subset q _ hs
    rw [mem_top] at hs
    have hsub : top q P ⊆ S'.filter (fun y => P.pri y < P.pri s) := by
      intro y hy
      exact Finset.mem_filter.2 ⟨hT hy, top_lt_bottom hy (h hsS') hsT⟩
    have := Finset.card_le_card hsub
    rw [top_card] at this
    have h2 := hs.2; unfold cnt at h2
    change (S'.filter (fun y => P.pri y < P.pri s)).card < q at h2
    omega
  · intro hs
    have := rank_restrict_top P S' h hT hs
    have hs2 := hs
    unfold top at hs2 ⊢; rw [Finset.mem_filter] at hs2 ⊢
    exact ⟨hT hs, this ▸ hs2.2⟩

lemma typeAt_restrict_le (P : Problem 𝒮) (S' : Finset 𝒮) (h : S' ⊆ P.S) (hT : top q P ⊆ S')
    (hq : q ≤ P.S.card) {k : ℕ} (hk : k ≤ q) :
    typeAt (P.restrict S' h) k = typeAt P k := by
  apply typeAt_eq_of
  intro b
  constructor
  · rintro ⟨s, hs, hk', hb⟩
    have hsT : s ∈ top q P := by
      rw [← top_restrict P S' h hT hq]; unfold top; rw [Finset.mem_filter]; exact ⟨hs, by omega⟩
    refine ⟨s, top_subset q P hsT, ?_, hb⟩
    rw [← rank_restrict_top P S' h hT hsT]; exact hk'
  · rintro ⟨s, hs, hk', hb⟩
    have hsT : s ∈ top q P := by unfold top; rw [Finset.mem_filter]; exact ⟨hs, by omega⟩
    exact ⟨s, hT hsT, by rw [rank_restrict_top P S' h hT hsT]; exact hk', hb⟩

lemma typeAt_restrict_gt (P : Problem 𝒮) (S' : Finset 𝒮) (h : S' ⊆ P.S) (hT : top q P ⊆ S')
    (hq : q ≤ P.S.card) (hX : ∀ x ∈ S', x ∉ top q P → P.τ x = true) {k : ℕ} (hk : q < k)
    (hk2 : k ≤ S'.card) : typeAt (P.restrict S' h) k = some true := by
  obtain ⟨s, hs, hrk⟩ := exists_rank_eq (P := P.restrict S' h) (k := k) (by omega) hk2
  rw [typeAt_some_iff]
  refine ⟨s, hs, hrk, hX s hs ?_⟩
  rw [← top_restrict P S' h hT hq]
  intro hst; unfold top at hst; rw [Finset.mem_filter] at hst; omega

lemma card_top_union (P : Problem 𝒮) (X : Finset 𝒮) (hX : X ⊆ botMin q P) (hq : q ≤ P.S.card) :
    (top q P ∪ X).card = q + X.card := by
  rw [Finset.card_union_of_disjoint, top_card]
  · omega
  · rw [Finset.disjoint_left]; intro x h1 h2; exact (mem_botMin.1 (hX h2)).2.1 h1

end Restr

section Lemma1
variable {𝒮 : Type*} [DecidableEq 𝒮] {q : ℕ} (C : ChoiceRule 𝒮 q)

/-- Two problems with the same top-tier pattern, each restricted to its top tier plus
equally many bottom-tier minorities, have the same number of affirmative-action admits. -/
lemma CA_restrict_eq (hAA : IsAffirmativeActionRule C) (P P' : Problem 𝒮)
    (hq : q ≤ P.S.card) (hq' : q ≤ P'.S.card)
    (htype : ∀ k, 1 ≤ k → k ≤ q → typeAt P k = typeAt P' k)
    (X X' : Finset 𝒮) (hX : X ⊆ botMin q P) (hX' : X' ⊆ botMin q P') (hXX : X.card = X'.card) :
    (CA C (P.restrict _ (top_botMin_sub P X hX))).card =
      (CA C (P'.restrict _ (top_botMin_sub P' X' hX'))).card := by
  apply CA_card_eq_of_typeAt C hAA
  · show (top q P ∪ X).card = (top q P' ∪ X').card
    rw [card_top_union P X hX hq, card_top_union P' X' hX' hq', hXX]
  · intro k hk1 hk2
    change k ≤ (top q P ∪ X).card at hk2
    by_cases hkq : k ≤ q
    · rw [typeAt_restrict_le P _ _ Finset.subset_union_left hq hkq,
        typeAt_restrict_le P' _ _ Finset.subset_union_left hq' hkq]
      exact htype k hk1 hkq
    · rw [not_le] at hkq
      have hXm : ∀ (Q : Problem 𝒮) (Y : Finset 𝒮), Y ⊆ botMin q Q →
          ∀ x ∈ top q Q ∪ Y, x ∉ top q Q → Q.τ x = true := by
        intro Q Y hY x hx hxt
        rcases Finset.mem_union.1 hx with h | h
        · exact absurd h hxt
        · exact (mem_botMin.1 (hY h)).2.2
      rw [typeAt_restrict_gt P _ _ Finset.subset_union_left hq (hXm P X hX) hkq hk2,
        typeAt_restrict_gt P' _ _ Finset.subset_union_left hq' (hXm P' X' hX') hkq
          (by rw [card_top_union P' X' hX' hq', ← hXX, ← card_top_union P X hX hq]; exact hk2)]

lemma CA_restrict_botMin (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (P : Problem 𝒮) (hq : q ≤ P.S.card) (X : Finset 𝒮) (hX : X ⊆ botMin q P)
    (hCX : CA C P ⊆ X) :
    CA C (P.restrict _ (top_botMin_sub P X hX)) = CA C P := by
  have hC : C.C P ⊆ top q P ∪ X := by
    intro c hc
    by_cases ht : c ∈ top q P
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _ (hCX ((mem_CA C).2 ⟨hc, bottom_chosen_minor C hAA hc ht, ht⟩))
  have hCe := restrict_eq C hAA hsub P _ (top_botMin_sub P X hX) hC
  have hte := top_restrict P _ (top_botMin_sub P X hX) Finset.subset_union_left hq
  ext s
  rw [mem_CA, mem_CA, hCe, hte]
  rfl

lemma rank_eq_of_topCoincide {P P' : Problem 𝒮} (htop : TopCoincide q P P') {s : 𝒮}
    (hs : s ∈ top q P) : rank P s = rank P' s := by
  have hs' : s ∈ top q P' := htop.1 ▸ hs
  rw [rank_eq, rank_eq, ← cnt_sub (top_subset q P) (fun y hy hlt => top_down hs hy hlt),
    ← cnt_sub (top_subset q P') (fun y hy hlt => top_down hs' hy hlt), ← htop.1]
  congr 1; unfold cnt; congr 1
  apply Finset.filter_congr
  intro y hy; exact htop.2 y hy s hs

lemma typeAt_eq_of_topCoincide {P P' : Problem 𝒮} (htop : TopCoincide q P P')
    (hτ : ∀ s ∈ top q P, P'.τ s = P.τ s) {k : ℕ} (hk : k ≤ q) : typeAt P k = typeAt P' k := by
  apply typeAt_eq_of
  intro b
  constructor
  · rintro ⟨s, hs, hk', hb⟩
    have hsT : s ∈ top q P := by unfold top; rw [Finset.mem_filter]; exact ⟨hs, by omega⟩
    exact ⟨s, top_subset q P' (htop.1 ▸ hsT), (rank_eq_of_topCoincide htop hsT) ▸ hk',
      (hτ s hsT).trans hb⟩
  · rintro ⟨s, hs, hk', hb⟩
    have hsT' : s ∈ top q P' := by unfold top; rw [Finset.mem_filter]; exact ⟨hs, by omega⟩
    have hsT : s ∈ top q P := htop.1 ▸ hsT'
    exact ⟨s, top_subset q P hsT, (rank_eq_of_topCoincide htop hsT).trans hk',
      (hτ s hsT).symm.trans hb⟩

end Lemma1

section Canon
variable {𝒮 : Type*} [DecidableEq 𝒮] {q : ℕ} (C : ChoiceRule 𝒮 q)

lemma topMaj_image (P : Problem 𝒮) :
    (topMaj q P).image (rank P) = (Finset.Icc 1 q).filter (fun k => typeAt P k = some false) := by
  ext k
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc, mem_topMaj]
  constructor
  · rintro ⟨s, ⟨hs, hτ⟩, rfl⟩
    have hs2 := hs; unfold top at hs2; rw [Finset.mem_filter] at hs2
    refine ⟨⟨by rw [rank_eq]; omega, hs2.2⟩, ?_⟩
    rw [typeAt_some_iff]; exact ⟨s, hs2.1, rfl, hτ⟩
  · rintro ⟨⟨hk1, hk2⟩, h⟩
    rw [typeAt_some_iff] at h
    obtain ⟨s, hs, hk, hτ⟩ := h
    refine ⟨s, ⟨?_, hτ⟩, hk⟩
    unfold top; rw [Finset.mem_filter]; exact ⟨hs, by omega⟩

lemma topMaj_card_eq {P P' : Problem 𝒮} (h : ∀ k, 1 ≤ k → k ≤ q → typeAt P k = typeAt P' k) :
    (topMaj q P).card = (topMaj q P').card := by
  have hinj : ∀ Q : Problem 𝒮, Set.InjOn (rank Q) ↑(topMaj q Q) := by
    intro Q x hx y hy hxy
    exact rank_inj (top_subset q Q (mem_topMaj.1 hx).1) (top_subset q Q (mem_topMaj.1 hy).1) hxy
  rw [← Finset.card_image_of_injOn (hinj P), ← Finset.card_image_of_injOn (hinj P'),
    topMaj_image, topMaj_image]
  congr 1
  apply Finset.filter_congr
  intro k hk; rw [Finset.mem_Icc] at hk; rw [h k hk.1 hk.2]

/-- the set whose supremum is the canonical reserve -/
def canonSet (P : Problem 𝒮) : Set ℕ :=
  {n | ∃ P' : Problem 𝒮, (∀ k, 1 ≤ k → k ≤ q → typeAt P' k = typeAt P k) ∧ n = (CA C P').card}

lemma canonicalReserve_eq (P : Problem 𝒮) : canonicalReserve C P = sSup (canonSet C P) := rfl

lemma canonSet_bdd (P : Problem 𝒮) : BddAbove (canonSet C P) :=
  ⟨q, by rintro n ⟨P', -, rfl⟩; exact CA_card_le_q C P'⟩

lemma canonSet_nonempty (P : Problem 𝒮) : (canonSet C P).Nonempty :=
  ⟨_, P, fun _ _ _ => rfl, rfl⟩

lemma le_canon {P P' : Problem 𝒮} (h : ∀ k, 1 ≤ k → k ≤ q → typeAt P' k = typeAt P k) :
    (CA C P').card ≤ canonicalReserve C P :=
  le_csSup (canonSet_bdd C P) ⟨P', h, rfl⟩

lemma canon_attained (P : Problem 𝒮) : ∃ P' : Problem 𝒮,
    (∀ k, 1 ≤ k → k ≤ q → typeAt P' k = typeAt P k) ∧ canonicalReserve C P = (CA C P').card :=
  Nat.sSup_mem (canonSet_nonempty C P) (canonSet_bdd C P)

lemma canon_congr {P P' : Problem 𝒮} (h : ∀ k, 1 ≤ k → k ≤ q → typeAt P k = typeAt P' k) :
    canonicalReserve C P = canonicalReserve C P' := by
  rw [canonicalReserve_eq, canonicalReserve_eq]; congr 1
  ext n; simp only [canonSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P'', h1, rfl⟩; exact ⟨P'', fun k hk1 hk2 => (h1 k hk1 hk2).trans (h k hk1 hk2), rfl⟩
  · rintro ⟨P'', h1, rfl⟩; exact ⟨P'', fun k hk1 hk2 => (h1 k hk1 hk2).trans (h k hk1 hk2).symm, rfl⟩

lemma canon_le_topMaj (hAA : IsAffirmativeActionRule C) (P : Problem 𝒮) :
    canonicalReserve C P ≤ (topMaj q P).card := by
  rw [canonicalReserve_eq]
  apply csSup_le (canonSet_nonempty C P)
  rintro n ⟨P', h, rfl⟩
  rw [topMaj_card_eq (P := P) (P' := P') (fun k hk1 hk2 => (h k hk1 hk2).symm)]
  exact CA_card_le_topMaj C hAA P'

lemma q_le_of_pattern {P P' : Problem 𝒮} (hq : 1 ≤ q)
    (h : ∀ k, 1 ≤ k → k ≤ q → typeAt P' k = typeAt P k) (hP : q ≤ P.S.card) : q ≤ P'.S.card := by
  obtain ⟨s, hs, hk⟩ := exists_rank_eq (P := P) (k := q) hq hP
  have h1 : typeAt P q = some (P.τ s) := (typeAt_some_iff P q _).2 ⟨s, hs, hk, rfl⟩
  rw [← h q hq le_rfl, typeAt_some_iff] at h1
  obtain ⟨s', hs', hk', -⟩ := h1
  rw [← hk']; exact rank_le_card hs'

/-- key lower bound: with the same top-tier pattern, `P` admits at least
`min |C^A(P')| |B^m(P)|` minority students via affirmative action. -/
lemma CA_ge_min (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C) (hq : 1 ≤ q)
    {P P' : Problem 𝒮} (h : ∀ k, 1 ≤ k → k ≤ q → typeAt P' k = typeAt P k) :
    min (CA C P').card (botMin q P).card ≤ (CA C P).card := by
  set b := min (CA C P').card (botMin q P).card with hb
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · rw [hb0]; exact Nat.zero_le _
  have hbm : 0 < (botMin q P).card := lt_of_lt_of_le hbpos (min_le_right _ _)
  have hCA : 0 < (CA C P').card := lt_of_lt_of_le hbpos (min_le_left _ _)
  obtain ⟨x0, hx0⟩ := Finset.card_pos.1 hbm
  obtain ⟨y0, hy0⟩ := Finset.card_pos.1 hCA
  have hqP : q ≤ P.S.card := (card_S_gt_of_bottom (mem_botMin.1 hx0).1 (mem_botMin.1 hx0).2.1).le
  have hqP' : q ≤ P'.S.card := by
    have hy := CA_sub_botMin C P' hy0
    exact (card_S_gt_of_bottom (mem_botMin.1 hy).1 (mem_botMin.1 hy).2.1).le
  set X := (botMin q P).filter (fun x => cnt (botMin q P) P.pri x < b) with hXdef
  have hXsub : X ⊆ botMin q P := Finset.filter_subset _ _
  have hXcard : X.card = b := by
    rw [hXdef, card_filter_cnt_lt (botMin_inj P)]; omega
  obtain ⟨X', hX'sub, hX'card⟩ := Finset.exists_subset_card_eq (s := CA C P') (n := b)
    (min_le_left _ _)
  have hX'bm : X' ⊆ botMin q P' := hX'sub.trans (CA_sub_botMin C P')
  have heq := CA_restrict_eq C hAA P P' hqP hqP' (fun k hk1 hk2 => (h k hk1 hk2).symm)
    X X' hXsub hX'bm (hXcard.trans hX'card.symm)
  -- the restricted problem of P' has at least b students chosen via affirmative action
  have hge : b ≤ (CA C (P'.restrict _ (top_botMin_sub P' X' hX'bm))).card := by
    rw [← hX'card]
    apply Finset.card_le_card
    intro x hx
    have hxCA := hX'sub hx
    rw [mem_CA] at hxCA ⊢
    refine ⟨hsub P' x hxCA.1 _ (top_botMin_sub P' X' hX'bm) (Finset.mem_union_right _ hx),
      hxCA.2.1, ?_⟩
    rw [top_restrict P' _ _ Finset.subset_union_left hqP']; exact hxCA.2.2
  by_contra hlt
  rw [not_le] at hlt
  have hsubX : CA C P ⊆ X := by
    rw [CA_prefix C hAA P]; exact filter_cnt_mono _ _ hlt.le
  have := CA_restrict_botMin C hAA hsub P hqP X hXsub hsubX
  rw [this] at heq; omega

lemma CA_eq_min_canon (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C) (hq : 1 ≤ q)
    (P : Problem 𝒮) :
    (CA C P).card = min (canonicalReserve C P) (botMin q P).card := by
  obtain ⟨P', h, hR⟩ := canon_attained C P
  have h1 := CA_ge_min C hAA hsub hq h
  have h2 := le_canon C (P := P) (P' := P) (fun _ _ _ => rfl)
  have h3 := CA_card_le_botMin C P
  rw [← hR] at h1
  omega

theorem canonical_represents (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (hq : 1 ≤ q) :
    IsReserveFunction q (canonicalReserve C) ∧ IsReserveRep C (canonicalReserve C) := by
  refine ⟨⟨canon_le_topMaj C hAA, fun P P' h => canon_congr C h⟩, fun P => ?_⟩
  rw [C_eq_reserveChoice C hAA P, reserveChoice_min P (canonicalReserve C P),
    ← CA_eq_min_canon C hAA hsub hq P]

end Canon
end ACInfra

open AffirmativeChoice.Reserve ACInfra

theorem solution {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C) :
    IsReserveFunction q (canonicalReserve C) ∧ IsReserveRep C (canonicalReserve C) :=
  canonical_represents C hAA hsub (by omega)
