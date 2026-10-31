-- Prove2me | solution 1 for AffirmativeChoice.Reserve.canonical_satisfies_B2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:28:12.819352+00:00
-- url     : https://prove2.me/submissions/64865e75-7127-4a7f-a63e-91b71317a5d7

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

section Removal
variable {𝒮 : Type*} [DecidableEq 𝒮] {q : ℕ} (C : ChoiceRule 𝒮 q)

lemma top_char (Q : Problem 𝒮) (T : Finset 𝒮) (hT : T ⊆ Q.S) (hc : T.card = q)
    (h : ∀ t ∈ T, ∀ s ∈ Q.S, s ∉ T → Q.pri t < Q.pri s) : top q Q = T := by
  ext s
  rw [mem_top]
  constructor
  · rintro ⟨hs, hcnt⟩
    by_contra hsT
    have hsub : T ⊆ Q.S.filter (fun y => Q.pri y < Q.pri s) := by
      intro t ht; exact Finset.mem_filter.2 ⟨hT ht, h t ht s hs hsT⟩
    have := Finset.card_le_card hsub
    unfold cnt at hcnt; omega
  · intro hsT
    refine ⟨hT hsT, ?_⟩
    have hsub : Q.S.filter (fun y => Q.pri y < Q.pri s) ⊆ T.erase s := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [Finset.mem_erase]
      refine ⟨fun hys => by rw [hys] at hy; exact lt_irrefl _ hy.2, ?_⟩
      by_contra hyT
      have := h s hsT y hy.1 hyT; omega
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hsT] at h1
    have : 0 < T.card := Finset.card_pos.2 ⟨s, hsT⟩
    unfold cnt; omega

lemma CA_card_eq_of_order (hAA : IsAffirmativeActionRule C) {P1 P2 : Problem 𝒮}
    (hS : P1.S = P2.S) (hτ : ∀ x ∈ P1.S, P1.τ x = P2.τ x)
    (hpri : ∀ x ∈ P1.S, ∀ y ∈ P1.S, (P1.pri x < P1.pri y ↔ P2.pri x < P2.pri y)) :
    (CA C P1).card = (CA C P2).card := by
  have hrank : ∀ x ∈ P1.S, rank P1 x = rank P2 x := by
    intro x hx
    rw [rank_eq, rank_eq]; congr 1; unfold cnt; rw [← hS]; congr 1
    apply Finset.filter_congr; intro y hy; exact hpri y hy x hx
  apply CA_card_eq_of_typeAt C hAA (by rw [hS])
  intro k _ _
  apply typeAt_eq_of
  intro b
  constructor
  · rintro ⟨x, hx, hk, hb⟩; exact ⟨x, hS ▸ hx, (hrank x hx) ▸ hk, (hτ x hx) ▸ hb⟩
  · rintro ⟨x, hx, hk, hb⟩
    have hx1 : x ∈ P1.S := hS ▸ hx
    exact ⟨x, hx1, (hrank x hx1).trans hk, (hτ x hx1).trans hb⟩

/-- the student of rank `q+1` is above every other bottom-tier student -/
lemma b1_lt {P : Problem 𝒮} {b1 s : 𝒮} (hb1 : b1 ∈ P.S) (hrk : rank P b1 = q + 1)
    (hs : s ∈ P.S) (hst : s ∉ top q P) (hsb : s ≠ b1) : P.pri b1 < P.pri s := by
  have h1 := (not_top_iff hs).1 hst
  have h2 : rank P s ≠ rank P b1 := fun h => hsb (rank_inj hs hb1 h)
  simp only [rank_eq] at h1 h2 hrk
  exact (cnt_lt_iff P.inj hb1 hs).1 (by omega)

lemma b1_not_top {P : Problem 𝒮} {b1 : 𝒮} (hb1 : b1 ∈ P.S) (hrk : rank P b1 = q + 1) :
    b1 ∉ top q P := by
  rw [not_top_iff hb1]; omega

lemma top_erase (P : Problem 𝒮) (hqS : q < P.S.card) {z b1 : 𝒮} (hz : z ∈ top q P)
    (hb1 : b1 ∈ P.S) (hrk : rank P b1 = q + 1) :
    top q (P.restrict (P.S.erase z) (Finset.erase_subset _ _)) = insert b1 ((top q P).erase z) := by
  have hb1t := b1_not_top hb1 hrk
  apply top_char
  · intro x hx
    rw [Finset.mem_insert, Finset.mem_erase] at hx
    show x ∈ P.S.erase z
    rw [Finset.mem_erase]
    rcases hx with rfl | ⟨hxz, hx⟩
    · exact ⟨fun h => hb1t (h ▸ hz), hb1⟩
    · exact ⟨hxz, top_subset q P hx⟩
  · rw [Finset.card_insert_of_notMem (fun h => hb1t (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hz, top_card]
    have : 0 < q := by
      have := Finset.card_pos.2 ⟨z, hz⟩; rw [top_card] at this; omega
    omega
  · intro t ht s hs hsT
    show P.pri t < P.pri s
    change s ∈ P.S.erase z at hs
    rw [Finset.mem_erase] at hs
    rw [Finset.mem_insert, Finset.mem_erase, not_or, not_and] at hsT
    have hst : s ∉ top q P := fun h => hsT.2 hs.1 h
    rw [Finset.mem_insert, Finset.mem_erase] at ht
    rcases ht with rfl | ⟨-, ht⟩
    · exact b1_lt hb1 hrk hs.2 hst hsT.1
    · exact top_lt_bottom ht hs.2 hst

/-- removal of a top-tier student when the rank-`(q+1)` student is a minority -/
lemma removal (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (P : Problem 𝒮) (hqS : q < P.S.card) {z b1 : 𝒮} (hz : z ∈ top q P)
    (hb1 : b1 ∈ P.S) (hrk : rank P b1 = q + 1) (hτb : P.τ b1 = true) :
    (CA C P).card ≤ (CA C (P.restrict (P.S.erase z) (Finset.erase_subset _ _))).card + 1 ∧
    (CA C (P.restrict (P.S.erase z) (Finset.erase_subset _ _))).card ≤ (CA C P).card ∧
    (z ∉ C.C P → b1 ∈ CA C P →
      (CA C (P.restrict (P.S.erase z) (Finset.erase_subset _ _))).card + 1 = (CA C P).card) := by
  set Q := P.restrict (P.S.erase z) (Finset.erase_subset _ _) with hQ
  have hb1t := b1_not_top hb1 hrk
  have htQ : top q Q = insert b1 ((top q P).erase z) := top_erase P hqS hz hb1 hrk
  have hzS := top_subset q P hz
  -- lower bound
  have hlow : (CA C P).erase b1 ⊆ CA C Q := by
    intro x hx
    rw [Finset.mem_erase, mem_CA] at hx
    obtain ⟨hxb, hxC, hxτ, hxt⟩ := hx
    have hxz : x ≠ z := fun h => hxt (h ▸ hz)
    rw [mem_CA]
    refine ⟨hsub P x hxC _ (Finset.erase_subset _ _) (Finset.mem_erase.2 ⟨hxz, C.subset P hxC⟩),
      hxτ, ?_⟩
    rw [htQ, Finset.mem_insert, Finset.mem_erase, not_or, not_and]
    exact ⟨hxb, fun _ h => hxt h⟩
  have h1 : (CA C P).card ≤ (CA C Q).card + 1 := by
    have := Finset.card_le_card hlow
    have := Finset.pred_card_le_card_erase (s := CA C P) (a := b1)
    omega
  -- characterization of CA Q elements
  have hmemQ : ∀ x ∈ CA C Q, x ≠ b1 ∧ x ≠ z ∧ x ∉ top q P := by
    intro x hx
    rw [mem_CA] at hx
    have hxS : x ∈ P.S.erase z := C.subset Q hx.1
    rw [Finset.mem_erase] at hxS
    have := hx.2.2
    rw [htQ, Finset.mem_insert, Finset.mem_erase, not_or, not_and] at this
    exact ⟨this.1, hxS.1, fun h => this.2 hxS.1 h⟩
  by_cases hzC : z ∈ C.C P
  · -- z chosen
    set E := (C.C P).erase z with hE
    have hEsub : E ⊆ C.C Q := by
      intro x hx
      rw [Finset.mem_erase] at hx
      exact hsub P x hx.2 _ (Finset.erase_subset _ _) (Finset.mem_erase.2 ⟨hx.1, C.subset P hx.2⟩)
    have hCQ : (C.C Q).card = q := by
      rw [C_card C hAA]; show min (P.S.erase z).card q = q
      rw [Finset.card_erase_of_mem hzS]; omega
    have hCP : (C.C P).card = q := by rw [C_card C hAA]; omega
    have hEc : E.card = q - 1 := by rw [hE, Finset.card_erase_of_mem hzC, hCP]
    have hD : (C.C Q \ E).card = 1 := by
      rw [Finset.card_sdiff_of_subset hEsub, hCQ, hEc]
      have : 0 < q := by have := Finset.card_pos.2 ⟨z, hz⟩; rw [top_card] at this; omega
      omega
    have hsubU : CA C Q ⊆ (CA C P).erase b1 ∪ (C.C Q \ E).erase b1 := by
      intro x hx
      obtain ⟨hxb, hxz, hxt⟩ := hmemQ x hx
      have hx' := (mem_CA C).1 hx
      by_cases hxE : x ∈ E
      · apply Finset.mem_union_left
        rw [Finset.mem_erase, mem_CA]
        exact ⟨hxb, (Finset.mem_erase.1 hxE).2, hx'.2.1, hxt⟩
      · apply Finset.mem_union_right
        rw [Finset.mem_erase, Finset.mem_sdiff]
        exact ⟨hxb, hx'.1, hxE⟩
    have hcardU := (Finset.card_le_card hsubU).trans (Finset.card_union_le _ _)
    refine ⟨h1, ?_, fun h => absurd hzC h⟩
    by_cases hb1CA : b1 ∈ CA C P
    · rw [Finset.card_erase_of_mem hb1CA] at hcardU
      have := Finset.card_erase_le (s := C.C Q \ E) (a := b1)
      have : 0 < (CA C P).card := Finset.card_pos.2 ⟨b1, hb1CA⟩
      omega
    · -- then nothing is chosen via affirmative action
      have hCA0 : CA C P = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        apply hb1CA
        have hx' := (mem_CA C).1 hx
        have hxb : x ≠ b1 := fun h => hb1CA (h ▸ hx)
        rw [mem_CA]
        exact ⟨minor_down C hAA hx'.1 hb1 hτb (b1_lt hb1 hrk (C.subset P hx'.1) hx'.2.2 hxb),
          hτb, hb1t⟩
      have hb1CQ : b1 ∈ C.C Q := by
        apply topMin_sub C hAA Q
        rw [mem_topMin, htQ]; exact ⟨Finset.mem_insert_self _ _, hτb⟩
      have hb1E : b1 ∉ E := by
        intro h
        apply hb1CA; rw [mem_CA]; exact ⟨(Finset.mem_erase.1 h).2, hτb, hb1t⟩
      have : ((C.C Q \ E).erase b1).card = 0 := by
        rw [Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hb1CQ, hb1E⟩), hD]
      rw [hCA0] at hcardU ⊢
      simp only [Finset.erase_empty, Finset.card_empty, zero_add] at hcardU
      simp only [Finset.card_empty]; omega
  · -- z not chosen: the choice is unchanged
    have hCe : C.C Q = C.C P := by
      apply restrict_eq C hAA hsub P _ (Finset.erase_subset _ _)
      intro x hx; exact Finset.mem_erase.2 ⟨fun h => hzC (h ▸ hx), C.subset P hx⟩
    have hCAe : CA C Q = (CA C P).erase b1 := by
      apply Finset.Subset.antisymm _ hlow
      intro x hx
      obtain ⟨hxb, -, hxt⟩ := hmemQ x hx
      have hx' := (mem_CA C).1 hx
      rw [Finset.mem_erase, mem_CA, ← hCe]
      exact ⟨hxb, hx'.1, hx'.2.1, hxt⟩
    refine ⟨h1, ?_, fun _ hb => ?_⟩
    · rw [hCAe]; exact Finset.card_erase_le
    · rw [hCAe, Finset.card_erase_of_mem hb]
      have : 0 < (CA C P).card := Finset.card_pos.2 ⟨b1, hb⟩
      omega

end Removal

section Ext
variable {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] {q : ℕ}

def extK (q : ℕ) (P : Problem 𝒮) : ℕ := (top q P).sup P.pri + 1

noncomputable def extPri (q : ℕ) (P : Problem 𝒮) (s : 𝒮) : ℕ :=
  if s ∈ top q P then P.pri s else extK q P + ((Fintype.equivFin 𝒮 s : Fin _) : ℕ)

def extTau (q : ℕ) (P : Problem 𝒮) (s : 𝒮) : Bool := if s ∈ top q P then P.τ s else true

lemma extPri_top {P : Problem 𝒮} {s : 𝒮} (hs : s ∈ top q P) : extPri q P s = P.pri s := by
  unfold extPri; rw [if_pos hs]

lemma extPri_bot {P : Problem 𝒮} {s : 𝒮} (hs : s ∉ top q P) :
    extPri q P s = extK q P + ((Fintype.equivFin 𝒮 s : Fin _) : ℕ) := by
  unfold extPri; rw [if_neg hs]

lemma extTau_top {P : Problem 𝒮} {s : 𝒮} (hs : s ∈ top q P) : extTau q P s = P.τ s := by
  unfold extTau; rw [if_pos hs]

lemma extTau_bot {P : Problem 𝒮} {s : 𝒮} (hs : s ∉ top q P) : extTau q P s = true := by
  unfold extTau; rw [if_neg hs]

lemma extPri_lt {P : Problem 𝒮} {t s : 𝒮} (ht : t ∈ top q P) (hs : s ∉ top q P) :
    extPri q P t < extPri q P s := by
  rw [extPri_top ht, extPri_bot hs]
  have := Finset.le_sup (f := P.pri) ht
  unfold extK; omega

lemma extPri_bot_iff {P : Problem 𝒮} {s s' : 𝒮} (hs : s ∉ top q P) (hs' : s' ∉ top q P) :
    extPri q P s < extPri q P s' ↔
      ((Fintype.equivFin 𝒮 s : Fin _) : ℕ) < ((Fintype.equivFin 𝒮 s' : Fin _) : ℕ) := by
  rw [extPri_bot hs, extPri_bot hs']; omega

lemma extPri_inj (P : Problem 𝒮) : Set.InjOn (extPri q P) ↑(Finset.univ : Finset 𝒮) := by
  intro x _ y _ h
  by_cases hx : x ∈ top q P <;> by_cases hy : y ∈ top q P
  · rw [extPri_top hx, extPri_top hy] at h
    exact P.inj (top_subset q P hx) (top_subset q P hy) h
  · have := extPri_lt (P := P) hx hy; omega
  · have := extPri_lt (P := P) hy hx; omega
  · rw [extPri_bot hx, extPri_bot hy] at h
    have : (Fintype.equivFin 𝒮 x) = (Fintype.equivFin 𝒮 y) := Fin.ext (by omega)
    exact (Fintype.equivFin 𝒮).injective this

/-- the extension of the top tier of `P` by all other students, as minorities ranked below -/
noncomputable def Ext (q : ℕ) (P : Problem 𝒮) : Problem 𝒮 :=
  ⟨Finset.univ, extTau q P, extPri q P, extPri_inj P⟩

lemma top_Ext {P : Problem 𝒮} (hq : q ≤ P.S.card) : top q (Ext q P) = top q P := by
  apply top_char
  · intro x _; exact Finset.mem_univ x
  · rw [top_card]; omega
  · intro t ht s _ hs; exact extPri_lt ht hs

lemma topCoincide_Ext {P : Problem 𝒮} (hq : q ≤ P.S.card) : TopCoincide q P (Ext q P) := by
  refine ⟨(top_Ext hq).symm, fun s hs s' hs' => ?_⟩
  show P.pri s < P.pri s' ↔ extPri q P s < extPri q P s'
  rw [extPri_top hs, extPri_top hs']

lemma typeAt_Ext {P : Problem 𝒮} (hq : q ≤ P.S.card) {k : ℕ} (hk : k ≤ q) :
    typeAt (Ext q P) k = typeAt P k :=
  (typeAt_eq_of_topCoincide (topCoincide_Ext hq) (fun s hs => extTau_top hs) hk).symm

lemma botMin_Ext {P : Problem 𝒮} (hq : q ≤ P.S.card) :
    (botMin q (Ext q P)).card = Fintype.card 𝒮 - q := by
  have : botMin q (Ext q P) = Finset.univ \ top q P := by
    ext x
    rw [mem_botMin, top_Ext hq, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, extTau_bot h2⟩
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, top_card]
  omega

variable (C : ChoiceRule 𝒮 q)

lemma CA_empty_of_le (P : Problem 𝒮) (h : P.S.card ≤ q) : CA C P = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
  rw [mem_CA, top_eq_S h] at hx; exact hx.2.2 (C.subset P hx.1)

lemma canon_le_card (hAA : IsAffirmativeActionRule C) (hq1 : 1 ≤ q) {P : Problem 𝒮}
    (hq : q ≤ P.S.card) : canonicalReserve C P ≤ Fintype.card 𝒮 - q := by
  rw [canonicalReserve_eq]
  apply csSup_le (canonSet_nonempty C P)
  rintro n ⟨P', h, rfl⟩
  have hq' := q_le_of_pattern hq1 h hq
  have h1 := CA_card_le_botMin C P'
  have h2 : botMin q P' ⊆ P'.S \ top q P' := by
    intro x hx; rw [mem_botMin] at hx; exact Finset.mem_sdiff.2 ⟨hx.1, hx.2.1⟩
  have h3 := Finset.card_le_card h2
  rw [Finset.card_sdiff_of_subset (top_subset q P'), top_card] at h3
  have h4 : P'.S.card ≤ Fintype.card 𝒮 := Finset.card_le_univ _
  omega

lemma canon_Ext (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C) (hq1 : 1 ≤ q)
    {P : Problem 𝒮} (hq : q ≤ P.S.card) :
    canonicalReserve C P = (CA C (Ext q P)).card := by
  rw [CA_eq_min_canon C hAA hsub hq1, botMin_Ext hq,
    canon_congr C (P := Ext q P) (P' := P) (fun k _ hk => typeAt_Ext hq hk)]
  have := canon_le_card C hAA hq1 hq
  omega

lemma canon_zero_of_lt (hAA : IsAffirmativeActionRule C) {P : Problem 𝒮} (h : P.S.card < q) :
    canonicalReserve C P = 0 := by
  rw [canonicalReserve_eq]
  apply Nat.eq_zero_of_le_zero
  apply csSup_le (canonSet_nonempty C P)
  rintro n ⟨P', hp, rfl⟩
  have hnone : typeAt P (P.S.card + 1) = none := by
    rw [typeAt_none_iff]; rintro ⟨s, hs, hk⟩; have := rank_le_card hs; omega
  rw [← hp _ (by omega) (by omega), typeAt_none_iff] at hnone
  have : P'.S.card ≤ P.S.card := by
    by_contra hc; rw [not_le] at hc
    exact hnone (exists_rank_eq (by omega) (by omega))
  rw [CA_empty_of_le C P' (by omega)]; simp

/-- the rank-`(q+1)` student of the extension -/
lemma exists_b1 {P : Problem 𝒮} (hq : q ≤ P.S.card) (hU : q < Fintype.card 𝒮) :
    ∃ b1, rank (Ext q P) b1 = q + 1 ∧ b1 ∉ top q P := by
  obtain ⟨b1, -, hb⟩ := exists_rank_eq (P := Ext q P) (k := q + 1) (by omega)
    (by show q + 1 ≤ (Finset.univ : Finset 𝒮).card; rw [Finset.card_univ]; omega)
  refine ⟨b1, hb, ?_⟩
  rw [← top_Ext hq]; exact b1_not_top (Finset.mem_univ _) hb

end Ext

section Improve
variable {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] {q : ℕ}

lemma top_improve {P : Problem 𝒮} {z : 𝒮} {pri' : 𝒮 → ℕ} (h : Improvement P z pri')
    (hz : z ∈ top q P) (hq : q ≤ P.S.card) : top q (P.withPri pri' h.inj) = top q P := by
  apply top_char
  · exact top_subset q P
  · rw [top_card]; omega
  · intro t ht u hu hut
    show pri' t < pri' u
    have hlt := top_lt_bottom ht hu hut
    by_cases htz : t = z
    · subst htz; exact h.weak u hu hlt
    · have huz : u ≠ z := fun e => hut (e ▸ hz)
      exact (h.others t (top_subset q P ht) u hu htz huz).1 hlt

lemma ext_improve {P : Problem 𝒮} {z : 𝒮} {pri' : 𝒮 → ℕ} (h : Improvement P z pri')
    (hz : z ∈ top q P) (hq : q ≤ P.S.card) :
    Improvement (Ext q P) z (Ext q (P.withPri pri' h.inj)).pri := by
  set P1 := P.withPri pri' h.inj
  have ht1 : top q P1 = top q P := top_improve h hz hq
  have e1 : ∀ x ∈ top q P, (Ext q P1).pri x = pri' x := fun x hx => extPri_top (P := P1) (ht1 ▸ hx)
  have e0 : ∀ x ∈ top q P, (Ext q P).pri x = P.pri x := fun x hx => extPri_top hx
  have l1 : ∀ x ∈ top q P, ∀ y ∉ top q P, (Ext q P1).pri x < (Ext q P1).pri y :=
    fun x hx y hy => extPri_lt (P := P1) (ht1 ▸ hx) (ht1 ▸ hy)
  have l0 : ∀ x ∈ top q P, ∀ y ∉ top q P, (Ext q P).pri x < (Ext q P).pri y :=
    fun x hx y hy => extPri_lt hx hy
  have b1 : ∀ x ∉ top q P, ∀ y ∉ top q P,
      ((Ext q P1).pri x < (Ext q P1).pri y ↔ (Ext q P).pri x < (Ext q P).pri y) := by
    intro x hx y hy
    show extPri q P1 x < extPri q P1 y ↔ extPri q P x < extPri q P y
    rw [extPri_bot_iff (P := P1) (ht1 ▸ hx) (ht1 ▸ hy), extPri_bot_iff hx hy]
  refine ⟨Finset.mem_univ _, (Ext q P1).inj, ?_, ?_, ?_⟩
  · intro y _ hy
    by_cases hyt : y ∈ top q P
    · rw [e0 z hz, e0 y hyt] at hy; rw [e1 z hz, e1 y hyt]
      exact h.weak y (top_subset q P hyt) hy
    · exact l1 z hz y hyt
  · obtain ⟨y, hyS, hyz, hy1, hy2⟩ := h.strict
    have hyt := top_down hz hyS hy1
    refine ⟨y, Finset.mem_univ _, hyz, ?_, ?_⟩
    · rw [e0 z hz, e0 y hyt]; exact hy1
    · rw [e1 z hz, e1 y hyt]; exact hy2
  · intro x _ y _ hxz hyz
    by_cases hxt : x ∈ top q P <;> by_cases hyt : y ∈ top q P
    · rw [e0 x hxt, e0 y hyt, e1 x hxt, e1 y hyt]
      exact h.others x (top_subset q P hxt) y (top_subset q P hyt) hxz hyz
    · exact iff_of_true (l0 x hxt y hyt) (l1 x hxt y hyt)
    · exact iff_of_false (fun h' => absurd (l0 y hyt x hxt) (not_lt.2 h'.le))
        (fun h' => absurd (l1 y hyt x hxt) (not_lt.2 h'.le))
    · exact (b1 x hxt y hyt).symm

lemma ext_improve_tau {P : Problem 𝒮} {z : 𝒮} {pri' : 𝒮 → ℕ} (h : Improvement P z pri')
    (hz : z ∈ top q P) (hq : q ≤ P.S.card) (x : 𝒮) :
    (Ext q (P.withPri pri' h.inj)).τ x = (Ext q P).τ x := by
  have ht1 := top_improve h hz hq
  show extTau q (P.withPri pri' h.inj) x = extTau q P x
  by_cases hx : x ∈ top q P
  · rw [extTau_top (P := P.withPri pri' h.inj) (ht1 ▸ hx), extTau_top hx]; rfl
  · rw [extTau_bot (P := P.withPri pri' h.inj) (ht1 ▸ hx), extTau_bot hx]

lemma rank_eq_of_cmp {P1 P2 : Problem 𝒮} (hS : P1.S = P2.S) {b : 𝒮}
    (h : ∀ y ∈ P1.S, (P1.pri y < P1.pri b ↔ P2.pri y < P2.pri b)) : rank P1 b = rank P2 b := by
  rw [rank_eq, rank_eq]; congr 1; unfold cnt; rw [← hS]; congr 1
  exact Finset.filter_congr h

variable (C : ChoiceRule 𝒮 q)

/-- comparing two problems on the same students that agree except at a top-tier student `z` -/
lemma compare_removal (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (E1 E2 : Problem 𝒮) (hS : E1.S = E2.S) (hq : q < E1.S.card) (hT : top q E1 = top q E2)
    {z b1 : 𝒮} (hz : z ∈ top q E1) (hb1 : b1 ∈ E1.S) (hrk1 : rank E1 b1 = q + 1)
    (hrk2 : rank E2 b1 = q + 1) (hτ1 : E1.τ b1 = true) (hτ2 : E2.τ b1 = true)
    (hτ : ∀ x ∈ E1.S, x ≠ z → E1.τ x = E2.τ x)
    (hpri : ∀ x ∈ E1.S, ∀ y ∈ E1.S, x ≠ z → y ≠ z → (E1.pri x < E1.pri y ↔ E2.pri x < E2.pri y)) :
    (CA C E2).card ≤ (CA C E1).card + 1 := by
  have r1 := removal C hAA hsub E1 hq hz hb1 hrk1 hτ1
  have r2 := removal C hAA hsub E2 (hS ▸ hq) (hT ▸ hz) (hS ▸ hb1) hrk2 hτ2
  have heq : (CA C (E1.restrict (E1.S.erase z) (Finset.erase_subset _ _))).card =
      (CA C (E2.restrict (E2.S.erase z) (Finset.erase_subset _ _))).card := by
    refine CA_card_eq_of_order C hAA ?_ ?_ ?_
    · show E1.S.erase z = E2.S.erase z; rw [hS]
    · intro x hx; exact hτ x (Finset.mem_of_mem_erase hx) (Finset.mem_erase.1 hx).1
    · intro x hx y hy
      exact hpri x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
        (Finset.mem_erase.1 hx).1 (Finset.mem_erase.1 hy).1
  omega

/-- the two-sided removal comparison for an improvement of a top-tier student -/
lemma ext_improve_bounds (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    {P : Problem 𝒮} {z : 𝒮} {pri' : 𝒮 → ℕ} (h : Improvement P z pri')
    (hz : z ∈ top q P) (hq : q ≤ P.S.card) :
    (CA C (Ext q (P.withPri pri' h.inj))).card ≤ (CA C (Ext q P)).card + 1 ∧
    (CA C (Ext q P)).card ≤ (CA C (Ext q (P.withPri pri' h.inj))).card + 1 := by
  set P1 := P.withPri pri' h.inj
  have ht1 : top q P1 = top q P := top_improve h hz hq
  by_cases hU : Fintype.card 𝒮 ≤ q
  · have hle : ∀ Q : Problem 𝒮, Q.S = Finset.univ → (CA C Q).card = 0 := by
      intro Q hQ
      rw [CA_empty_of_le C Q (by rw [hQ, Finset.card_univ]; exact hU)]; rfl
    rw [hle _ rfl, hle _ rfl]; omega
  rw [not_le] at hU
  obtain ⟨b1, hb1, hb1t⟩ := exists_b1 hq hU
  have hI := ext_improve h hz hq
  have hT0 : top q (Ext q P) = top q P := top_Ext hq
  have hT1 : top q (Ext q P1) = top q P := (top_Ext (P := P1) hq).trans ht1
  have hUS : q < (Ext q P).S.card := by
    show q < (Finset.univ : Finset 𝒮).card; rw [Finset.card_univ]; exact hU
  have hτb : (Ext q P).τ b1 = true := extTau_bot hb1t
  have hτb1 : (Ext q P1).τ b1 = true := (ext_improve_tau h hz hq b1).trans hτb
  have hrk1 : rank (Ext q P1) b1 = q + 1 := by
    rw [← hb1]; symm
    refine rank_eq_of_cmp (P1 := Ext q P) (P2 := Ext q P1) rfl ?_
    intro y _
    by_cases hyz : y = z
    · subst hyz
      exact iff_of_true (extPri_lt hz hb1t) (extPri_lt (P := P1) (ht1 ▸ hz) (ht1 ▸ hb1t))
    · have hbz : b1 ≠ z := fun e => hb1t (e ▸ hz)
      exact hI.others y (Finset.mem_univ _) b1 (Finset.mem_univ _) hyz hbz
  have hτall : ∀ x ∈ (Ext q P).S, x ≠ z → (Ext q P).τ x = (Ext q P1).τ x :=
    fun x _ _ => (ext_improve_tau h hz hq x).symm
  constructor
  · exact compare_removal C hAA hsub (Ext q P) (Ext q P1) rfl hUS (hT0.trans hT1.symm)
      (hT0 ▸ hz) (Finset.mem_univ _) hb1 hrk1 hτb hτb1 hτall
      (fun x hx y hy hxz hyz => hI.others x hx y hy hxz hyz)
  · exact compare_removal C hAA hsub (Ext q P1) (Ext q P) rfl hUS (hT1.trans hT0.symm)
      (hT1 ▸ hz) (Finset.mem_univ _) hrk1 hb1 hτb1 hτb
      (fun x hx hxz => (hτall x hx hxz).symm)
      (fun x hx y hy hxz hyz => (hI.others x hx y hy hxz hyz).symm)

end Improve
end ACInfra

open AffirmativeChoice.Reserve ACInfra

theorem solution {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (hMPI : MPI C) (hMTC : MTC C) :
    CondB2 q (canonicalReserve C) := by
  intro P s hs pri' h
  set P' := P.withPri pri' h.inj with hP'
  have hsT : s ∈ top q P := (mem_topMin.1 hs).1
  by_cases hlt : P.S.card < q
  · left
    rw [canon_zero_of_lt C hAA hlt, canon_zero_of_lt C hAA (P := P') hlt]
  rw [not_lt] at hlt
  rw [canon_Ext C hAA hsub (by omega) hlt, canon_Ext C hAA hsub (by omega) (P := P') hlt]
  have hb := ext_improve_bounds C hAA hsub h hsT hlt
  have hI := ext_improve h hsT hlt
  have htE : top q (Ext q P) = top q P := top_Ext hlt
  have htE' : top q (Ext q P') = top q P := (top_Ext (P := P') hlt).trans (top_improve h hsT hlt)
  have hlow : (CA C (Ext q P)).card ≤ (CA C (Ext q P')).card := by
    have hsE : (Ext q P).τ s = true := by
      show extTau q P s = true; rw [extTau_top hsT]; exact (mem_topMin.1 hs).2
    have hsC : s ∈ Cm C (Ext q P) := by
      unfold Cm; rw [Finset.mem_filter]
      exact ⟨topMin_sub C hAA _ (mem_topMin.2 ⟨htE ▸ hsT, hsE⟩), hsE⟩
    have hm := hMPI (Ext q P) s hsC _ hI
    have hsub2 : CA C (Ext q P) ⊆ CA C ((Ext q P).withPri (Ext q P').pri hI.inj) := by
      intro x hx
      rw [mem_CA] at hx
      have := hm (Finset.mem_filter.2 ⟨hx.1, hx.2.1⟩)
      unfold Cm at this; rw [Finset.mem_filter] at this
      rw [mem_CA]
      refine ⟨this.1, this.2, ?_⟩
      have htn : top q ((Ext q P).withPri (Ext q P').pri hI.inj) = top q (Ext q P') := rfl
      rw [htn, htE']; rw [htE] at hx; exact hx.2.2
    have heq : (CA C ((Ext q P).withPri (Ext q P').pri hI.inj)).card = (CA C (Ext q P')).card := by
      refine CA_card_eq_of_order C hAA ?_ ?_ ?_
      · rfl
      · intro x _; exact (ext_improve_tau h hsT hlt x).symm
      · intro _ _ _ _; exact Iff.rfl
    exact (Finset.card_le_card hsub2).trans heq.le
  have h1 : (CA C (Ext q P')).card ≤ (CA C (Ext q P)).card + 1 := hb.1
  omega
