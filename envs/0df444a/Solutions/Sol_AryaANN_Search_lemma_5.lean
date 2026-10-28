-- Prove2me | solution 1 for AryaANN.Search.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T11:14:30.449255+00:00
-- url     : https://prove2.me/submissions/6770e589-e0e5-4c8a-8cb7-9a4be0c620c0

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_AryaANN_Search_Setting
import Mathlib


section

namespace AryaANN.Search.BBDFresh

def RectLE {d : ℕ} (R S : Rect d) : Prop := ∀ i, S.lo i ≤ R.lo i ∧ R.hi i ≤ S.hi i

theorem rectLE_refl {d : ℕ} (R : Rect d) : RectLE R R := fun _ => ⟨le_rfl, le_rfl⟩

theorem rectLE_trans {d : ℕ} {R S U : Rect d} (h : RectLE R S) (h' : RectLE S U) :
    RectLE R U := fun i => ⟨(h' i).1.trans (h i).1, (h i).2.trans (h' i).2⟩

theorem rectLE_subset {d : ℕ} {R S : Rect d} (h : RectLE R S) : R.toSet ⊆ S.toSet := by
  intro x hx
  exact ⟨fun i => (h i).1.trans (hx.1 i), fun i => (hx.2 i).trans (h i).2⟩

theorem sticky_rectLE {d : ℕ} {R S : Rect d} (h : IsSticky R S) : RectLE R S :=
  fun i => ⟨(h i).1, (h i).2.1⟩

theorem splitLow_rectLE {d : ℕ} (c : Cell d) (i : Fin d) (t : ℝ)
    (ht : t ≤ c.outer.hi i) : RectLE (c.splitLow i t).outer c.outer := by
  intro j
  constructor
  · exact le_rfl
  · by_cases h : j=i
    · subst j; simpa [Cell.splitLow] using ht
    · simp [Cell.splitLow, Function.update_of_ne h]

theorem splitHigh_rectLE {d : ℕ} (c : Cell d) (i : Fin d) (t : ℝ)
    (ht : c.outer.lo i ≤ t) : RectLE (c.splitHigh i t).outer c.outer := by
  intro j
  constructor
  · by_cases h : j=i
    · subst j; simpa [Cell.splitHigh] using ht
    · simp [Cell.splitHigh, Function.update_of_ne h]
  · exact le_rfl

theorem valid_wf {d : ℕ} {c : Cell d} {T : BBDTree d} (h : Valid c T) : c.WF := by
  cases T with
  | leaf => exact h
  | split i t low high => exact h.1
  | shrink b inner outer => exact h.1

theorem leaf_wf {d : ℕ} {c l : Cell d} {T : BBDTree d}
    (h : Valid c T) (hl : l ∈ leaves c T) : l.WF := by
  induction T generalizing c with
  | leaf =>
    have he : l=c := by simpa [leaves] using hl
    subst l
    exact h
  | split i t low high ihl ihr =>
    simp only [leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihl h.2.2.2.2.1 hl
    · exact ihr h.2.2.2.2.2 hl
  | shrink b inner outer ihi iho =>
    simp only [leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihi h.2.1 hl
    · exact iho h.2.2 hl

theorem leaf_outer_rectLE {d : ℕ} {c l : Cell d} {T : BBDTree d}
    (h : Valid c T) (hl : l ∈ leaves c T) : RectLE l.outer c.outer := by
  induction T generalizing c with
  | leaf =>
    have he : l=c := by simpa [leaves] using hl
    subst l
    exact rectLE_refl _
  | split i t low high ihl ihr =>
    simp only [leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact rectLE_trans (ihl h.2.2.2.2.1 hl) (splitLow_rectLE c i t h.2.2.1.le)
    · exact rectLE_trans (ihr h.2.2.2.2.2 hl) (splitHigh_rectLE c i t h.2.1.le)
  | shrink b inner outer ihi iho =>
    simp only [leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · have hb : IsSticky b c.outer := ((valid_wf h.2.2).2 b (by simp)).2.1
      exact rectLE_trans (ihi h.2.1 hl) (sticky_rectLE hb)
    · exact iho (c := ⟨c.outer, some b⟩) h.2.2 hl

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh

def RectSeparated {d : ℕ} (R S : Rect d) : Prop :=
  ∃ i, R.hi i ≤ S.lo i ∨ S.hi i ≤ R.lo i

theorem rectSeparated_symm {d : ℕ} {R S : Rect d} (h : RectSeparated R S) :
    RectSeparated S R := by
  rcases h with ⟨i,h|h⟩
  · exact ⟨i,Or.inr h⟩
  · exact ⟨i,Or.inl h⟩

theorem rectSeparated_mono_left {d : ℕ} {R S U : Rect d}
    (h : RectLE R S) (hsep : RectSeparated S U) : RectSeparated R U := by
  rcases hsep with ⟨i,hi|hi⟩
  · exact ⟨i,Or.inl ((h i).2.trans hi)⟩
  · exact ⟨i,Or.inr (hi.trans (h i).1)⟩

theorem rectSeparated_mono_right {d : ℕ} {R S U : Rect d}
    (h : RectLE R S) (hsep : RectSeparated U S) : RectSeparated U R :=
  rectSeparated_symm (rectSeparated_mono_left h (rectSeparated_symm hsep))

def HoleRelation {d : ℕ} (b : Rect d) (c : Cell d) : Prop :=
  RectSeparated b c.outer ∨ ∃ b' ∈ c.inner, RectLE b b'

theorem holeRelation_mono {d : ℕ} {R S : Rect d} {c : Cell d}
    (h : RectLE R S) (hr : HoleRelation S c) : HoleRelation R c := by
  rcases hr with hs | ⟨b,hb,hle⟩
  · exact Or.inl (rectSeparated_mono_left h hs)
  · exact Or.inr ⟨b,hb,rectLE_trans h hle⟩

theorem hole_splitLow {d : ℕ} (c : Cell d) (i : Fin d) (t : ℝ) (b : Rect d)
    (hb : b ∈ c.inner) (hcut : b.hi i ≤ t ∨ t ≤ b.lo i) :
    HoleRelation b (c.splitLow i t) := by
  have hc : c.inner=some b := by simpa only [Option.mem_def] using hb
  by_cases ht : b.hi i ≤ t
  · right
    refine ⟨b,?_,rectLE_refl b⟩
    simp [Cell.splitLow,hc,ht]
  · left
    refine ⟨i,Or.inr ?_⟩
    simpa [Cell.splitLow] using hcut.resolve_left ht

theorem hole_splitHigh {d : ℕ} (c : Cell d) (i : Fin d) (t : ℝ) (b : Rect d)
    (hb : b ∈ c.inner) (hcut : b.hi i ≤ t ∨ t ≤ b.lo i) :
    HoleRelation b (c.splitHigh i t) := by
  have hc : c.inner=some b := by simpa only [Option.mem_def] using hb
  by_cases ht : t ≤ b.lo i
  · right
    refine ⟨b,?_,rectLE_refl b⟩
    simp [Cell.splitHigh,hc,ht]
  · left
    refine ⟨i,Or.inl ?_⟩
    simpa [Cell.splitHigh] using hcut.resolve_right ht

theorem leaf_hole_relation {d : ℕ} {c l : Cell d} {T : BBDTree d}
    (h : Valid c T) (hl : l ∈ leaves c T) (b : Rect d) (hb : b ∈ c.inner) :
    HoleRelation b l := by
  induction T generalizing c b with
  | leaf =>
    have he : l=c := by simpa [leaves] using hl
    subst l
    exact Or.inr ⟨b,hb,rectLE_refl b⟩
  | split i t low high ihl ihr =>
    simp only [leaves,List.mem_append] at hl
    rcases hl with hl | hl
    · rcases hole_splitLow c i t b hb (h.2.2.2.1 b hb) with hs | ⟨b',hb',hle⟩
      · exact Or.inl (rectSeparated_mono_right (leaf_outer_rectLE h.2.2.2.2.1 hl) hs)
      · exact holeRelation_mono hle (ihl h.2.2.2.2.1 hl b' hb')
    · rcases hole_splitHigh c i t b hb (h.2.2.2.1 b hb) with hs | ⟨b',hb',hle⟩
      · exact Or.inl (rectSeparated_mono_right (leaf_outer_rectLE h.2.2.2.2.2 hl) hs)
      · exact holeRelation_mono hle (ihr h.2.2.2.2.2 hl b' hb')
  | shrink B inner outer ihi iho =>
    simp only [leaves,List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihi h.2.1 hl b hb
    · have hle : RectLE b B := sticky_rectLE (((valid_wf h.2.1).2 b hb).2.1)
      exact holeRelation_mono hle (iho h.2.2 hl B (by simp))

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh

noncomputable def translateRect {d : ℕ} (B : Rect d) (i : Fin d) (t : ℝ) : Rect d :=
  ⟨fun j => B.lo j + if j=i then t else 0, fun j => B.hi j + if j=i then t else 0⟩

theorem translateRect_len {d : ℕ} (B : Rect d) (i j : Fin d) (t : ℝ) :
    (translateRect B i t).len j = B.len j := by
  unfold translateRect Rect.len
  dsimp
  ring

theorem translateRect_box {d : ℕ} (B : Rect d) (i : Fin d) (t : ℝ) (h : IsBox B) :
    IsBox (translateRect B i t) := by
  intro j
  simpa only [translateRect_len,Rect.size] using h j

theorem sticky_translate_upper {d : ℕ} (B O : Rect d) (hB : IsBox B)
    (hs : IsSticky B O) (p : Fin d → ℝ) (hp : p ∈ B.toSet) (i : Fin d)
    (hface : p i = B.hi i) (hgap : p i < O.hi i) :
    RectLE (translateRect B i (B.len i)) O ∧
    p ∈ (translateRect B i (B.len i)).toSet ∧
    RectSeparated B (translateRect B i (B.len i)) := by
  have hw := (hB i).1
  have hg : B.len i ≤ O.hi i-B.hi i := by
    rcases (hs i).2.2.2 with he | he
    · linarith
    · exact he
  have hb := sticky_rectLE hs
  refine ⟨?_,?_,?_⟩
  · intro j
    by_cases hj : j=i
    · subst j
      simp only [translateRect]
      dsimp [Rect.len] at *
      constructor <;> linarith [(hb i).1]
    · simpa [translateRect,hj] using hb j
  · constructor
    · intro j
      by_cases hj : j=i
      · subst j
        simp only [translateRect]
        dsimp [Rect.len]
        linarith
      · simpa [translateRect,hj] using hp.1 j
    · intro j
      by_cases hj : j=i
      · subst j
        simp only [translateRect]
        dsimp [Rect.len] at *
        linarith
      · simpa [translateRect,hj] using hp.2 j
  · refine ⟨i,Or.inl ?_⟩
    simp [translateRect,Rect.len]

theorem sticky_translate_lower {d : ℕ} (B O : Rect d) (hB : IsBox B)
    (hs : IsSticky B O) (p : Fin d → ℝ) (hp : p ∈ B.toSet) (i : Fin d)
    (hface : p i = B.lo i) (hgap : O.lo i < p i) :
    RectLE (translateRect B i (-(B.len i))) O ∧
    p ∈ (translateRect B i (-(B.len i))).toSet ∧
    RectSeparated B (translateRect B i (-(B.len i))) := by
  have hw := (hB i).1
  have hg : B.len i ≤ B.lo i-O.lo i := by
    rcases (hs i).2.2.1 with he | he
    · linarith
    · exact he
  have hb := sticky_rectLE hs
  refine ⟨?_,?_,?_⟩
  · intro j
    by_cases hj : j=i
    · subst j
      simp only [translateRect]
      dsimp [Rect.len] at *
      constructor <;> linarith [(hb i).2]
    · simpa [translateRect,hj] using hb j
  · constructor
    · intro j
      by_cases hj : j=i
      · subst j
        simp only [translateRect]
        dsimp [Rect.len] at *
        linarith
      · simpa [translateRect,hj] using hp.1 j
    · intro j
      by_cases hj : j=i
      · subst j
        simp only [translateRect]
        dsimp [Rect.len]
        linarith
      · simpa [translateRect,hj] using hp.2 j
  · refine ⟨i,Or.inr ?_⟩
    simp [translateRect,Rect.len]

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh
open Set

theorem preconnected_closed_crossing {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hU : IsPreconnected U) (hV : IsClosed V)
    (hin : (U ∩ V).Nonempty) (hout : (U \ V).Nonempty) :
    ∃ p ∈ U, p ∈ V ∧ p ∉ interior V := by
  by_contra h
  have hsub : U ⊆ interior V ∪ Vᶜ := by
    intro p hp
    by_cases hv : p ∈ V
    · left
      by_contra hi
      exact h ⟨p,hp,hv,hi⟩
    · exact Or.inr hv
  have hd : Disjoint (interior V) Vᶜ := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact hx' (interior_subset hx)
  rcases IsPreconnected.subset_or_subset isOpen_interior hV.isOpen_compl hd hsub hU with hi | ho
  · obtain ⟨x,hx,hx'⟩ := hout
    exact hx' (interior_subset (hi hx))
  · obtain ⟨x,hx,hx'⟩ := hin
    exact ho hx hx'

end AryaANN.Search.BBDFresh
end


section

open Set

namespace AryaANN.Search.BBDFresh

def rectInterior {d : ℕ} (R : Rect d) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun i => Ioo (R.lo i) (R.hi i))

@[simp] lemma mem_rectInterior {d : ℕ} (R : Rect d) (x : Fin d → ℝ) :
    x ∈ rectInterior R ↔ ∀ i, R.lo i < x i ∧ x i < R.hi i := by
  simp [rectInterior]

lemma rect_interior_eq {d : ℕ} (R : Rect d) : interior R.toSet = rectInterior R := by
  rw [Rect.toSet, ← pi_univ_Icc, interior_pi_set Set.finite_univ]
  simp only [interior_Icc, rectInterior]

lemma rect_isOpen_interior {d : ℕ} (R : Rect d) : IsOpen (rectInterior R) := by
  rw [← rect_interior_eq]
  exact isOpen_interior

lemma rect_isCompact {d : ℕ} (R : Rect d) : IsCompact R.toSet := isCompact_Icc

lemma rect_isClosed {d : ℕ} (R : Rect d) : IsClosed R.toSet := isClosed_Icc

lemma box_lo_lt_hi {d : ℕ} {R : Rect d} (hR : IsBox R) (i : Fin d) : R.lo i < R.hi i :=
  sub_pos.mp (hR i).1

lemma rect_closure_interior {d : ℕ} {R : Rect d} (hR : IsBox R) :
    closure (rectInterior R) = R.toSet := by
  unfold rectInterior
  rw [closure_pi_set]
  simp only [closure_Ioo (ne_of_lt (box_lo_lt_hi hR _)), pi_univ_Icc, Rect.toSet]

lemma rect_interior_nonempty {d : ℕ} {R : Rect d} (hR : IsBox R) :
    (rectInterior R).Nonempty := by
  refine ⟨fun i => (R.lo i+R.hi i)/2, ?_⟩
  rw [mem_rectInterior]
  intro i
  have h := box_lo_lt_hi hR i
  constructor <;> linarith

lemma rect_nonempty {d : ℕ} {R : Rect d} (hR : IsBox R) : R.toSet.Nonempty := by
  obtain ⟨x,hx⟩ := rect_interior_nonempty hR
  exact ⟨x, interior_subset (by rwa [rect_interior_eq])⟩

lemma rectInterior_subset {d : ℕ} (R : Rect d) : rectInterior R ⊆ R.toSet := by
  rw [← rect_interior_eq]
  exact interior_subset

lemma rectLE_interior_subset {d : ℕ} {R S : Rect d} (h : RectLE R S) :
    rectInterior R ⊆ rectInterior S := by
  intro x hx
  rw [mem_rectInterior] at hx ⊢
  exact fun i => ⟨(h i).1.trans_lt (hx i).1, (hx i).2.trans_le (h i).2⟩

lemma rect_eq_of_toSet_eq {d : ℕ} {R S : Rect d} (hR : IsBox R) (hS : IsBox S)
    (he : R.toSet = S.toSet) : R=S := by
  have hRl : R.lo ∈ R.toSet := ⟨le_rfl, fun i => (box_lo_lt_hi hR i).le⟩
  have hRh : R.hi ∈ R.toSet := ⟨fun i => (box_lo_lt_hi hR i).le, le_rfl⟩
  have hSl : S.lo ∈ S.toSet := ⟨le_rfl, fun i => (box_lo_lt_hi hS i).le⟩
  have hSh : S.hi ∈ S.toSet := ⟨fun i => (box_lo_lt_hi hS i).le, le_rfl⟩
  rw [he] at hRl hRh
  rw [← he] at hSl hSh
  have hl : R.lo=S.lo := le_antisymm hSl.1 hRl.1
  have hh : R.hi=S.hi := le_antisymm hRh.2 hSh.2
  cases R
  cases S
  cases hl
  cases hh
  rfl

lemma len_le_size {d : ℕ} (R : Rect d) (i : Fin d) : R.len i ≤ R.size :=
  le_ciSup (Set.finite_range R.len).bddAbove i

end AryaANN.Search.BBDFresh
end


section

open Set

namespace AryaANN.Search.BBDFresh

lemma open_inter_closure_nonempty {α : Type*} [TopologicalSpace α]
    {U S : Set α} (hU : IsOpen U) (h : (closure S ∩ U).Nonempty) :
    (S ∩ U).Nonempty := by
  obtain ⟨x,hx⟩ := h
  exact (show (closure (S∩U)).Nonempty from ⟨x,hU.closure_inter hx⟩).of_closure

lemma proper_box_difference_nonempty {d : ℕ} {R B : Rect d}
    (hR : IsBox R) (hB : IsBox B) (hb : RectLE B R) (hne : B≠R) :
    (R.toSet \ B.toSet).Nonempty := by
  have hn : ¬ R.toSet ⊆ B.toSet := by
    intro h
    apply hne
    exact rect_eq_of_toSet_eq hB hR (Subset.antisymm (rectLE_subset hb) h)
  obtain ⟨x,hx,hxb⟩ := Set.not_subset.mp hn
  exact ⟨x,hx,hxb⟩

lemma cell_subset_outer {d : ℕ} (c : Cell d) : c.toSet ⊆ c.outer.toSet := by
  cases hi : c.inner with
  | none => simp only [Cell.toSet,hi,Subset.rfl]
  | some b =>
    simp only [Cell.toSet,hi]
    exact closure_minimal sdiff_subset (rect_isClosed _)

lemma cell_isClosed {d : ℕ} (c : Cell d) : IsClosed c.toSet := by
  cases hi : c.inner with
  | none => simpa only [Cell.toSet,hi] using rect_isClosed c.outer
  | some b => simp only [Cell.toSet,hi]; exact isClosed_closure

lemma cell_isCompact {d : ℕ} (c : Cell d) : IsCompact c.toSet :=
  (rect_isCompact c.outer).of_isClosed_subset (cell_isClosed c) (cell_subset_outer c)

lemma cell_nonempty {d : ℕ} {c : Cell d} (hc : c.WF) : c.toSet.Nonempty := by
  cases hi : c.inner with
  | none => simpa only [Cell.toSet,hi] using rect_nonempty hc.1
  | some b =>
    have hb := hc.2 b (by simp [hi])
    simpa only [Cell.toSet,hi] using
      (proper_box_difference_nonempty hc.1 hb.1 (sticky_rectLE hb.2.1) hb.2.2).closure

lemma open_meets_rect_interior {d : ℕ} {R : Rect d} (hR : IsBox R)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (h : (R.toSet ∩ U).Nonempty) :
    (rectInterior R ∩ U).Nonempty := by
  rw [← rect_closure_interior hR] at h
  exact open_inter_closure_nonempty hU h

lemma open_meets_shell_interior {d : ℕ} {R B : Rect d} (hR : IsBox R)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (h : (closure (R.toSet \ B.toSet) ∩ U).Nonempty) :
    ∃ x, x ∈ rectInterior R ∧ x ∉ B.toSet ∧ x ∈ U := by
  obtain ⟨y,hy,hyU⟩ := open_inter_closure_nonempty hU h
  have ho : IsOpen (U ∩ B.toSetᶜ) := hU.inter (rect_isClosed B).isOpen_compl
  obtain ⟨x,hx,hxU,hxB⟩ := open_meets_rect_interior hR ho ⟨y,hy.1,hyU,hy.2⟩
  exact ⟨x,hx,hxB,hxU⟩

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh
open Set

theorem rectInterior_convex {d : ℕ} (R : Rect d) : Convex ℝ (rectInterior R) :=
  convex_pi (fun i _ => convex_Ioo (R.lo i) (R.hi i))

theorem rect_boundary_face {d : ℕ} (B : Rect d) (p : Fin d → ℝ)
    (hp : p ∈ B.toSet) (hnot : p ∉ interior B.toSet) :
    ∃ i, p i=B.lo i ∨ p i=B.hi i := by
  by_contra h
  push Not at h
  apply hnot
  rw [rect_interior_eq,mem_rectInterior]
  intro i
  constructor
  · exact lt_of_le_of_ne (hp.1 i) (Ne.symm (h i).1)
  · exact lt_of_le_of_ne (hp.2 i) (h i).2

theorem sticky_replacement_box {d : ℕ} (B O : Rect d) (hB : IsBox B)
    (hO : IsBox O) (hs : IsSticky B O) (U : Set (Fin d → ℝ))
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hinner : (B.toSet ∩ U).Nonempty)
    (hshell : (closure (O.toSet \ B.toSet) ∩ U).Nonempty) :
    ∃ R : Rect d, IsBox R ∧ (∀ i, R.len i=B.len i) ∧ RectLE R O ∧
      RectSeparated B R ∧ (R.toSet ∩ U).Nonempty := by
  obtain ⟨x,hxO,hxB,hxU⟩ := open_meets_shell_interior hO hU hshell
  obtain ⟨y,hyB,hyU⟩ := open_meets_rect_interior hB hU hinner
  have hyO := rectLE_interior_subset (sticky_rectLE hs) hyB
  have hpre : IsPreconnected (U ∩ rectInterior O) :=
    (hconv.inter (rectInterior_convex O)).isPreconnected
  obtain ⟨p,hp,hpB,hpn⟩ := preconnected_closed_crossing
    (U ∩ rectInterior O) B.toSet hpre (rect_isClosed B)
    ⟨y,⟨hyU,hyO⟩,rectInterior_subset B hyB⟩ ⟨x,⟨hxU,hxO⟩,hxB⟩
  obtain ⟨i,hface|hface⟩ := rect_boundary_face B p hpB hpn
  · have hh := sticky_translate_lower B O hB hs p hpB i hface
      ((mem_rectInterior O p).mp hp.2 i).1
    exact ⟨translateRect B i (-(B.len i)),translateRect_box B i _ hB,
      fun j => translateRect_len B i j _,hh.1,hh.2.2,⟨p,hh.2.1,hp.1⟩⟩
  · have hh := sticky_translate_upper B O hB hs p hpB i hface
      ((mem_rectInterior O p).mp hp.2 i).2
    exact ⟨translateRect B i (B.len i),translateRect_box B i _ hB,
      fun j => translateRect_len B i j _,hh.1,hh.2.2,⟨p,hh.2.1,hp.1⟩⟩

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh

def LeafRelation {d : ℕ} (c l : Cell d) : Prop :=
  RectSeparated c.outer l.outer ∨
    (∃ b ∈ l.inner, RectLE c.outer b) ∨ (∃ b ∈ c.inner, RectLE l.outer b)

theorem leafRelation_symm {d : ℕ} {c l : Cell d} (h : LeafRelation c l) :
    LeafRelation l c := by
  rcases h with h|h|h
  · exact Or.inl (rectSeparated_symm h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem leaves_pairwise_relation {d : ℕ} {c : Cell d} {T : BBDTree d}
    (h : Valid c T) : (leaves c T).Pairwise LeafRelation := by
  induction T generalizing c with
  | leaf => simp [leaves]
  | split i t low high ihl ihr =>
    rw [leaves,List.pairwise_append]
    refine ⟨ihl h.2.2.2.2.1,ihr h.2.2.2.2.2,?_⟩
    intro a ha b hb
    left
    have hs : RectSeparated (c.splitLow i t).outer (c.splitHigh i t).outer := by
      refine ⟨i,Or.inl ?_⟩
      simp [Cell.splitLow,Cell.splitHigh]
    exact rectSeparated_mono_right (leaf_outer_rectLE h.2.2.2.2.2 hb)
      (rectSeparated_mono_left (leaf_outer_rectLE h.2.2.2.2.1 ha) hs)
  | shrink B inner outer ihi iho =>
    rw [leaves,List.pairwise_append]
    refine ⟨ihi h.2.1,iho h.2.2,?_⟩
    intro a ha b hb
    have hle : RectLE a.outer B := leaf_outer_rectLE h.2.1 ha
    rcases leaf_hole_relation h.2.2 hb B (by simp) with hs | ⟨b',hb',hB⟩
    · exact Or.inl (rectSeparated_mono_left hle hs)
    · exact Or.inr (Or.inl ⟨b',hb',rectLE_trans hle hB⟩)

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh
open Set

structure ReplacementData {d : ℕ} (c : Cell d) (R : Rect d)
    (ell : ℝ) (U : Set (Fin d → ℝ)) : Prop where
  box : IsBox R
  side : ∀ i, ell ≤ R.len i
  contained : RectLE R c.outer
  meets : (R.toSet ∩ U).Nonempty
  guard : ∀ b ∈ c.inner, (∀ i, ell ≤ b.len i) → (b.toSet ∩ U).Nonempty → RectSeparated b R

theorem rectLE_len {d : ℕ} {R S : Rect d} (h : RectLE R S) (i : Fin d) :
    R.len i ≤ S.len i := by
  dsimp [Rect.len]
  linarith [(h i).1,(h i).2]

theorem replacement_exists {d : ℕ} (c : Cell d) (hc : c.WF) (ell : ℝ)
    (hside : ∀ i, ell ≤ c.outer.len i) (U : Set (Fin d → ℝ))
    (hU : IsOpen U) (hconv : Convex ℝ U) (hmeet : (c.toSet ∩ U).Nonempty) :
    ∃ R, ReplacementData c R ell U := by
  classical
  cases hi : c.inner with
  | none =>
    refine ⟨c.outer,hc.1,hside,rectLE_refl _,?_,?_⟩
    · exact hmeet.mono (fun _ hx => ⟨cell_subset_outer c hx.1,hx.2⟩)
    · intro b hb
      simp [hi] at hb
  | some b =>
    have hb := hc.2 b (by simp [hi])
    by_cases hgood : (∀ i, ell ≤ b.len i) ∧ (b.toSet ∩ U).Nonempty
    · have hsh : (closure (c.outer.toSet \ b.toSet) ∩ U).Nonempty := by
        simpa only [Cell.toSet,hi] using hmeet
      obtain ⟨R,hR,hlen,hRO,hsep,hRU⟩ := sticky_replacement_box b c.outer hb.1 hc.1 hb.2.1 U hU hconv hgood.2 hsh
      refine ⟨R,hR,?_,hRO,hRU,?_⟩
      · intro i; rw [hlen]; exact hgood.1 i
      · intro b' hb' _ _
        have he : b'=b := by
          have hh : b=b' := by simpa [hi] using hb'
          exact hh.symm
        subst b'
        exact hsep
    · refine ⟨c.outer,hc.1,hside,rectLE_refl _,?_,?_⟩
      · exact hmeet.mono (fun _ hx => ⟨cell_subset_outer c hx.1,hx.2⟩)
      · intro b' hb' hsmall hm
        have he : b'=b := by
          have hh : b=b' := by simpa [hi] using hb'
          exact hh.symm
        subst b'
        exact False.elim (hgood ⟨hsmall,hm⟩)

theorem replacements_separated {d : ℕ} {c l : Cell d} {R S : Rect d}
    {ell : ℝ} {U : Set (Fin d → ℝ)} (hc : ReplacementData c R ell U)
    (hl : ReplacementData l S ell U) (hrel : LeafRelation c l) : RectSeparated R S := by
  rcases hrel with hsep | ⟨b,hb,hcb⟩ | ⟨b,hb,hlb⟩
  · exact rectSeparated_mono_right hl.contained (rectSeparated_mono_left hc.contained hsep)
  · have hRb := rectLE_trans hc.contained hcb
    have hs : ∀ i, ell ≤ b.len i := fun i => (hc.side i).trans (rectLE_len hRb i)
    have hm : (b.toSet ∩ U).Nonempty := hc.meets.mono (fun _ hx => ⟨rectLE_subset hRb hx.1,hx.2⟩)
    exact rectSeparated_mono_left hRb (hl.guard b hb hs hm)
  · have hSb := rectLE_trans hl.contained hlb
    have hs : ∀ i, ell ≤ b.len i := fun i => (hl.side i).trans (rectLE_len hSb i)
    have hm : (b.toSet ∩ U).Nonempty := hl.meets.mono (fun _ hx => ⟨rectLE_subset hSb hx.1,hx.2⟩)
    exact rectSeparated_symm (rectSeparated_mono_left hSb (hc.guard b hb hs hm))

theorem rectSeparated_disjoint {d : ℕ} {R S : Rect d} (h : RectSeparated R S) :
    Disjoint (interior R.toSet) (interior S.toSet) := by
  rw [rect_interior_eq,rect_interior_eq]
  apply Set.disjoint_left.mpr
  intro x hx hy
  rw [mem_rectInterior] at hx hy
  rcases h with ⟨i,hi|hi⟩
  · linarith [(hx i).2,(hy i).1]
  · linarith [(hy i).2,(hx i).1]

theorem replacement_family {d N : ℕ} (c : Fin N → Cell d) (ell : ℝ)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hwf : ∀ i, (c i).WF) (hside : ∀ i j, ell ≤ (c i).outer.len j)
    (hmeet : ∀ i, ((c i).toSet ∩ U).Nonempty)
    (hrel : Pairwise (fun i j => LeafRelation (c i) (c j))) :
    ∃ R : Fin N → Rect d, (∀ i, IsBox (R i)) ∧ (∀ i j, ell ≤ (R i).len j) ∧
      (∀ i, ((R i).toSet ∩ U).Nonempty) ∧
      Pairwise (fun i j => Disjoint (interior (R i).toSet) (interior (R j).toSet)) := by
  choose R hR using fun i => replacement_exists (c i) (hwf i) ell (hside i) U hU hconv (hmeet i)
  exact ⟨R,fun i => (hR i).box,fun i => (hR i).side,fun i => (hR i).meets,
    fun i j hij => rectSeparated_disjoint (replacements_separated (hR i) (hR j) (hrel hij))⟩

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh

theorem grid_interval_point (a δ lo hi x : ℝ) (n : ℕ) (hδ : 0 < δ)
    (hwidth : δ < hi-lo) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hxa : a < x) (hxn : x < a+(n:ℝ)*δ) :
    ∃ i : Fin (n+1), lo < a+(i.val:ℝ)*δ ∧ a+(i.val:ℝ)*δ < hi := by
  by_cases h : lo < a
  · refine ⟨⟨0, by omega⟩, ?_, ?_⟩ <;> simp only [Nat.cast_zero, zero_mul, add_zero]
    · exact h
    · linarith
  have hla : 0 ≤ lo-a := by linarith
  let q := (lo-a)/δ
  have hq : 0 ≤ q := div_nonneg hla hδ.le
  have hqn : q < (n:ℝ) := by
    dsimp [q]
    apply (div_lt_iff₀ hδ).mpr
    linarith
  have hf : ⌊q⌋₊ < n := (Nat.floor_lt hq).mpr hqn
  refine ⟨⟨⌊q⌋₊+1, by omega⟩, ?_, ?_⟩
  · have ht := Nat.lt_floor_add_one q
    have hm := mul_lt_mul_of_pos_right ht hδ
    have he : q*δ=lo-a := by dsimp [q]; field_simp
    rw [he] at hm
    push_cast
    nlinarith
  · have ht := Nat.floor_le hq
    have hm := mul_le_mul_of_nonneg_right ht hδ.le
    have he : q*δ=lo-a := by dsimp [q]; field_simp
    rw [he] at hm
    push_cast
    nlinarith

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh
open Set
open scoped BigOperators

theorem finite_strict_radius {ι : Type*} [Fintype ι] (f : ι → ℝ) (R : ℝ)
    (hR : 0 < R) (hf : ∀ i, f i < R) :
    ∃ ρ, 0 < ρ ∧ ρ < R ∧ ∀ i, f i < ρ := by
  classical
  let s := insert 0 (Finset.univ.image f)
  have hs : s.Nonempty := by simp [s]
  let a := s.max' hs
  have ha0 : 0 ≤ a := s.le_max' 0 (by simp [s])
  have haR : a < R := by
    apply (Finset.max'_lt_iff _ _).mpr
    intro y hy
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hy
    rcases hy with rfl | ⟨i,rfl⟩
    · exact hR
    · exact hf i
  refine ⟨(a+R)/2,by linarith,by linarith,?_⟩
  intro i
  have hi : f i ≤ a := s.le_max' _ (by simp [s])
  linarith

theorem rectangle_grid_count {d N : ℕ} (B : Fin N → Rect d)
    (q : Fin d → ℝ) (R ell : ℝ) (hR : 0 < R) (hell : 0 < ell)
    (hside : ∀ k i, ell ≤ (B k).len i)
    (hdisj : Pairwise (fun k l => Disjoint (interior (B k).toSet) (interior (B l).toSet)))
    (x : Fin N → Fin d → ℝ) (hx : ∀ k, x k ∈ (B k).toSet)
    (hclose : ∀ k i, |x k i-q i| < R) :
    N ≤ ⌈1+2*R/ell⌉₊ ^ d := by
  classical
  obtain ⟨ρ,hρ,hρR,hρx⟩ := finite_strict_radius (fun p : Fin N × Fin d => |x p.1 p.2-q p.2|) R hR
    (fun p => hclose p.1 p.2)
  let k := ⌈1+2*R/ell⌉₊
  have hceil : 1+2*R/ell ≤ (k:ℝ) := Nat.le_ceil _
  have hk : 2 ≤ k := by
    have hpos : 0 < 2*R/ell := by positivity
    have h : (1:ℝ) < k := lt_of_lt_of_le (by linarith) hceil
    exact_mod_cast h
  let n := k-1
  have hn : n+1=k := by dsimp [n]; omega
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by dsimp [n];omega)
  have hkn : (k:ℝ)=(n:ℝ)+1 := by exact_mod_cast hn.symm
  have hRell : 2*R ≤ (n:ℝ)*ell := by
    rw [hkn] at hceil
    have hh : 2*R/ell ≤ (n:ℝ) := by linarith
    exact (div_le_iff₀ hell).mp hh
  let δ := 2*ρ/(n:ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδell : δ < ell := by
    dsimp [δ]
    apply (div_lt_iff₀ hn0).mpr
    nlinarith
  have hend : (n:ℝ)*δ=2*ρ := by dsimp [δ]; field_simp
  have hgrid (j : Fin N) (i : Fin d) :
      ∃ a : Fin (n+1), (B j).lo i < q i-ρ+(a.val:ℝ)*δ ∧
        q i-ρ+(a.val:ℝ)*δ < (B j).hi i := by
    have hxx := abs_lt.mp (hρx (j,i))
    apply grid_interval_point (q i-ρ) δ ((B j).lo i) ((B j).hi i) (x j i) n hδ
    · exact hδell.trans_le (hside j i)
    · exact (hx j).1 i
    · exact (hx j).2 i
    · linarith
    · rw [hend]; linarith
  choose g hg using hgrid
  let point (a : Fin d → Fin (n+1)) : Fin d → ℝ := fun i => q i-ρ+(a i).val*δ
  have hp (j : Fin N) : point (g j) ∈ interior (B j).toSet := by
    rw [rect_interior_eq,mem_rectInterior]
    exact hg j
  have hinj : Function.Injective g := by
    intro j l he
    by_contra hne
    have hd := Set.disjoint_left.mp (hdisj hne)
    exact hd (hp j) (by simpa only [he] using hp l)
  have hc := Fintype.card_le_of_injective g hinj
  simpa only [Fintype.card_fin,Fintype.card_fun,hn] using hc

end AryaANN.Search.BBDFresh
end


section

open scoped ENNReal
open WithLp

namespace AryaANN.Search.BBDFresh

noncomputable def lmExponent (m : ℕ∞) : ℝ≥0∞ := if m=⊤ then ⊤ else (m.toNat : ℝ≥0∞)

lemma lmExponent_ge_one {m : ℕ∞} (hm : 1 ≤ m) : 1 ≤ lmExponent m := by
  unfold lmExponent
  split_ifs with h
  · exact le_top
  · have ht := ENat.toNat_le_toNat hm h
    simp only [ENat.toNat_one] at ht
    exact_mod_cast ht

lemma lmDist_eq_lp_norm {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (x y : Fin d → ℝ) :
    lmDist m x y = ‖toLp (lmExponent m) (x-y)‖ := by
  by_cases h : m = ⊤
  · subst m
    change (⨆ i, |x i-y i|) = ‖toLp (⊤ : ℝ≥0∞) (x-y)‖
    rw [PiLp.norm_eq_ciSup]
    rfl
  · have ht := ENat.toNat_le_toNat hm h
    simp only [ENat.toNat_one] at ht
    have hp : 0 < ((m.toNat : ℝ≥0∞)).toReal := by
      simp only [ENNReal.toReal_natCast]
      exact_mod_cast (show 0 < m.toNat by omega)
    have he : lmExponent m = (m.toNat : ℝ≥0∞) := if_neg h
    rw [he, PiLp.norm_eq_sum hp]
    simp only [lmDist, if_neg h, ENNReal.toReal_natCast, Pi.sub_apply,
      Real.norm_eq_abs, Real.rpow_natCast]

lemma lmDist_nonneg {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (x y : Fin d → ℝ) :
    0 ≤ lmDist m x y := by
  let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩
  rw [lmDist_eq_lp_norm m hm]
  exact norm_nonneg _

lemma lmDist_triangle {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (x y z : Fin d → ℝ) :
    lmDist m x z ≤ lmDist m x y + lmDist m y z := by
  let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩
  simp only [lmDist_eq_lp_norm m hm]
  have he : toLp (lmExponent m) (x-z) =
      toLp (lmExponent m) (x-y) + toLp (lmExponent m) (y-z) := by
    rw [← toLp_add]
    congr 1
    abel
  rw [he]
  exact norm_add_le _ _

lemma lmDist_coord_le {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (x y : Fin d → ℝ)
    (i : Fin d) : |x i-y i| ≤ lmDist m x y := by
  let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩
  rw [lmDist_eq_lp_norm m hm]
  exact PiLp.norm_apply_le (toLp (lmExponent m) (x-y)) i

lemma continuous_lmDist_right {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (x : Fin d → ℝ) :
    Continuous (lmDist m x) := by
  let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩
  have he : lmDist m x = fun y => ‖toLp (lmExponent m) (x-y)‖ := by
    funext y
    exact lmDist_eq_lp_norm m hm x y
  rw [he]
  exact ((PiLp.continuous_toLp (lmExponent m) (fun _ : Fin d => ℝ)).comp
    (continuous_const.sub continuous_id)).norm

lemma lmDist_le_sum_abs {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (x y : Fin d → ℝ) :
    lmDist m x y ≤ ∑ i, |x i-y i| := by
  classical
  let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩
  rw [lmDist_eq_lp_norm m hm]
  have he : toLp (lmExponent m) (x-y) =
      ∑ i : Fin d, PiLp.single (lmExponent m) i (x i-y i) := by
    ext j
    simp
  rw [he]
  have hnorm := norm_sum_le Finset.univ (fun i : Fin d =>
    (PiLp.single (lmExponent m) i (x i-y i) : PiLp (lmExponent m) (fun _ : Fin d => ℝ)))
  simpa only [PiLp.norm_single, Real.norm_eq_abs] using hnorm

end AryaANN.Search.BBDFresh
end


section

open Set WithLp

namespace AryaANN.Search.BBDFresh

lemma lmDist_eq_dist {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (x y : Fin d → ℝ) :
    lmDist m x y = @dist (PiLp (lmExponent m) (fun _ : Fin d => ℝ))
      (by let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩; infer_instance)
      (toLp _ x) (toLp _ y) := by
  let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩
  rw [dist_eq_norm, ← toLp_sub]
  exact lmDist_eq_lp_norm m hm x y

lemma lmBall_isOpen {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (q : Fin d → ℝ) (r : ℝ) :
    IsOpen {x | lmDist m q x < r} :=
  isOpen_lt (continuous_lmDist_right m hm q) continuous_const

lemma lmBall_convex {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (q : Fin d → ℝ) (r : ℝ) :
    Convex ℝ {x | lmDist m q x < r} := by
  let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩
  let e := (WithLp.linearEquiv (lmExponent m) ℝ (Fin d → ℝ)).symm
  have h := (convex_ball (toLp (lmExponent m) q) r).linear_preimage e.toLinearMap
  convert! h using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, Metric.mem_ball]
  rw [lmDist_eq_dist m hm, dist_comm]
  rfl

lemma lmDist_self {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (x : Fin d → ℝ) :
    lmDist m x x = 0 := by
  let : Fact (1 ≤ lmExponent m) := ⟨lmExponent_ge_one hm⟩
  rw [lmDist_eq_dist m hm]
  exact dist_self _

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh
open Set

noncomputable def prefixCell {d N : ℕ} (E : List (Cell d × (Fin d → ℝ)))
    (hN : N ≤ E.length) (i : Fin N) : Cell d := (E[i.val]'(lt_of_lt_of_le i.isLt hN)).1

theorem prefix_leaf_relation {d N : ℕ} (c : Cell d) (T : BBDTree d)
    (hT : Valid c T) (E : List (Cell d × (Fin d → ℝ)))
    (hperm : (E.map Prod.fst).Perm (leaves c T)) (hN : N ≤ E.length) :
    Pairwise (fun i j : Fin N => LeafRelation (prefixCell E hN i) (prefixCell E hN j)) := by
  have hpw : (E.map Prod.fst).Pairwise LeafRelation :=
    (hperm.pairwise_iff (fun {_ _} => leafRelation_symm)).mpr (leaves_pairwise_relation hT)
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := (List.pairwise_iff_getElem.mp hpw) i.val j.val
      (by simpa using lt_of_lt_of_le i.isLt hN) (by simpa using lt_of_lt_of_le j.isLt hN) hlt
    simpa only [List.getElem_map,prefixCell] using h
  · apply leafRelation_symm
    have h := (List.pairwise_iff_getElem.mp hpw) j.val i.val
      (by simpa using lt_of_lt_of_le j.isLt hN) (by simpa using lt_of_lt_of_le i.isLt hN) hgt
    simpa only [List.getElem_map,prefixCell] using h

theorem prefix_leaf_wf {d N : ℕ} (c : Cell d) (T : BBDTree d)
    (hT : Valid c T) (E : List (Cell d × (Fin d → ℝ)))
    (hperm : (E.map Prod.fst).Perm (leaves c T)) (hN : N ≤ E.length) (i : Fin N) :
    (prefixCell E hN i).WF := by
  apply leaf_wf hT
  apply hperm.mem_iff.mp
  exact List.mem_map.mpr ⟨E[i.val]'(lt_of_lt_of_le i.isLt hN),List.getElem_mem _,rfl⟩

theorem native_prefix_packing {d N : ℕ} (m : ℕ∞) (hm : 1 ≤ m)
    (c : Cell d) (T : BBDTree d) (hT : Valid c T)
    (E : List (Cell d × (Fin d → ℝ))) (hperm : (E.map Prod.fst).Perm (leaves c T))
    (hN : N ≤ E.length) (q : Fin d → ℝ) (R ell : ℝ) (hR : 0 < R) (hell : 0 < ell)
    (hside : ∀ i j, ell ≤ (prefixCell E hN i).outer.len j)
    (hmeet : ∀ i, ((prefixCell E hN i).toSet ∩ {x | lmDist m q x < R}).Nonempty) :
    N ≤ ⌈1+2*R/ell⌉₊ ^ d := by
  obtain ⟨B,_,hBside,hBmeet,hdisj⟩ := replacement_family (prefixCell E hN) ell
    {x | lmDist m q x < R} (lmBall_isOpen m hm q R) (lmBall_convex m hm q R)
    (prefix_leaf_wf c T hT E hperm hN) hside hmeet (prefix_leaf_relation c T hT E hperm hN)
  choose x hx using hBmeet
  apply rectangle_grid_count B q R ell hR hell hBside hdisj x (fun i => (hx i).1)
  intro i j
  have hh := (lmDist_coord_le m hm q (x i) j).trans_lt (hx i).2
  simpa only [abs_sub_comm] using hh

end AryaANN.Search.BBDFresh
end


section

open Set
open scoped BigOperators

namespace AryaANN.Search.BBDFresh

lemma rect_coord_abs_le {d : ℕ} {R : Rect d} {x y : Fin d → ℝ}
    (hx : x ∈ R.toSet) (hy : y ∈ R.toSet) (i : Fin d) :
    |x i-y i| ≤ R.len i := by
  rw [abs_le]
  have hxlo := hx.1 i
  have hxhi := hx.2 i
  have hylo := hy.1 i
  have hyhi := hy.2 i
  dsimp [Rect.len]
  constructor <;> linarith

lemma rect_dist_le_sum_len {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) {R : Rect d}
    {x y : Fin d → ℝ} (hx : x ∈ R.toSet) (hy : y ∈ R.toSet) :
    lmDist m x y ≤ ∑ i, R.len i :=
  (lmDist_le_sum_abs m hm x y).trans
    (Finset.sum_le_sum (fun i _ => rect_coord_abs_le hx hy i))

lemma sum_len_le_side_scale {d : ℕ} {R : Rect d} (hR : IsBox R) (i : Fin d) :
    ∑ j, R.len j ≤ (3*(d:ℝ)-2)*R.len i := by
  classical
  calc
    _ ≤ ∑ j : Fin d, (3*R.len i - if j=i then 2*R.len i else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j=i
      · subst j
        simp only [if_true]
        linarith
      · simp only [if_neg hj, sub_zero]
        exact (len_le_size R j).trans (hR i).2
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp
      ring

end AryaANN.Search.BBDFresh
end


section

open Set

namespace AryaANN.Search.BBDFresh

lemma cellDist_attained {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (q : Fin d → ℝ)
    {c : Cell d} (hc : c.WF) : ∃ x ∈ c.toSet, lmDist m q x = cellDist m q c := by
  obtain ⟨x,hx,hmin⟩ := (cell_isCompact c).exists_isMinOn (cell_nonempty hc)
    (continuous_lmDist_right m hm q).continuousOn
  refine ⟨x,hx,le_antisymm ?_ ?_⟩
  · apply le_csInf ((cell_nonempty hc).image (lmDist m q))
    rintro _ ⟨y,hy,rfl⟩
    exact hmin hy
  · apply csInf_le
    · exact ⟨0,by rintro _ ⟨y,hy,rfl⟩; exact lmDist_nonneg m hm q y⟩
    · exact mem_image_of_mem _ hx

lemma cellDist_nonneg {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (q : Fin d → ℝ)
    {c : Cell d} (hc : c.WF) : 0 ≤ cellDist m q c := by
  obtain ⟨x,hx,he⟩ := cellDist_attained m hm q hc
  rw [← he]
  exact lmDist_nonneg m hm q x

lemma cell_meets_lmBall_of_dist_lt {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m)
    (q : Fin d → ℝ) {c : Cell d} (hc : c.WF) {r : ℝ} (hr : cellDist m q c < r) :
    (c.toSet ∩ {x | lmDist m q x < r}).Nonempty := by
  obtain ⟨x,hx,he⟩ := cellDist_attained m hm q hc
  exact ⟨x,hx,by simpa only [mem_ofPred_eq,he] using hr⟩

end AryaANN.Search.BBDFresh
end


section

open Set

namespace AryaANN.Search.BBDFresh

lemma enumerated_cell_wf {d : ℕ} {C : Rect d} {T : BBDTree d}
    (hT : Valid ⟨C,none⟩ T) {E : List (Cell d × (Fin d → ℝ))}
    (hp : (E.map Prod.fst).Perm (leaves ⟨C,none⟩ T)) (j : ℕ) (hj : j < E.length) :
    (E[j]).1.WF := by
  apply leaf_wf hT
  apply hp.mem_iff.mp
  exact List.mem_map.mpr ⟨E[j],List.getElem_mem hj,rfl⟩

lemma visited_distance_le_last {d : ℕ} (m : ℕ∞) (q : Fin d → ℝ)
    {E : List (Cell d × (Fin d → ℝ))}
    (hs : E.Pairwise (fun a b => cellDist m q a.1  ≤  cellDist m q b.1))
    {N : ℕ} (hN : N ≤ E.length) {j : ℕ} (hj : j < N) :
    cellDist m q (E[j]'(by omega)).1  ≤ 
      cellDist m q (E[N-1]'(by omega)).1 := by
  rcases eq_or_lt_of_le (show j ≤ N-1 by omega) with he | he
  · subst j
    exact le_rfl
  · exact hs.rel_get_of_lt (a := ⟨j,by omega⟩) (b := ⟨N-1,by omega⟩) he

lemma visited_minimum_side {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m)
    {C : Rect d} {T : BBDTree d} (hT : Valid ⟨C,none⟩ T)
    (ε : ℝ) (hε : 0 < ε) (q : Fin d → ℝ)
    {E : List (Cell d × (Fin d → ℝ))}
    (hp : (E.map Prod.fst).Perm (leaves ⟨C,none⟩ T))
    (hpt : ∀ e ∈ E,e.2 ∈ e.1.outer.toSet)
    (hs : E.Pairwise (fun a b => cellDist m q a.1  ≤  cellDist m q b.1))
    {N : ℕ} (hN : IsVisitCount m ε q E N) {j : ℕ} (hj : j < N) (i : Fin d) :
    cellDist m q (E[N-1]'(by have := hN.1; omega)).1 * ε / (3*(d:ℝ)-2)  ≤ 
      (E[j]'(by have := hN.1; omega)).1.outer.len i := by
  have hjE : j < E.length := lt_of_lt_of_le hj hN.1
  have hnE : N-1 < E.length := by have := hN.1; omega
  let r := cellDist m q (E[N-1]'hnE).1
  have hnstop := hN.2.1 (N-1) (by omega)
  have hdiv : r  ≤  lmDist m q (E[j]'hjE).2 / (1+ε) := by
    apply le_of_not_gt
    intro h
    apply hnstop
    exact ⟨hnE,j,hjE,by omega,h⟩
  have hpoint : r*(1+ε)  ≤  lmDist m q (E[j]'hjE).2 :=
    (le_div_iff₀ (by linarith : 0 < 1+ε)).mp hdiv
  have hw := enumerated_cell_wf hT hp j hjE
  obtain ⟨x,hx,he⟩ := cellDist_attained m hm q hw
  have hdist := visited_distance_le_last m q hs hN.1 hj
  have hrect := rect_dist_le_sum_len m hm (cell_subset_outer _ hx)
    (hpt _ (List.getElem_mem hjE))
  have htriangle := lmDist_triangle m hm q x (E[j]'hjE).2
  have hsum := sum_len_le_side_scale hw.1 i
  have hd : 0  <  3*(d:ℝ)-2 := by
    have hd' : (1:ℝ)  ≤  d := by exact_mod_cast (show 1 ≤ d by have := i.isLt; omega)
    linarith
  apply (div_le_iff₀ hd).mpr
  change r*ε  ≤  _
  dsimp [r] at hpoint ⊢
  rw [he] at htriangle
  nlinarith

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh

lemma finite_positive_lower {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ a : ℝ, 0 < a ∧ ∀ i, a ≤ f i := by
  classical
  have h : ∀ s : Finset ι, ∃ a : ℝ, 0 < a ∧ ∀ i ∈ s, a ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a,ha,hs⟩ := ih
      refine ⟨min a (f i),lt_min ha (hf i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs j hj)
  obtain ⟨a,ha,hall⟩ := h Finset.univ
  exact ⟨a,ha,fun i => hall i (Finset.mem_univ _)⟩

lemma positive_search_radii {d : ℕ} (hd : 0 < d) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    let ell := r*ε/(3*(d:ℝ)-2)
    let R := r*(3*(d:ℝ)-1)/(3*(d:ℝ)-2)
    0 < ell ∧ r < R ∧ 1+2*R/ell ≤ 1+6*(d:ℝ)/ε := by
  dsimp
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 < 3*(d:ℝ)-2 := by linarith
  have he : 0 < r*ε/(3*(d:ℝ)-2) := div_pos (mul_pos hr hε) hc
  refine ⟨he,?_,?_⟩
  · apply (lt_div_iff₀ hc).mpr
    nlinarith
  · have hratio : 2*(r*(3*(d:ℝ)-1)/(3*(d:ℝ)-2))/(r*ε/(3*(d:ℝ)-2)) =
        (6*(d:ℝ)-2)/ε := by
      field_simp
      ring
    rw [hratio]
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (by linarith) hε.le

lemma search_ceiling_ge_two {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    2 ≤ ⌈1+6*(d:ℝ)/ε⌉₊ := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hh : (1:ℝ) < 1+6*(d:ℝ)/ε := by
    have : 0 < 6*(d:ℝ)/ε := by positivity
    linarith
  have hh' : (1:ℕ) < ⌈1+6*(d:ℝ)/ε⌉₊ := Nat.lt_ceil.mpr (by simpa using hh)
  omega

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search.BBDFresh

lemma native_search_bound {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (C : Rect d) (T : BBDTree d)
    (hT : Valid ⟨C,none⟩ T) (ε : ℝ) (hε : 0 < ε) (q : Fin d → ℝ)
    (E : List (Cell d × (Fin d → ℝ)))
    (hperm : (E.map Prod.fst).Perm (leaves ⟨C,none⟩ T))
    (hpt : ∀ e ∈ E, e.2 ∈ e.1.outer.toSet)
    (hsorted : E.Pairwise (fun a b => cellDist m q a.1 ≤ cellDist m q b.1))
    (N : ℕ) (hN : IsVisitCount m ε q E N) :
    N ≤ ⌈1+6*(d:ℝ)/ε⌉₊ ^ d := by
  classical
  by_cases hn : N = 0
  · subst N
    exact Nat.zero_le _
  have hnpos : 0 < N := Nat.pos_of_ne_zero hn
  by_cases hd : d = 0
  · subst d
    have hh := native_prefix_packing m hm ⟨C,none⟩ T hT E hperm hN.1 q 1 1
      (by norm_num) (by norm_num) (fun _ j => Fin.elim0 j) (by
        intro i
        obtain ⟨x,hx⟩ := cell_nonempty (prefix_leaf_wf ⟨C,none⟩ T hT E hperm hN.1 i)
        refine ⟨x,hx,?_⟩
        have he : x = q := Subsingleton.elim _ _
        change lmDist m q x < 1
        rw [he,lmDist_self m hm]
        norm_num)
    simpa using hh
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hlast : N-1 < E.length := by have := hN.1; omega
  let r := cellDist m q (E[N-1]'hlast).1
  have hr : 0 ≤ r := cellDist_nonneg m hm q (enumerated_cell_wf hT hperm (N-1) hlast)
  have hdist : ∀ i : Fin N, cellDist m q (prefixCell E hN.1 i) ≤ r := by
    intro i
    exact visited_distance_le_last m q hsorted hN.1 i.isLt
  by_cases hrzero : r = 0
  · obtain ⟨ell,hell,hside⟩ := finite_positive_lower
      (fun p : Fin N × Fin d => (prefixCell E hN.1 p.1).outer.len p.2)
      (fun p => (prefix_leaf_wf ⟨C,none⟩ T hT E hperm hN.1 p.1).1 p.2 |>.1)
    have hh := native_prefix_packing m hm ⟨C,none⟩ T hT E hperm hN.1 q (ell/4) ell
      (by positivity) hell (fun i j => hside (i,j)) (by
        intro i
        apply cell_meets_lmBall_of_dist_lt m hm q
          (prefix_leaf_wf ⟨C,none⟩ T hT E hperm hN.1 i)
        have hi := hdist i
        rw [hrzero] at hi
        exact hi.trans_lt (by positivity))
    have he : 1+2*(ell/4)/ell = (3/2:ℝ) := by field_simp; ring
    rw [he] at hh
    norm_num at hh
    exact hh.trans (Nat.pow_le_pow_left (search_ceiling_ge_two hdpos hε) d)
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
    let ell := r*ε/(3*(d:ℝ)-2)
    let R := r*(3*(d:ℝ)-1)/(3*(d:ℝ)-2)
    obtain ⟨hell,hrR,hconstant⟩ := positive_search_radii hdpos hrpos hε
    have hh := native_prefix_packing m hm ⟨C,none⟩ T hT E hperm hN.1 q R ell
      (hrpos.trans hrR) hell (by
        intro i j
        exact visited_minimum_side m hm hT ε hε q hperm hpt hsorted hN i.isLt j) (by
        intro i
        exact cell_meets_lmBall_of_dist_lt m hm q
          (prefix_leaf_wf ⟨C,none⟩ T hT E hperm hN.1 i) ((hdist i).trans_lt hrR))
    exact hh.trans (Nat.pow_le_pow_left (Nat.ceil_mono hconstant) d)

end AryaANN.Search.BBDFresh
end


section

namespace AryaANN.Search

/-- Lemma 5 (p. 911): the number `N` of leaf cells the search visits up until termination is at
most `⌈1 + 6d/ε⌉^d`. As in the proof (p. 912), `N` counts the cells that did not cause termination;
the cell whose test fires is not counted (counting it, the printed bound can be exceeded by one). -/
theorem lemma_5 {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (C : Rect d) (T : BBDTree d)
    (hT : Valid ⟨C, none⟩ T) (ε : ℝ) (hε : 0 < ε) (q : Fin d → ℝ)
    (E : List (Cell d × (Fin d → ℝ)))
    (hperm : (E.map Prod.fst).Perm (leaves ⟨C, none⟩ T))
    (hpt : ∀ e ∈ E, e.2 ∈ e.1.outer.toSet)
    (hsorted : E.Pairwise (fun a b => cellDist m q a.1 ≤ cellDist m q b.1))
    (N : ℕ) (hN : IsVisitCount m ε q E N) :
    N ≤ ⌈1 + 6 * (d : ℝ) / ε⌉₊ ^ d := by
  exact BBDFresh.native_search_bound m hm C T hT ε hε q E hperm hpt hsorted N hN

end AryaANN.Search
end


theorem solution {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (C : AryaANN.Search.Rect d) (T : AryaANN.Search.BBDTree d)
    (hT : AryaANN.Search.Valid ⟨C, none⟩ T) (ε : ℝ) (hε : 0 < ε) (q : Fin d → ℝ)
    (E : List (AryaANN.Search.Cell d × (Fin d → ℝ)))
    (hperm : (E.map Prod.fst).Perm (AryaANN.Search.leaves ⟨C, none⟩ T))
    (hpt : ∀ e ∈ E, e.2 ∈ e.1.outer.toSet)
    (hsorted : E.Pairwise (fun a b => AryaANN.Search.cellDist m q a.1 ≤ AryaANN.Search.cellDist m q b.1))
    (N : ℕ) (hN : AryaANN.Search.IsVisitCount m ε q E N) :
    N ≤ ⌈1 + 6 * (d : ℝ) / ε⌉₊ ^ d := by
  exact AryaANN.Search.lemma_5 m hm C T hT ε hε q E hperm hpt hsorted N hN
