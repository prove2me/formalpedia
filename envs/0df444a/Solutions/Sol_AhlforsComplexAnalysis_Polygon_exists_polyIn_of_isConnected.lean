-- Prove2me | solution 1 for AhlforsComplexAnalysis.Polygon.exists_polyIn_of_isConnected
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:37:11.06133+00:00
-- url     : https://prove2.me/submissions/4008ad3c-c49a-44b5-a099-4538d9cd5592

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

set_option autoImplicit false

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

lemma pk_polyIn_append_aux {U : Set ℂ} (x : ℂ) (l : List ℂ) (a : ℂ) (m : List ℂ)
    (h : (x :: l).getLast? = some a) (hl : PolyIn U (x :: l)) (hm : PolyIn U (a :: m)) :
    PolyIn U ((x :: l) ++ m) := by
  induction l generalizing x with
  | nil =>
    have hx : x = a := by simpa using h
    subst hx
    simpa using hm
  | cons y l ih =>
    have h' : (y :: l).getLast? = some a := by
      simpa [List.getLast?_cons_cons] using h
    have e1 : (x :: y :: l) ++ m = x :: y :: (l ++ m) := rfl
    rw [e1, polyIn_cons_cons]
    exact ⟨hl.1, ih y h' hl.2⟩

lemma pk_polyIn_append' {U : Set ℂ} {l : List ℂ} {a : ℂ} (m : List ℂ)
    (h : l.getLast? = some a) (hl : PolyIn U l) (hm : PolyIn U (a :: m)) :
    PolyIn U (l ++ m) := by
  cases l with
  | nil => simp at h
  | cons x l => exact pk_polyIn_append_aux x l a m h hl hm

end AhlforsComplexAnalysis.Polygon

open AhlforsComplexAnalysis.Polygon

theorem solution {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {a b : ℂ} (ha : a ∈ Ω) (hb : b ∈ Ω) :
    ∃ l : List ℂ, PolyIn Ω l ∧ l.head? = some a ∧ l.getLast? = some b := by
  set S : Set ℂ := {b | b ∈ Ω ∧ ∃ l : List ℂ, PolyIn Ω l ∧ l.head? = some a ∧
    l.getLast? = some b} with hS
  have key : ∀ {B : Set ℂ}, Convex ℝ B → B ⊆ Ω → ∀ {x y : ℂ}, x ∈ B → y ∈ B → x ∈ S → y ∈ S := by
    rintro B hBc hBΩ x y hxB hyB ⟨hxΩ, l, hl, hh, hlast⟩
    refine ⟨hBΩ hyB, l ++ [y], ?_, ?_, ?_⟩
    · refine pk_polyIn_append' [y] hlast hl ?_
      rw [polyIn_cons_cons, polyIn_singleton]
      exact ⟨(hBc.segment_subset hxB hyB).trans hBΩ, hBΩ hyB⟩
    · cases l with
      | nil => simp at hh
      | cons u l => simpa using hh
    · simp
  have hSopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩo x hx.1
    exact ⟨r, hr, fun y hy => key (convex_ball x r) hball (Metric.mem_ball_self hr) hy hx⟩
  have hTopen : IsOpen (Ω \ S) := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩo x hx.1
    refine ⟨r, hr, fun y hy => ⟨hball hy, fun hyS => hx.2 ?_⟩⟩
    exact key (convex_ball x r) hball hy (Metric.mem_ball_self hr) hyS
  have haS : a ∈ S := ⟨ha, [a], by simpa [polyIn_singleton] using ha, rfl, rfl⟩
  have hsub : Ω ⊆ S := by
    refine hΩc.isPreconnected.subset_left_of_subset_union hSopen hTopen
      disjoint_sdiff_self_right ?_ ⟨a, ha, haS⟩
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  exact (hsub hb).2

#print axioms solution
