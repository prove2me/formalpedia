-- Prove2me | solution 1 for AssumptionsOfPhysics.eq_iUnion_verifiableSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:20:29.476215+00:00
-- url     : https://prove2.me/submissions/3e105a22-cdb7-4910-abd6-f41fc6d769c6

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem aop_ae4a_fin {Ω : Type*} (B : Set (Set Ω)) (A : Set Ω) (ω : Ω)
    (hB : ∀ b ∈ B, ∀ y ∈ A, (y ∈ b ↔ ω ∈ b)) {t : Set Ω} (ht : FinConjCountDisj B t) :
    ∀ y ∈ A, (y ∈ t ↔ ω ∈ t) := by
  induction ht with
  | basic h => exact hB _ h
  | univ => intro y _; simp
  | empty => intro y _; simp
  | inter _ _ ih1 ih2 => intro y hy; simp [ih1 y hy, ih2 y hy]
  | iUnion f _ ih =>
    intro y hy
    simp only [Set.mem_iUnion]
    exact exists_congr (fun n => ih n y hy)

open AssumptionsOfPhysics in
theorem aop_ae4a_neg {Ω : Type*} (S : Set (Set Ω)) (A : Set Ω) (ω : Ω)
    (hS : ∀ s ∈ S, ∀ y ∈ A, (y ∈ s ↔ ω ∈ s)) {t : Set Ω} (ht : NegFinConjCountDisj S t) :
    ∀ y ∈ A, (y ∈ t ↔ ω ∈ t) := by
  induction ht with
  | basic h => exact hS _ h
  | univ => intro y _; simp
  | compl _ ih => intro y hy; simp [Set.mem_compl_iff, ih y hy]
  | inter _ _ ih1 ih2 => intro y hy; simp [ih1 y hy, ih2 y hy]
  | iUnion f _ ih =>
    intro y hy
    simp only [Set.mem_iUnion]
    exact exists_congr (fun n => ih n y hy)

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) (s : Set Ω)
    (hs : s ∈ D.stmts) : s = ⋃ x ∈ D.verifiableSet s, x.val := by
  classical
  obtain ⟨B, hBc, hBsub, hBgen⟩ := D.exists_countable_basis
  ext ω
  constructor
  · intro hω
    obtain ⟨g, hg⟩ := (hBc.insert Set.univ).exists_eq_range (Set.insert_nonempty _ _)
    let A : Set Ω := ⋂ n, if ω ∈ g n then g n else (g n)ᶜ
    have hωA : ω ∈ A := by
      simp only [A, Set.mem_iInter]
      intro n
      split_ifs with h
      · exact h
      · exact h
    have hB : ∀ b ∈ B, ∀ y ∈ A, (y ∈ b ↔ ω ∈ b) := by
      intro b hb y hy
      have hbr : b ∈ Set.range g := hg ▸ Set.mem_insert_of_mem _ hb
      obtain ⟨n, rfl⟩ := hbr
      have := Set.mem_iInter.mp hy n
      by_cases h : ω ∈ g n
      · rw [if_pos h] at this
        exact ⟨fun _ => h, fun _ => this⟩
      · rw [if_neg h] at this
        exact ⟨fun h' => absurd h' this, fun h' => absurd h' h⟩
    have hgD : ∀ n, g n ∈ D.theoretical := by
      intro n
      have hn : g n ∈ insert Set.univ B := hg ▸ Set.mem_range_self n
      rcases hn with h | h
      · rw [h]; exact NegFinConjCountDisj.univ
      · exact NegFinConjCountDisj.basic (hBsub h)
    have hAD : A ∈ D.theoretical := by
      have hAeq : A = (⋃ n, (if ω ∈ g n then g n else (g n)ᶜ)ᶜ)ᶜ := by
        simp only [A, Set.compl_iUnion, compl_compl]
      rw [hAeq]
      refine NegFinConjCountDisj.compl (NegFinConjCountDisj.iUnion _ fun n => ?_)
      refine NegFinConjCountDisj.compl ?_
      split_ifs
      · exact hgD n
      · exact NegFinConjCountDisj.compl (hgD n)
    have hP : ∀ t ∈ D.theoretical, ∀ y ∈ A, (y ∈ t ↔ ω ∈ t) := fun t ht =>
      aop_ae4a_neg D.stmts A ω (fun s' hs' => aop_ae4a_fin B A ω hB (hBgen s' hs')) ht
    have hposs : D.IsPossibility A := by
      refine ⟨hAD, ⟨ω, hωA⟩, fun t ht => ?_⟩
      by_cases h : ω ∈ t
      · left
        intro y hy
        exact (hP t ht y hy).2 h
      · right
        rw [Set.disjoint_left]
        intro y hy hyt
        exact h ((hP t ht y hy).1 hyt)
    simp only [Set.mem_iUnion]
    exact ⟨⟨A, hposs⟩, ⟨ω, hωA, hω⟩, hωA⟩
  · intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨x, hx, hωx⟩ := h
    rcases x.isPossibility.2.2 s (NegFinConjCountDisj.basic hs) with h | h
    · exact h hωx
    · obtain ⟨y, hy1, hy2⟩ := (hx : (x.val ∩ s).Nonempty)
      exact absurd hy2 (Set.disjoint_left.mp h hy1)
