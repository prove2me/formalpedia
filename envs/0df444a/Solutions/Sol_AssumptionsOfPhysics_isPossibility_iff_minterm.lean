-- Prove2me | solution 1 for AssumptionsOfPhysics.isPossibility_iff_minterm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:03:48.269477+00:00
-- url     : https://prove2.me/submissions/dff391d5-32df-4841-a413-b9905f4e3d1b

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace AoP9ef

open AssumptionsOfPhysics

universe u

variable {Ω : Type u}

lemma negOfFin {B : Set (Set Ω)} {s : Set Ω} (h : FinConjCountDisj B s) :
    NegFinConjCountDisj B s := by
  induction h with
  | basic hb => exact .basic hb
  | univ => exact .univ
  | empty => simpa using (NegFinConjCountDisj.compl (NegFinConjCountDisj.univ (B := B)))
  | inter _ _ ih₁ ih₂ => exact .inter ih₁ ih₂
  | iUnion f _ ih => exact .iUnion f ih

lemma negTrans {B C : Set (Set Ω)} (hBC : ∀ s ∈ B, NegFinConjCountDisj C s) {s : Set Ω}
    (h : NegFinConjCountDisj B s) : NegFinConjCountDisj C s := by
  induction h with
  | basic hb => exact hBC _ hb
  | univ => exact .univ
  | compl _ ih => exact .compl ih
  | inter _ _ ih₁ ih₂ => exact .inter ih₁ ih₂
  | iUnion f _ ih => exact .iUnion f ih

lemma dich {B : Set (Set Ω)} (σ : B → Bool) {s : Set Ω} (h : NegFinConjCountDisj B s) :
    minterm B σ ⊆ s ∨ minterm B σ ⊆ sᶜ := by
  induction h with
  | basic hb =>
    rename_i b
    have hsub : minterm B σ ⊆ (if σ ⟨b, hb⟩ then b else bᶜ) :=
      Set.iInter_subset (fun c : B => if σ c then (c : Set Ω) else (c : Set Ω)ᶜ) ⟨b, hb⟩
    cases hσ : σ ⟨b, hb⟩
    · right; simpa [hσ] using hsub
    · left; simpa [hσ] using hsub
  | univ => left; exact Set.subset_univ _
  | compl _ ih =>
    rcases ih with h1 | h1
    · right; simpa using h1
    · left; exact h1
  | inter _ _ ih₁ ih₂ =>
    rcases ih₁ with h1 | h1
    · rcases ih₂ with h2 | h2
      · left; exact Set.subset_inter h1 h2
      · right; exact h2.trans (Set.compl_subset_compl.mpr Set.inter_subset_right)
    · right; exact h1.trans (Set.compl_subset_compl.mpr Set.inter_subset_left)
  | iUnion f _ ih =>
    by_cases hex : ∃ n, minterm B σ ⊆ f n
    · obtain ⟨n, hn⟩ := hex
      left; exact hn.trans (Set.subset_iUnion f n)
    · right
      rw [Set.compl_iUnion]
      refine Set.subset_iInter (fun n => ?_)
      rcases ih n with h1 | h1
      · exact absurd ⟨n, h1⟩ hex
      · exact h1

/-- With a point `p` of the minterm, the minterm is inside `s` iff `p ∈ s`. -/
lemma sub_iff {B : Set (Set Ω)} (σ : B → Bool) {p : Ω} (hp : p ∈ minterm B σ) {s : Set Ω}
    (h : NegFinConjCountDisj B s) : minterm B σ ⊆ s ↔ p ∈ s := by
  constructor
  · intro hs; exact hs hp
  · intro hps
    rcases dich σ h with h1 | h1
    · exact h1
    · exact absurd hps (h1 hp)

lemma negFin_iUnion {C : Set (Set Ω)} {ι : Type u} [Countable ι] (f : ι → Set Ω)
    (h : ∀ i, NegFinConjCountDisj C (f i)) : NegFinConjCountDisj C (⋃ i, f i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Set.iUnion_of_empty]
    simpa using (NegFinConjCountDisj.compl (NegFinConjCountDisj.univ (B := C)))
  · obtain ⟨g, hg⟩ := exists_surjective_nat ι
    rw [← hg.iUnion_comp]
    exact .iUnion _ (fun n => h (g n))

lemma minterm_negFin {C B : Set (Set Ω)} (hB : B.Countable)
    (hBC : ∀ b ∈ B, NegFinConjCountDisj C b) (τ : B → Bool) :
    NegFinConjCountDisj C (minterm B τ) := by
  haveI : Countable B := hB.to_subtype
  have key : NegFinConjCountDisj C
      (⋃ b : B, (if τ b then (b : Set Ω) else (b : Set Ω)ᶜ)ᶜ)ᶜ := by
    refine .compl (negFin_iUnion _ (fun b => .compl ?_))
    cases τ b
    · simpa using NegFinConjCountDisj.compl (hBC _ b.2)
    · simpa using hBC _ b.2
  rw [Set.compl_iUnion] at key
  simpa [minterm] using key

theorem main (D : ExperimentalDomain Ω)
    (B : Set (Set Ω)) (hB : IsBasis D.stmts B) (x : Set Ω) :
    D.IsPossibility x ↔ x.Nonempty ∧ ∃ σ : B → Bool, x = minterm B σ := by
  classical
  -- theoretical statements are exactly those generated (with negation) from `B`
  have hDB : ∀ {s : Set Ω}, NegFinConjCountDisj D.stmts s → NegFinConjCountDisj B s :=
    fun h => negTrans (fun s hs => negOfFin (hB.2 s hs)) h
  have hBD : ∀ {s : Set Ω}, NegFinConjCountDisj B s → NegFinConjCountDisj D.stmts s :=
    fun h => negTrans (fun s hs => .basic (hB.1 hs)) h
  constructor
  · rintro ⟨hxT, hxne, hx⟩
    refine ⟨hxne, fun b => decide (x ⊆ (b : Set Ω)), ?_⟩
    have hxm : x ⊆ minterm B (fun b => decide (x ⊆ (b : Set Ω))) := by
      refine Set.subset_iInter (fun b => ?_)
      by_cases hxb : x ⊆ (b : Set Ω)
      · simpa [hxb] using hxb
      · simp only [hxb, decide_false]
        rcases hx b (.basic (hB.1 b.2)) with h1 | h1
        · exact absurd h1 hxb
        · simpa using Set.subset_compl_iff_disjoint_right.mpr h1
    obtain ⟨p, hp⟩ := hxne
    have hpm := hxm hp
    have : minterm B (fun b => decide (x ⊆ (b : Set Ω))) ⊆ x :=
      (sub_iff _ hpm (hDB hxT)).mpr hp
    exact Set.Subset.antisymm hxm this
  · rintro ⟨hxne, σ, rfl⟩
    obtain ⟨p, hp⟩ := hxne
    obtain ⟨B0, hB0c, hB0⟩ := D.exists_countable_basis
    let τ : B0 → Bool := fun b => decide (p ∈ (b : Set Ω))
    have hpA : p ∈ minterm B0 τ := by
      refine Set.mem_iInter.mpr (fun b => ?_)
      by_cases hpb : p ∈ (b : Set Ω)
      · simp [τ, hpb]
      · simp [τ, hpb]
    -- every element of `D` is generated from `B0`
    have hDB0 : ∀ {s : Set Ω}, NegFinConjCountDisj D.stmts s → NegFinConjCountDisj B0 s :=
      fun h => negTrans (fun s hs => negOfFin (hB0.2 s hs)) h
    have hEq : minterm B σ = minterm B0 τ := by
      apply Set.Subset.antisymm
      · refine Set.subset_iInter (fun b => ?_)
        have hb : NegFinConjCountDisj B (b : Set Ω) := hDB (.basic (hB0.1 b.2))
        by_cases hpb : p ∈ (b : Set Ω)
        · simpa [τ, hpb] using (sub_iff σ hp hb).mpr hpb
        · simp only [τ, hpb, decide_false]
          rcases dich σ hb with h1 | h1
          · exact absurd (h1 hp) hpb
          · simpa using h1
      · refine Set.subset_iInter (fun b => ?_)
        have hb : NegFinConjCountDisj B0 (b : Set Ω) := hDB0 (.basic (hB.1 b.2))
        have hpb : p ∈ (if σ b then (b : Set Ω) else (b : Set Ω)ᶜ) :=
          Set.mem_iInter.mp hp b
        cases hσ : σ b
        · simp only [hσ] at hpb ⊢
          rcases dich τ hb with h1 | h1
          · exact absurd (h1 hpA) (by simpa using hpb)
          · simpa using h1
        · simp only [hσ] at hpb ⊢
          exact (sub_iff τ hpA hb).mpr (by simpa using hpb)
    have hT : NegFinConjCountDisj D.stmts (minterm B σ) := by
      rw [hEq]
      exact minterm_negFin hB0c (fun b hb => .basic (hB0.1 hb)) τ
    refine ⟨hT, ⟨p, hp⟩, fun s hs => ?_⟩
    rcases dich σ (hDB hs) with h1 | h1
    · left; exact h1
    · right; exact Set.subset_compl_iff_disjoint_right.mp h1

end AoP9ef

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω)
    (B : Set (Set Ω)) (hB : IsBasis D.stmts B) (x : Set Ω) :
    D.IsPossibility x ↔ x.Nonempty ∧ ∃ σ : B → Bool, x = minterm B σ := by
  exact AoP9ef.main D B hB x
