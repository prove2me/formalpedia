-- Prove2me | solution 1 for AlmostKing.Query.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:49:52.309633+00:00
-- url     : https://prove2.me/submissions/013792a3-795b-45d5-874d-48c5460578b0

import Mathlib
import Definitions.Def_AlmostKing_Query_Regularity

namespace AlmostKing.Query

/-- Out-degree of `j` inside `S`, as a sum of indicators. -/
noncomputable def degIn {V : Type*} (T : Digraph V) (S : Finset V) (j : V) : ℕ := by
  classical
  exact ∑ x ∈ S, if T.Adj j x then 1 else 0

theorem degIn_double {V : Type*} [DecidableEq V] (T : Digraph V) (hT : IsTournament T)
    (S : Finset V) :
    ∑ j ∈ S, degIn T S j + ∑ j ∈ S, degIn T S j =
      ∑ j ∈ S, ∑ x ∈ S, (if j = x then 0 else 1) := by
  classical
  unfold degIn
  have hc : (∑ j ∈ S, ∑ x ∈ S, if T.Adj j x then 1 else 0) =
      ∑ j ∈ S, ∑ x ∈ S, if T.Adj x j then 1 else 0 := Finset.sum_comm
  nth_rewrite 2 [hc]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hjx : j = x
  · subst hjx; rw [if_neg (hT.1 j), if_pos rfl]
  · rw [if_neg hjx]
    rcases (hT.2 j x hjx).1 with h | h
    · have h' : ¬ T.Adj x j := fun h' => (hT.2 j x hjx).2 ⟨h, h'⟩
      rw [if_pos h, if_neg h']
    · have h' : ¬ T.Adj j x := fun h' => (hT.2 j x hjx).2 ⟨h', h⟩
      rw [if_pos h, if_neg h']

theorem main_aux {V : Type*} [DecidableEq V] (T₁ T₂ : Digraph V) (h₁ : IsTournament T₁)
    (h₂ : IsTournament T₂) (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, u = v ∨ T₁.Adj v u ∨ T₂.Adj v u ∨
      ∃ z ∈ S, T₁.Adj v z ∧ T₂.Adj z u := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  by_contra hcon
  push Not at hcon
  have key : ∀ j ∈ S, ∃ i ∈ S, i ≠ j ∧
      (∀ u ∈ S.erase j, u = i ∨ T₁.Adj i u ∨ T₂.Adj i u ∨
        ∃ z ∈ S.erase j, T₁.Adj i z ∧ T₂.Adj z u) ∧
      ¬ (j = i ∨ T₁.Adj i j ∨ T₂.Adj i j ∨ ∃ z ∈ S, T₁.Adj i z ∧ T₂.Adj z j) := by
    intro j hj
    obtain ⟨u, huS, hu⟩ := hcon j hj
    have huj : u ≠ j := fun h => hu.1 h
    have hne : (S.erase j).Nonempty := ⟨u, Finset.mem_erase.mpr ⟨huj, huS⟩⟩
    obtain ⟨i, hiS, hgood⟩ := ih (S.erase j) (Finset.erase_ssubset hj) hne
    refine ⟨i, Finset.mem_of_mem_erase hiS, Finset.ne_of_mem_erase hiS, hgood, ?_⟩
    intro hij
    obtain ⟨w, hwS, hw⟩ := hcon i (Finset.mem_of_mem_erase hiS)
    by_cases hwj : w = j
    · subst hwj
      rcases hij with h | h | h | ⟨z, hz, hz1, hz2⟩
      · exact hw.1 h
      · exact hw.2.1 h
      · exact hw.2.2.1 h
      · exact hw.2.2.2 z hz hz1 hz2
    · rcases hgood w (Finset.mem_erase.mpr ⟨hwj, hwS⟩) with h | h | h | ⟨z, hz, hz1, hz2⟩
      · exact hw.1 h
      · exact hw.2.1 h
      · exact hw.2.2.1 h
      · exact hw.2.2.2 z (Finset.mem_of_mem_erase hz) hz1 hz2
  choose! π hπS hπne hgood hbad using key
  -- injectivity
  have hinj : Set.InjOn π S := by
    intro j hj j' hj' hjj
    by_contra hne
    apply hbad j hj
    have hmem : j ∈ S.erase j' := Finset.mem_erase.mpr ⟨hne, hj⟩
    rcases hgood j' hj' j hmem with h | h | h | ⟨z, hz, hz1, hz2⟩
    · exact Or.inl (hjj ▸ h)
    · exact Or.inr (Or.inl (hjj ▸ h))
    · exact Or.inr (Or.inr (Or.inl (hjj ▸ h)))
    · exact Or.inr (Or.inr (Or.inr ⟨z, Finset.mem_of_mem_erase hz, hjj ▸ hz1, hz2⟩))
  -- degree inequality
  have hlt : ∀ j ∈ S, degIn T₁ S (π j) < degIn T₂ S j := by
    intro j hj
    have hb := hbad j hj
    push Not at hb
    obtain ⟨hji, hn1, hn2, hnz⟩ := hb
    unfold degIn
    apply Finset.sum_lt_sum
    · intro x hx
      by_cases h1 : T₁.Adj (π j) x
      · have hxj : x ≠ j := fun h => hn1 (h ▸ h1)
        have : T₂.Adj j x := by
          rcases (h₂.2 j x (Ne.symm hxj)).1 with h | h
          · exact h
          · exact absurd h (hnz x hx h1)
        simp [h1, this]
      · simp [h1]
    · refine ⟨π j, hπS j hj, ?_⟩
      have h1 : ¬ T₁.Adj (π j) (π j) := h₁.1 _
      have h2 : T₂.Adj j (π j) := by
        rcases (h₂.2 j (π j) hji).1 with h | h
        · exact h
        · exact absurd h hn2
      simp [h1, h2]
  have hsum_lt : ∑ j ∈ S, degIn T₁ S (π j) < ∑ j ∈ S, degIn T₂ S j :=
    Finset.sum_lt_sum_of_nonempty hS hlt
  have himage : S.image π = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact hπS j hj
    · rw [Finset.card_image_of_injOn hinj]
  have hperm : ∑ j ∈ S, degIn T₁ S (π j) = ∑ j ∈ S, degIn T₁ S j := by
    rw [← Finset.sum_image (f := degIn T₁ S) hinj, himage]
  have e1 := degIn_double T₁ h₁ S
  have e2 := degIn_double T₂ h₂ S
  omega

end AlmostKing.Query

open AlmostKing.Query

/-- Lemma 14, p. 10. The first arc of the two-arc path is in T₁, the second in T₂. -/
theorem solution {V : Type*} [Fintype V] [Nonempty V]
    (T₁ T₂ : Digraph V) (h₁ : IsTournament T₁) (h₂ : IsTournament T₂) :
    ∃ v : V, ∀ u : V, u = v ∨ T₁.Adj v u ∨ T₂.Adj v u ∨
      ∃ z : V, T₁.Adj v z ∧ T₂.Adj z u := by
  classical
  obtain ⟨v, -, hv⟩ := main_aux T₁ T₂ h₁ h₂ Finset.univ Finset.univ_nonempty
  refine ⟨v, fun u => ?_⟩
  rcases hv u (Finset.mem_univ u) with h | h | h | ⟨z, -, hz⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨z, hz⟩))
