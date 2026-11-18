-- Prove2me | solution 1 for AlgebraicFPT.HittingSet.component_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:11:53.972058+00:00
-- url     : https://prove2.me/submissions/85395c21-e4cb-433b-af37-5d5f7c3510b9

import Theorems.Thm_AlgebraicFPT_HittingSet_coordinate_geometry
import Theorems.Thm_AlgebraicFPT_HittingSet_small_hitting_count
import Definitions.Def_HSElemKernel_HSInstance

set_option autoImplicit false
open AlgebraicFPT.HittingSet

lemma codim_unique {n : ℕ} {Z : Set (Fin n → ℂ)} {a b : ℕ}
    (ha : HasCodim Z a) (hb : HasCodim Z b) : a = b := by
  obtain ⟨s, hs, hsa⟩ := ha
  obtain ⟨t, ht, htb⟩ := hb
  have hst : s = t := by
    exact_mod_cast hs.symm.trans ht
  omega

theorem solution (H : HSElemKernel.HSInstance) (d : ℕ) (hd : 1 ≤ d)
    (hE : ∀ e ∈ H.S, e.card ≤ d) :
    (∀ C : Finset (Fin H.n),
      (coordinateSubspace C ∈ components (edgeVariety H.S) ↔ IsMinimalHitting H.S C)) ∧
    (∀ C : Finset (Fin H.n), HasCodim (coordinateSubspace C) C.card) ∧
    Set.BijOn coordinateSubspace {C | IsMinimalHitting H.S C} (components (edgeVariety H.S)) ∧
    Set.BijOn coordinateSubspace (smallHittingSets H.S H.k) (lowComponents (edgeVariety H.S) H.k) ∧
    (lowComponents (edgeVariety H.S) H.k).encard = (smallHittingSets H.S H.k).encard ∧
    (lowComponents (edgeVariety H.S) H.k).encard ≤ (d ^ H.k : ℕ) ∧
    (exactHittingSets H.S H.k).encard ≤ (d ^ H.k : ℕ) := by
  obtain ⟨hcomponent, hcodim, hbij⟩ := coordinate_geometry H.n H.S
  have hsmall : Set.BijOn coordinateSubspace (smallHittingSets H.S H.k)
      (lowComponents (edgeVariety H.S) H.k) := by
    refine ⟨?_, hbij.2.1.mono (fun _ hC => hC.1), ?_⟩
    · intro C hC
      exact ⟨(hcomponent C).mpr hC.1, C.card, hC.2, hcodim C⟩
    · rintro Z ⟨hZ, c, hc, hZcodim⟩
      obtain ⟨C, hC, rfl⟩ := hbij.2.2 hZ
      have heq := codim_unique (hcodim C) hZcodim
      exact ⟨C, ⟨hC, heq ▸ hc⟩, rfl⟩
  have heq := Set.encard_congr hsmall.equiv
  have hcount := small_hitting_count H.n H.S H.k d hd hE
  refine ⟨hcomponent, hcodim, hbij, hsmall, heq.symm, ?_, ?_⟩
  · rw [← heq]
    exact hcount
  · apply le_trans (Set.encard_mono ?_) hcount
    intro C hC
    exact ⟨hC.1, hC.2.le⟩
