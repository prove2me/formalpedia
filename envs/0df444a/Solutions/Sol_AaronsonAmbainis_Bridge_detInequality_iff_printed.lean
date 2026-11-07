-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.detInequality_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:52.410543+00:00
-- url     : https://prove2.me/submissions/e03e46fd-0266-445b-bfaa-a0c0d5121350

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_antipode_sdiff

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : DetInequality ↔ DetInequalityPrinted := by
  constructor
  · intro h ι _ _ g ℓ hℓ A hA D hD
    apply h ι g ℓ hℓ A hA D
    intro u hu G hGA hG
    exact (hD u hu).2 G (Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, hGA⟩) hG
  · intro h ι _ _ g ℓ hℓ A hA d hd
    -- the minimum exists at every point of the zone: the family is non-empty
    have key : ∀ u : Cube ι, ∃ D0 : ℝ, u ∈ zone g →
        ((∃ G : Finset ι, G ⊆ univ \ A u ∧ g (flipSet (antipode u) G) = true ∧
            D0 = ∑ j ∈ G, ℓ j) ∧
          ∀ G : Finset ι, G ⊆ univ \ A u → g (flipSet (antipode u) G) = true →
            D0 ≤ ∑ j ∈ G, ℓ j) := by
      intro u
      by_cases hu : u ∈ zone g
      · have hne : (univ.filter fun G : Finset ι =>
            G ⊆ univ \ A u ∧ g (flipSet (antipode u) G) = true).Nonempty := by
          refine ⟨univ \ A u, ?_⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, Finset.Subset.refl _, ?_⟩
          rw [flipSet_antipode_sdiff]
          exact hA u hu (A u) (Finset.Subset.refl _)
        obtain ⟨G0, hG0, hmin⟩ :=
          Finset.exists_min_image _ (fun G : Finset ι => ∑ j ∈ G, ℓ j) hne
        rw [Finset.mem_filter] at hG0
        refine ⟨∑ j ∈ G0, ℓ j, fun _ => ⟨⟨G0, hG0.2.1, hG0.2.2, rfl⟩, fun G hGA hG => ?_⟩⟩
        exact hmin G (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGA, hG⟩)
      · exact ⟨0, fun h => absurd h hu⟩
    choose D hD using key
    have h1 := h ι g ℓ hℓ A hA D hD
    refine le_trans (Finset.sum_le_sum fun u hu => ?_) h1
    obtain ⟨G, hGA, hG, hDG⟩ := (hD u hu).1
    rw [hDG]
    exact hd u hu G (Finset.subset_sdiff.mp hGA).2 hG
end AaronsonAmbainis.Bridge
