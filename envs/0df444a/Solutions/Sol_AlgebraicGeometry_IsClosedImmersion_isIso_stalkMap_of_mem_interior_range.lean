-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.isIso_stalkMap_of_mem_interior_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e8f72f06-c2b9-5fc6-ba79-318a61cce6cc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsReduced X]
    (c : C) (hc : i c ∈ interior (Set.range i)) : IsIso (i.stalkMap c) := by
  classical
  have hsurj : Function.Surjective (i.stalkMap c) := i.stalkMap_surjective c
  suffices hinj : Function.Injective (i.stalkMap c) from
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  rw [injective_iff_map_eq_zero]
  intro g hg
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  rw [Scheme.Hom.germ_stalkMap_apply] at hg

  obtain ⟨W', hcW', ιU, ιV, hW'⟩ := TopCat.Presheaf.germ_eq C.presheaf (U := i ⁻¹ᵁ U) (V := i ⁻¹ᵁ U) c hxU hxU (i.app U s) 0
    (by rw [hg, map_zero])
  rw [map_zero] at hW'

  obtain ⟨W₀, hW₀open, hW₀⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp W'.2

  let V : X.Opens := U ⊓ ⟨W₀, hW₀open⟩ ⊓ ⟨interior (Set.range i), isOpen_interior⟩
  have hcV : i c ∈ V := ⟨⟨hxU, by show i c ∈ W₀; rw [← Set.mem_preimage, show (i ⁻¹' W₀) = (W' : Set C) from hW₀]; exact hcW'⟩, hc⟩
  have hVU : V ≤ U := inf_le_left.trans inf_le_left

  have hsV : X.presheaf.map (homOfLE hVU).op s = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro y hy
    rw [Scheme.mem_basicOpen''] at hy
    obtain ⟨hyV, hunit⟩ := hy
    exfalso

    obtain ⟨c', rfl⟩ : y ∈ Set.range i := interior_subset hyV.2
    have hc'W' : c' ∈ W' := by
      have h' : c' ∈ i ⁻¹' W₀ := hyV.1.2
      rw [hW₀] at h'
      exact h'

    have h0 : i.stalkMap c' (X.presheaf.germ U (i c') hyV.1.1 s) = 0 := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      have := TopCat.Presheaf.germ_res_apply C.presheaf ιU c' hc'W' (i.app U s)
      rw [← this, hW', map_zero]
    have hu : IsUnit (i.stalkMap c' (X.presheaf.germ U (i c') hyV.1.1 s)) := by
      rw [TopCat.Presheaf.germ_res_apply] at hunit
      exact hunit.map _
    rw [h0] at hu
    exact not_isUnit_zero hu

  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) (i c) hcV s, hsV, map_zero]

#print axioms solution

end S_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range (solution)
