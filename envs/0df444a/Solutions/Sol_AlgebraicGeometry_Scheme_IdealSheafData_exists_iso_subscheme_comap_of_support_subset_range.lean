-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1920e674-f9ae-5d50-8980-d246cd6e1ae7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsOpenImmersion ψ]
    (h : (I.support : Set X) ⊆ Set.range ψ) :
    ∃ e : (I.comap ψ).subscheme ≅ I.subscheme, e.hom ≫ I.subschemeι = (I.comap ψ).subschemeι ≫ ψ := by
  have hZU : ∀ z : I.subscheme, I.subschemeι z ∈ Set.range ⇑ψ := by
    intro z
    apply h
    change I.subschemeι z ∈ (I.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
  haveI : IsIso (pullback.snd ψ I.subschemeι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Scheme.Pullback.range_snd]
    exact hZU z
  refine ⟨I.comapIso ψ ≪≫ asIso (pullback.snd ψ I.subschemeι), ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

end S_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range (solution)
