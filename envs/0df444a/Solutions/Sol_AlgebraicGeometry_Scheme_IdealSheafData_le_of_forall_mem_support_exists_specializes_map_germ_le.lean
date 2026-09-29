-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.le_of_forall_mem_support_exists_specializes_map_germ_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/70ac0776-ce1b-5807-b053-771ae6c88fd2

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_le_of_forall_mem_support_exists_specializes_map_germ_le

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem solution
    {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ x : X, x ∈ (J.support : Set X) →
      ∃ (y : X) (_ : x ⤳ y) (U : X.affineOpens) (hy : y ∈ (U : X.Opens)),
        Ideal.map (X.presheaf.germ (U : X.Opens) y hy).hom (I.ideal U) ≤
          Ideal.map (X.presheaf.germ (U : X.Opens) y hy).hom (J.ideal U)) :
    I ≤ J := by
  classical
  obtain ⟨hind, -, hsupp⟩ :=
    @AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy X
  rw [Scheme.IdealSheafData.le_def]
  intro U s hs
  rw [U.2.mem_ideal_iff]
  intro x hxU
  by_cases hxJ : x ∈ (J.support : Set X)
  · obtain ⟨y, hxy, V, hyV, hle⟩ := h x hxJ
    have hxV : x ∈ (V : X.Opens) := hxy.mem_open V.1.isOpen hyV

    have hsI : (X.presheaf.germ (U : X.Opens) x hxU).hom s ∈
        Ideal.map (X.presheaf.germ (V : X.Opens) x hxV).hom (I.ideal V) := by
      rw [← hind I x U V hxU hxV]
      exact Ideal.mem_map_of_mem _ hs
    rw [hind J x U V hxU hxV]

    have hgerm : (X.presheaf.germ (V : X.Opens) x hxV).hom =
        (X.presheaf.stalkSpecializes hxy).hom.comp (X.presheaf.germ (V : X.Opens) y hyV).hom := by
      rw [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
    rw [hgerm, ← Ideal.map_map] at hsI ⊢
    exact Ideal.map_mono hle hsI
  · rw [(hsupp J U x hxU).1 hxJ]
    exact Submodule.mem_top

end S_AlgebraicGeometry_Scheme_IdealSheafData_le_of_forall_mem_support_exists_specializes_map_germ_le
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_le_of_forall_mem_support_exists_specializes_map_germ_le (solution)
