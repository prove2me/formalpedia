-- Prove2me | solution 1 for AlgebraicGeometry.isReduced_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/932ecbf8-03be-5153-812f-bebb3316b978

import Mathlib
import Theorems.Thm_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isReduced_of_etale
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace L3gen

theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal Z with hI
  have hrad : I.radical = I := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    have hsupp : I.support = Z := by
      apply Closeds.ext
      rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rw [hsupp]
  haveI : ∀ U : I.subschemeCover.I₀, IsReduced (I.subschemeCover.openCover.X U) := by
    intro U
    show IsReduced (Spec _)
    rw [affine_isReduced_iff]
    show _root_.IsReduced (_ ⧸ I.ideal U)
    have hradU : (I.ideal U).radical = I.ideal U := by
      rw [← Scheme.IdealSheafData.radical_ideal, hrad]
    exact (Ideal.isRadical_iff_quotient_reduced _).mp (hradU ▸ Ideal.radical_isRadical _)
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

theorem isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := by

  suffices h : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) by
    haveI := h; exact isReduced_of_isReduced_stalk X
  intro x
  obtain ⟨U, hU, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨U', hU'aff, rfl⟩ := hU
  have hxV0 : x ∈ (f ⁻¹ᵁ U' : X.Opens) := hxU
  obtain ⟨V, hV, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV0 (f ⁻¹ᵁ U').2
  obtain ⟨V', hV'aff, rfl⟩ := hV

  have het : (f.appLE U' V' hVU).hom.Etale := Etale.etale_appLE f hU'aff hV'aff hVU
  letI := (f.appLE U' V' hVU).hom.toAlgebra
  haveI : Algebra.Etale Γ(Y, U') Γ(X, V') := het
  haveI : IsNoetherianRing Γ(Y, U') := IsLocallyNoetherian.component_noetherian ⟨U', hU'aff⟩
  haveI : _root_.IsReduced Γ(Y, U') := IsReduced.component_reduced _
  have hredV : _root_.IsReduced Γ(X, V') := Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing Γ(Y, U') Γ(X, V')

  haveI : IsAffine (V' : Scheme.{u}) := hV'aff

  letI : Algebra Γ(X, V') (X.presheaf.stalk ((⟨x, hxV⟩ : V') : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V')
  haveI := hV'aff.isLocalization_stalk ⟨x, hxV⟩
  exact isReduced_localizationPreserves (hV'aff.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk ((⟨x, hxV⟩ : V') : X)) hredV

end L3gen

theorem solution {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := L3gen.isReduced_of_etale f

end S_AlgebraicGeometry_isReduced_of_etale
end P2MW
export P2MW.S_AlgebraicGeometry_isReduced_of_etale (solution)
