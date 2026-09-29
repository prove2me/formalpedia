-- Prove2me | solution 1 for AlgebraicGeometry.Spec.exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3aea0323-9379-57c7-aafe-33b2fc35aee3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Spec_exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    {A : Type} [CommRing A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (L : Type) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L 𝔭]
    {X : Scheme.{0}} (y y' : Spec (CommRingCat.of A) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ y = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ y') :
    ∃ f : A, f ∉ 𝔭 ∧ ∀ (Af : Type) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af],
      Spec.map (CommRingCat.ofHom (algebraMap A Af)) ≫ y = Spec.map (CommRingCat.ofHom (algebraMap A Af)) ≫ y' := by
  classical
  let x : ↥(Spec (CommRingCat.of A)) := (⟨𝔭, ‹𝔭.IsPrime›⟩ : PrimeSpectrum A)

  letI : Algebra A ↑((Spec (CommRingCat.of A)).presheaf.stalk x) := StructureSheaf.stalkAlgebra A x
  haveI : IsLocalization.AtPrime (↑((Spec (CommRingCat.of A)).presheaf.stalk x)) 𝔭 :=
    StructureSheaf.IsLocalization.to_stalk A x
  let e : L ≃ₐ[A] ↑((Spec (CommRingCat.of A)).presheaf.stalk x) := IsLocalization.algEquiv 𝔭.primeCompl _ _
  let ι₂ : CommRingCat.of L ⟶ (Spec (CommRingCat.of A)).presheaf.stalk x := CommRingCat.ofHom e.toRingHom
  have hto : StructureSheaf.toStalk A x = CommRingCat.ofHom (algebraMap A L) ≫ ι₂ := by
    ext a
    show algebraMap A _ a = e (algebraMap A L a)
    rw [AlgEquiv.commutes]
  have hstalk : (Spec (CommRingCat.of A)).fromSpecStalk x ≫ y = (Spec (CommRingCat.of A)).fromSpecStalk x ≫ y' := by
    have e0 : (Spec (CommRingCat.of A)).fromSpecStalk x =
        Spec.map ι₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap A L)) := by
      rw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
      exact congrArg Spec.map hto
    rw [e0, Category.assoc, Category.assoc, h]
  obtain ⟨U, hxU, hU⟩ := spread_out_unique_of_isGermInjective' y y' hstalk

  obtain ⟨V, hV, hxf, hfU⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  obtain ⟨W, ⟨f, rfl⟩, rfl⟩ := hV
  refine ⟨f, (PrimeSpectrum.mem_basicOpen (R := A) f x).mp hxf, ?_⟩
  intro Af _ _ _
  have hrange : Set.range ⇑(Spec.map (CommRingCat.ofHom (algebraMap A Af))) ⊆ Set.range ⇑U.ι := by
    rw [Scheme.Opens.range_ι]
    intro q hq
    apply hfU
    have : Set.range ⇑(Spec.map (CommRingCat.ofHom (algebraMap A Af))) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
      show Set.range (PrimeSpectrum.comap (algebraMap A Af)) = _
      exact PrimeSpectrum.localization_away_comap_range Af f
    rw [this] at hq
    exact hq
  have hfac := IsOpenImmersion.lift_fac U.ι (Spec.map (CommRingCat.ofHom (algebraMap A Af))) hrange
  rw [← hfac, Category.assoc, hU, ← Category.assoc]

end S_AlgebraicGeometry_Spec_exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Spec_exists_forall_away_specMap_comp_eq_of_atPrime_specMap_comp_eq (solution)
