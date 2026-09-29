-- Prove2me | solution 1 for AlgebraicGeometry.SchemeHomOver.apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c05717e3-16da-55c0-b443-733bfed4b86e

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

import Theorems.Thm_Algebra_FormallySmooth_of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation c] [Flat c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c)
    (hreg : IsRegularLocalRing (C.presheaf.stalk (ε.1.base (IsLocalRing.closedPoint A)))) :
    ε.1.base (IsLocalRing.closedPoint A) ∈ c.smoothLocus := by
  classical
  set s := IsLocalRing.closedPoint A with hs

  have hcx : c.base (ε.1.base s) = s := by
    rw [← Scheme.Hom.comp_apply, ε.2]
    rfl
  have hft := LocallyOfFiniteType.stalkMap c (ε.1.base s)
  have hfl := Flat.stalkMap c (ε.1.base s)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(c.stalkMap (ε.1.base s)).hom]

  haveI : IsRegularLocalRing (C.presheaf.stalk (ε.1.base s)) := hreg
  have hunits : (c.base (ε.1.base s)).asIdeal.primeCompl ≤ IsUnit.submonoid A := by
    intro a ha
    rw [hcx] at ha
    by_contra hna
    exact ha ((IsLocalRing.mem_maximalIdeal a).mpr hna)
  let e : A ≃ₐ[A] (Spec.structureSheaf A).presheaf.stalk (c.base (ε.1.base s)) :=
    IsLocalization.atUnits A (c.base (ε.1.base s)).asIdeal.primeCompl hunits
  let e' : A ≃+* (Spec (CommRingCat.of A)).presheaf.stalk (c.base (ε.1.base s)) := e.toRingEquiv
  haveI : IsNoetherianRing ((Spec (CommRingCat.of A)).presheaf.stalk (c.base (ε.1.base s))) :=
    isNoetherianRing_of_ringEquiv A e'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmaxA : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hmax : IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk (c.base (ε.1.base s))) =
      Ideal.span {e' ϖ} := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e', hmaxA, Ideal.map_span, Set.image_singleton]
  haveI : IsLocalHom (algebraMap ((Spec (CommRingCat.of A)).presheaf.stalk (c.base (ε.1.base s)))
      (C.presheaf.stalk (ε.1.base s))) :=
    inferInstanceAs (IsLocalHom (c.stalkMap (ε.1.base s)).hom)

  have key : c.stalkMap (ε.1.base s) ≫ ε.1.stalkMap s =
      ((Spec (CommRingCat.of A)).presheaf.stalkCongr (.of_eq hcx)).hom := by
    have h := Scheme.Hom.stalkMap_comp ε.1 c s
    rw [Scheme.Hom.stalkMap_congr_hom _ _ ε.2 s, Scheme.Hom.stalkMap_id] at h
    erw [Category.comp_id] at h
    exact h.symm
  let ρ₀ : C.presheaf.stalk (ε.1.base s) →+* (Spec (CommRingCat.of A)).presheaf.stalk (c.base (ε.1.base s)) :=
    (ε.1.stalkMap s ≫ ((Spec (CommRingCat.of A)).presheaf.stalkCongr (.of_eq hcx)).inv).hom
  let ρ : C.presheaf.stalk (ε.1.base s) →ₐ[(Spec (CommRingCat.of A)).presheaf.stalk (c.base (ε.1.base s))]
      (Spec (CommRingCat.of A)).presheaf.stalk (c.base (ε.1.base s)) :=
    { toRingHom := ρ₀
      commutes' := fun r => by
        show (c.stalkMap (ε.1.base s) ≫ ε.1.stalkMap s ≫
          ((Spec (CommRingCat.of A)).presheaf.stalkCongr (.of_eq hcx)).inv).hom r = r
        rw [reassoc_of% key, Iso.hom_inv_id]
        rfl }
  exact Algebra.FormallySmooth.of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span
    ((Spec (CommRingCat.of A)).presheaf.stalk (c.base (ε.1.base s))) (e' ϖ) hmax (C.presheaf.stalk (ε.1.base s)) ρ

end S_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk (solution)
