-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/978d2a5c-25e8-576f-899c-69fcfeaa52e7

import Mathlib
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_exists_isPushout_of_surjective_of_forall_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace SmoothLocLift

theorem presheafMap_isStandardSmooth {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.IsStandardSmooth := by
  haveI : IsAffine V := hV
  have e : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ U := fun x _ => h x.2
  have h1 : (V.ι.appLE U ⊤ e).hom.Etale :=
    HasRingHomProperty.appLE @Etale V.ι inferInstance ⟨U, hU⟩ ⟨⊤, isAffineOpen_top _⟩ e
  rw [Scheme.Opens.ι_appLE] at h1
  have h2 : (X.presheaf.map (homOfLE h).op) =
      X.presheaf.map (homOfLE (x := V.ι ''ᵁ ⊤) (Set.image_subset_iff.mpr e)).op ≫
        X.presheaf.map (eqToHom V.ι_image_top.symm).op := by
    rw [← X.presheaf.map_comp]
    rfl
  have h3 : (X.presheaf.map (homOfLE h).op).hom.Etale := by
    rw [h2, CommRingCat.hom_comp]
    exact RingHom.Etale.propertyIsLocal.respectsIso.1 _
      (X.presheaf.mapIso (eqToIso V.ι_image_top.symm).op).commRingCatIsoToRingEquiv h1
  exact (RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth 0 _
    ((RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero).mp h3))

section Charts

variable {B X₀ : Scheme.{u}} (f₀ : X₀ ⟶ B) [IsAffine B]

theorem exists_chart [Smooth f₀] (x : X₀) :
    ∃ U : X₀.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ V : X₀.Opens, IsAffineOpen V → V ≤ U → (f₀.appLE ⊤ V le_top).hom.IsStandardSmooth := by
  obtain ⟨W, hW, U, hU, hxU, e, hst⟩ := Smooth.exists_isStandardSmooth f₀ x
  refine ⟨U, hxU, hU, fun V hV hVU => ?_⟩

  have hB := presheafMap_isStandardSmooth (isAffineOpen_top B) hW le_top
  have hX := presheafMap_isStandardSmooth hU hV hVU
  have hcomp := (hX.comp hst).comp hB
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE] at hcomp
  exact hcomp

end Charts

section Lift

variable {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀)
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of S₀))

noncomputable def toΓ (V : X₀.Opens) : CommRingCat.of S₀ ⟶ Γ(X₀, V) :=
  (Scheme.ΓSpecIso (CommRingCat.of S₀)).inv ≫ f₀.appLE ⊤ V le_top

theorem ι_comp_eq (V : X₀.Opens) (hV : IsAffineOpen V) :
    V.ι ≫ f₀ = hV.isoSpec.hom ≫ Spec.map (toΓ f₀ V) := by
  rw [toΓ, Spec.map_comp, IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
    Scheme.Opens.toSpecΓ_top, Category.assoc, ← Scheme.isoSpec_Spec_inv,
    ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id, Scheme.Hom.resLE_comp_ι]

theorem exists_lift (hp : Function.Surjective p) (hnil : ∀ x ∈ RingHom.ker p, IsNilpotent x)
    (V : X₀.Opens) (hV : IsAffineOpen V) (hst : (f₀.appLE ⊤ V le_top).hom.IsStandardSmooth) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of S)) (g : (V : Scheme.{u}) ⟶ Y),
      IsAffine Y ∧ Smooth q ∧ IsPullback g (V.ι ≫ f₀) q (Spec.map (CommRingCat.ofHom p)) := by

  set A₀ : Type u := Γ(X₀, V) with hA₀
  letI algS₀ : Algebra S₀ A₀ := (toΓ f₀ V).hom.toAlgebra
  letI algSS₀ : Algebra S S₀ := p.toAlgebra
  letI algS : Algebra S A₀ := ((toΓ f₀ V).hom.comp p).toAlgebra
  haveI : IsScalarTower S S₀ A₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hst' : (toΓ f₀ V).hom.IsStandardSmooth := by
    rw [toΓ, CommRingCat.hom_comp]
    exact RingHom.isStandardSmooth_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of S₀)).symm.commRingCatIsoToRingEquiv hst
  have hA : Algebra.IsStandardSmooth S₀ A₀ := hst'
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hA
  haveI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension S₀ A₀ := ⟨ι, σ, _, ‹_›, P, rfl⟩

  have hsurj : Function.Surjective (algebraMap S S₀) := hp
  have hnil' : ∀ x ∈ RingHom.ker (algebraMap S S₀), IsNilpotent x := hnil
  obtain ⟨A, _, _, _, _, hss, -, -, hpo⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_isPushout_of_surjective_of_forall_isNilpotent
      P.dimension hsurj hnil' A₀

  have hPO := CommRingCat.isPushout_of_isPushout S S₀ A A₀
  have hPB := (isPullback_SpecMap_of_isPushout _ _ _ _ hPO).flip

  refine ⟨Spec (CommRingCat.of A), Spec.map (CommRingCat.ofHom (algebraMap S A)),
    hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A A₀)), inferInstance, ?_, ?_⟩
  ·
    rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom, RingHom.smooth_algebraMap]
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth P.dimension (R := S) (S := A)
    infer_instance
  ·
    have e4 : (CommRingCat.ofHom (algebraMap S S₀)) = CommRingCat.ofHom p := rfl
    have e3 : (CommRingCat.ofHom (algebraMap S₀ A₀)) = toΓ f₀ V := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    refine hPB.of_iso hV.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ι_comp_eq f₀ V hV, Iso.inv_hom_id_assoc, e3]
    · simp
    · rw [e4]; simp

end Lift

end SmoothLocLift

open SmoothLocLift in
theorem solution
    {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀) (hp : Function.Surjective p)
    (hnil : ∀ x ∈ RingHom.ker p, IsNilpotent x)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of S₀)) [Smooth f₀] (x : X₀) :
    ∃ U : X₀.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ V : X₀.Opens, IsAffineOpen V → V ≤ U →
        ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of S)) (g : (V : Scheme.{u}) ⟶ Y),
          IsAffine Y ∧ Smooth q ∧ IsPullback g (V.ι ≫ f₀) q (Spec.map (CommRingCat.ofHom p)) := by
  obtain ⟨U, hxU, hU, hch⟩ := exists_chart f₀ x
  exact ⟨U, hxU, hU, fun V hV hVU => exists_lift p f₀ hp hnil V hV (hch V hV hVU)⟩

end S_AlgebraicGeometry_Smooth_exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent (solution)
