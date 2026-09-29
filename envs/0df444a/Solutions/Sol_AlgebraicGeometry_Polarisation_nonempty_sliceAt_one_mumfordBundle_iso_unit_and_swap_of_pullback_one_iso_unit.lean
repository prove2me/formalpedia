-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/97fef3b3-51d4-509f-8e75-9bf0198695c9

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace AxesTriv

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (N : A.Modules)

theorem comp_addMor {P : Scheme.{0}} (g : P ⟶ pullback f f) :
    g ≫ addMor f L =
      (L.mul (g ≫ pullback.fst f f ≫ f)
        ⟨g ≫ pullback.fst f f, rfl⟩
        ⟨g ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]⟩).1 := by
  have hψ : g ≫ (pullback.fst f f ≫ f) = g ≫ pullback.fst f f ≫ f := rfl
  have h := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (g ≫ pullback.fst f f ≫ f) g hψ
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  exact h

theorem sliceAt_one_comp_addMor :
    sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ addMor f L = pullback.fst f (𝟙 _) := by
  rw [comp_addMor]
  have hq : sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ pullback.fst f f = pullback.fst f (𝟙 _) :=
    pullback.lift_fst _ _ _
  have hr : sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ pullback.snd f f =
      pullback.snd f (𝟙 _) ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 :=
    pullback.lift_snd _ _ _

  have hone : (⟨sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ pullback.snd f f,
        by rw [Category.assoc, ← pullback.condition]⟩ :
        SchemeHomOver (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ pullback.fst f f ≫ f) f) =
      L.one _ := by
    rw [← L.one_natural (𝟙 _) (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ pullback.fst f f ≫ f)
      (pullback.snd f (𝟙 _)) (by rw [Category.comp_id, ← Category.assoc, hq, pullback.condition, Category.comp_id])]
    exact Subtype.ext hr
  rw [hone, L.mul_one]
  exact hq

theorem sliceAt_one_swap_comp_addMor :
    (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ (pullbackSymmetry f f).hom) ≫ addMor f L =
      pullback.fst f (𝟙 _) := by
  rw [comp_addMor]
  have hq : (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ (pullbackSymmetry f f).hom) ≫ pullback.snd f f =
      pullback.fst f (𝟙 _) := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]; exact pullback.lift_fst _ _ _
  have hr : (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ (pullbackSymmetry f f).hom) ≫ pullback.fst f f =
      pullback.snd f (𝟙 _) ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]; exact pullback.lift_snd _ _ _
  have hbase : (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ (pullbackSymmetry f f).hom) ≫ pullback.fst f f ≫ f =
      pullback.fst f (𝟙 _) ≫ f := by
    rw [← Category.assoc, hr, Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of S)))).2, Category.comp_id,
      pullback.condition, Category.comp_id]
  have hone : (⟨(sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ (pullbackSymmetry f f).hom) ≫ pullback.fst f f, rfl⟩ :
        SchemeHomOver ((sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))) ≫ (pullbackSymmetry f f).hom) ≫
          pullback.fst f f ≫ f) f) = L.one _ := by
    rw [← L.one_natural (𝟙 _) _ (pullback.snd f (𝟙 _)) (by rw [Category.comp_id, hbase, pullback.condition, Category.comp_id])]
    exact Subtype.ext hr
  rw [hone, L.one_mul]
  exact hq

end AxesTriv

open AxesTriv in
theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (he : Nonempty ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj N ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))))).obj (mumfordBundle f L N) ≅ 𝟙_ _) ∧
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S)))))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj (mumfordBundle f L N)) ≅ 𝟙_ _) := by
  classical
  obtain ⟨ε⟩ := he

  let e : Spec (CommRingCat.of S) ⟶ A := (L.one (𝟙 (Spec (CommRingCat.of S)))).1
  let s := sliceAt f (L.one (𝟙 (Spec (CommRingCat.of S))))
  let q := pullback.fst f (𝟙 (Spec (CommRingCat.of S)))
  let r := pullback.snd f (𝟙 (Spec (CommRingCat.of S)))
  have hs1 : s ≫ pullback.fst f f = q := pullback.lift_fst _ _ _
  have hs2 : s ≫ pullback.snd f f = r ≫ e := pullback.lift_snd _ _ _
  have hsμ : s ≫ addMor f L = q := sliceAt_one_comp_addMor f L
  have ht1 : (s ≫ (pullbackSymmetry f f).hom) ≫ pullback.fst f f = r ≫ e := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]; exact hs2
  have ht2 : (s ≫ (pullbackSymmetry f f).hom) ≫ pullback.snd f f = q := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]; exact hs1
  have htμ : (s ≫ (pullbackSymmetry f f).hom) ≫ addMor f L = q := sliceAt_one_swap_comp_addMor f L

  obtain ⟨D⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hN).2
  have hNe := hN.pullback e
  obtain ⟨De⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hNe).2
  obtain ⟨Pe⟩ := Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 e hN
  have T0 : Scheme.Modules.dual ((Scheme.Modules.pullback e).obj N) ≅ 𝟙_ _ :=
    (λ_ _).symm ≪≫ (ε.symm ⊗ᵢ Iso.refl _) ≪≫ De
  have Tr : (Scheme.Modules.pullback (r ≫ e)).obj (Scheme.Modules.dual N) ≅ 𝟙_ _ :=
    ((Scheme.Modules.pullbackComp r e).app _).symm ≪≫ (Scheme.Modules.pullback r).mapIso (Pe ≪≫ T0) ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso r

  have Pair : (Scheme.Modules.pullback q).obj N ⊗ (Scheme.Modules.pullback q).obj (Scheme.Modules.dual N) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso q _ _).symm ≪≫ (Scheme.Modules.pullback q).mapIso D ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso q
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact Scheme.Modules.pullbackTensorObjIso s _ _ ≪≫
      (((Scheme.Modules.pullbackComp s _).app N ≪≫ (Scheme.Modules.pullbackCongr hsμ).app N) ⊗ᵢ
        (Scheme.Modules.pullbackTensorObjIso s _ _ ≪≫
          ((((Scheme.Modules.pullbackComp s _).app _ ≪≫ (Scheme.Modules.pullbackCongr hs1).app _)) ⊗ᵢ
            (((Scheme.Modules.pullbackComp s _).app _ ≪≫ (Scheme.Modules.pullbackCongr hs2).app _) ≪≫ Tr)) ≪≫
          ρ_ _)) ≪≫ Pair
  · exact (Scheme.Modules.pullbackComp s (pullbackSymmetry f f).hom).app _ ≪≫
      Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr htμ).app N) ⊗ᵢ
        (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
          (((((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr ht1).app _) ≪≫ Tr)) ⊗ᵢ
            ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr ht2).app _)) ≪≫
          λ_ _)) ≪≫ Pair

end S_AlgebraicGeometry_Polarisation_nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit (solution)
