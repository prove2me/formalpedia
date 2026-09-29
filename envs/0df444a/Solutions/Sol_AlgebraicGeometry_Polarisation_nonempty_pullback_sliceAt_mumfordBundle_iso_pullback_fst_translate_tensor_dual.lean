-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fst_translate_tensor_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0a82da74-b8c3-516f-a084-4661ab0028f2

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fst_translate_tensor_dual

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace SliceLink

p2m_open "GoodReductionJacobian AlgebraicGeometry.Polarisation CategoryTheory.MonoidalCategory"

variable {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

theorem triv_of_isInvertible_field (N : (Spec (CommRingCat.of k)).Modules) (hN : Scheme.Modules.IsInvertible N) :
    Nonempty (N ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := hN.1 default
  have hall : ∀ p : ↥(Spec (CommRingCat.of k)), p ∈ U := fun p => by rw [Subsingleton.elim p default]; exact hU
  let s : Spec (CommRingCat.of k) ⟶ (U : Scheme.{0}) :=
    IsOpenImmersion.lift U.ι (𝟙 _) (by rintro p ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; exact hall _)
  have hs : s ≫ U.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  exact ⟨((Scheme.Modules.pullbackId _).app N).symm ≪≫ ((Scheme.Modules.pullbackCongr hs).app N).symm ≪≫
    ((Scheme.Modules.pullbackComp s U.ι).app N).symm ≪≫ (Scheme.Modules.pullback s).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso s⟩

theorem mulRight_eq (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    L.mulRight (𝟙 (Spec (CommRingCat.of k))) x = pullback.fst f (𝟙 _) ≫ L.translate x := by
  have hψ : pullback.fst f (𝟙 (Spec (CommRingCat.of k))) ≫ f = pullback.snd f (𝟙 _) ≫ 𝟙 _ := pullback.condition
  have h := congrArg Subtype.val (L.mul_natural f _ (pullback.fst f (𝟙 _)) hψ RelativeGroupLaw.idPoint
    ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩)
  have h1 : schemeHomOverComp (pullback.fst f (𝟙 _)) hψ (RelativeGroupLaw.idPoint (f := f)) = L.fstPoint (𝟙 _) :=
    Subtype.ext (Category.comp_id _)
  have h2 : schemeHomOverComp (pullback.fst f (𝟙 _)) hψ
      (⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩ : SchemeHomOver f f) = L.sndPoint (𝟙 _) x := by
    apply Subtype.ext
    change pullback.fst f (𝟙 _) ≫ f ≫ x.1 = pullback.snd f (𝟙 _) ≫ x.1
    rw [← Category.assoc, hψ, Category.assoc, Category.id_comp]
  rw [h1, h2] at h
  exact h.symm

set_option maxHeartbeats 6400000 in
theorem main [IsAlgClosed k] (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback (pullback.fst f (𝟙 (Spec (CommRingCat.of k))))).obj
        ((Scheme.Modules.pullback (L.translate x)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛)) := by
  let t := 𝟙 (Spec (CommRingCat.of k))
  let pfst := pullback.fst f t
  let psnd := pullback.snd f t
  let σ := sliceAt f x
  let Lv := Scheme.Modules.dual 𝓛
  have hLv : Scheme.Modules.IsInvertible Lv := (AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).1
  have hσ1 : σ ≫ pullback.fst f f = pfst := pullback.lift_fst _ _ _
  have hσ2 : σ ≫ pullback.snd f f = psnd ≫ x.1 := pullback.lift_snd _ _ _

  have hσbase : σ ≫ (pullback.fst f f ≫ f) = psnd ≫ t := by
    rw [← Category.assoc, hσ1]; exact pullback.condition
  have hσadd : σ ≫ addMor f L = pfst ≫ L.translate x := by
    have h := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f) (psnd ≫ t) σ hσbase
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    have h1 : schemeHomOverComp σ hσbase (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) =
        L.fstPoint t := Subtype.ext hσ1
    have h2 : schemeHomOverComp σ hσbase (⟨pullback.snd f f, pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst f f ≫ f) f) = L.sndPoint t x := Subtype.ext hσ2
    rw [h1, h2] at h
    change σ ≫ addMor f L = L.mulRight t x at h
    rw [h, mulRight_eq]
  obtain ⟨T0⟩ := triv_of_isInvertible_field ((Scheme.Modules.pullback x.1).obj Lv) (hLv.pullback x.1)
  let E1 : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) ≅
      (Scheme.Modules.pullback pfst).obj ((Scheme.Modules.pullback (L.translate x)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp σ (addMor f L)).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hσadd).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp pfst (L.translate x)).app 𝓛).symm
  let E2 : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj Lv) ≅
      (Scheme.Modules.pullback pfst).obj Lv :=
    (Scheme.Modules.pullbackComp σ (pullback.fst f f)).app Lv ≪≫ (Scheme.Modules.pullbackCongr hσ1).app Lv
  let E3 : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj Lv) ≅
      𝟙_ (pullback f t).Modules :=
    (Scheme.Modules.pullbackComp σ (pullback.snd f f)).app Lv ≪≫ (Scheme.Modules.pullbackCongr hσ2).app Lv ≪≫
      ((Scheme.Modules.pullbackComp psnd x.1).app Lv).symm ≪≫ (Scheme.Modules.pullback psnd).mapIso T0 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso psnd
  refine ⟨?_⟩
  change (Scheme.Modules.pullback σ).obj (_ ⊗ (_ ⊗ _)) ≅ (Scheme.Modules.pullback pfst).obj (_ ⊗ _)
  exact Scheme.Modules.pullbackTensorObjIso σ _ _ ≪≫ (E1 ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso σ _ _)) ≪≫
    (Iso.refl _ ⊗ᵢ (E2 ⊗ᵢ E3)) ≪≫ (Iso.refl _ ⊗ᵢ ρ_ _) ≪≫ (Scheme.Modules.pullbackTensorObjIso pfst _ _).symm

end SliceLink

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback (pullback.fst f (𝟙 (Spec (CommRingCat.of k))))).obj
        ((Scheme.Modules.pullback (L.translate x)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛)) :=
  SliceLink.main L 𝓛 h𝓛 x

end S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fst_translate_tensor_dual
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_iso_pullback_fst_translate_tensor_dual (solution)
