-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_polarisation_pair_of_block
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4d776f2f-73d2-554e-8cb0-d02796f4f0fd

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal

import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso SmoothOfRelativeDimension pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Hom Spec Spec.map Scheme pullbackSpecIso pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Scheme.Hom.comp_base IsClosedImmersion IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange pullbackSpecIso_inv_snd_assoc Etale Scheme.Modules pullbackRestrictIsoRestrict Scheme.Hom.comp_apply Scheme.IdealSheafData RelPicard.rigSection RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_fst_assoc RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv.ofPoint RelPicard.sectionIdeal RelEffCartierDiv.exists_I_eq_ker_lift_and_supportedIn_of_finite_etale RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn RelEffCartierDiv.isInvertible_I_of_supportedIn RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn RelEffCartierDiv.supportedIn_ofPoint Scheme.IdealSheafData.comap_mul"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection sectionIdeal"
namespace N12
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem smoothOfRelativeDimension_one_preimage_ι_comp_snd {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of R)) :
    SmoothOfRelativeDimension 1 ((pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have h : (pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s =
      (pullbackRestrictIsoRestrict (pullback.fst c s) U).inv ≫ (pullbackSymmetry (pullback.fst c s) U.ι).hom ≫
        (pullbackRightPullbackFstIso c s U.ι).hom ≫ pullback.snd (U.ι ≫ c) s := by
    rw [pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc,
      pullbackRestrictIsoRestrict_inv_fst_assoc]
  rw [h, MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1),
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1),
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)]
  infer_instance

def castDeg {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S} {r s : ℕ} (h : r = s)
    (D : RelEffCartierDiv f r g) : RelEffCartierDiv f s g :=
  ⟨D.I, D.isFinite, D.flat, D.locallyOfFinitePresentation, fun t => (D.finrank_eq t).trans h⟩

@[scoped simp] theorem castDeg_I {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S} {r s : ℕ} (h : r = s)
    (D : RelEffCartierDiv f r g) : (castDeg h D).I = D.I := rfl

theorem castDeg_supportedIn {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S} {r s : ℕ} (h : r = s)
    (D : RelEffCartierDiv f r g) {U : 𝒞.Opens} (hD : D.SupportedIn U) : (castDeg h D).SupportedIn U := hD

theorem range_subset_preimage_of_comp_eq {X C T Y : Scheme.{u}} (s : T ⟶ X) (p : X ⟶ C) (y : T ⟶ Y) (z : Y ⟶ C)
    (h : s ≫ p = y ≫ z) (U : C.Opens) (hzU : Set.range z.base ⊆ (U : Set C)) :
    Set.range s.base ⊆ ((p ⁻¹ᵁ U : X.Opens) : Set X) := by
  rintro _ ⟨t, rfl⟩
  show p.base (s.base t) ∈ U
  have e := congrArg (fun k : T ⟶ C => k.base t) h
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e
  rw [e]
  exact hzU ⟨_, rfl⟩

theorem exists_I_eq_pow_and_supportedIn {𝒳 S : Scheme.{u}} {f : 𝒳 ⟶ S} [IsSeparated f] (U : 𝒳.Opens)
    [SmoothOfRelativeDimension 1 (U.ι ≫ f)] {e : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f e g) (hD : D.SupportedIn U) :
    ∀ n : ℕ, ∃ F : RelEffCartierDiv f (n * e) g, F.I = D.I ^ n ∧ F.SupportedIn U
  | 0 => ⟨castDeg (by simp) (RelEffCartierDiv.empty f g), by
      rw [castDeg_I, RelEffCartierDiv.empty_I, pow_zero]; rfl, by
      intro x hx
      rw [castDeg_I, RelEffCartierDiv.empty_I] at hx
      simp at hx⟩
  | n + 1 => by
      obtain ⟨F, hFI, hFU⟩ := exists_I_eq_pow_and_supportedIn U D hD n
      obtain ⟨G, hGI, hGU⟩ := RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U F D hFU hD
      exact ⟨castDeg (by ring) G, by rw [castDeg_I, hGI, hFI, pow_succ], castDeg_supportedIn _ _ hGU⟩

theorem exists_sectionIdeal_pow_mul_pow {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1.base ⊆ (U : Set C))
    {d : ℕ} (Z : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of R)))) (hZU : Z.SupportedIn U) (r r' : ℕ) :
    ∃ E : RelEffCartierDiv c (r + r' * d) (𝟙 (Spec (CommRingCat.of R))),
      E.SupportedIn U ∧ E.I = (sectionIdeal c ε (𝟙 (Spec (CommRingCat.of R)))) ^ r * Z.I ^ r' := by

  have h1 : (𝟙 (Spec (CommRingCat.of R)) ≫ ε.1) ≫ c = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [Category.assoc, ε.2, Category.comp_id]
  let Dε : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of R))) := RelEffCartierDiv.ofPoint c (𝟙 _ ≫ ε.1) h1
  have hDεI : Dε.I = sectionIdeal c ε (𝟙 (Spec (CommRingCat.of R))) := rfl
  have hDεU : Dε.SupportedIn U := by
    refine RelEffCartierDiv.supportedIn_ofPoint (𝟙 _ ≫ ε.1) h1 U fun t => ?_
    rw [Scheme.Hom.comp_apply]
    exact hεU ⟨_, rfl⟩
  obtain ⟨F, hFI, hFU⟩ := exists_I_eq_pow_and_supportedIn U Dε hDεU r
  obtain ⟨G, hGI, hGU⟩ := exists_I_eq_pow_and_supportedIn U Z hZU r'
  obtain ⟨E, hEI, hEU⟩ := RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U F G hFU hGU
  exact ⟨castDeg (by ring) E, castDeg_supportedIn _ _ hEU, by rw [castDeg_I, hEI, hFI, hGI, hDεI]⟩

theorem comap_pow {X Y : Scheme.{u}} (φ : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).comap φ = (I.comap φ) ^ n := by
  induction n with
  | zero => simp [Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

section Compat

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A]

def gMap : pullback (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) ⟶ pullback c (𝟙 (Spec (CommRingCat.of R))) :=
  pullback.map (baseChange R c A) (𝟙 _) c (𝟙 _) (pullback.fst c (specMap R A)) (specMap R A) (specMap R A)
    (pullback.condition).symm (by simp)

@[reassoc (attr := simp)]
theorem gMap_fst : gMap c A ≫ pullback.fst c (𝟙 _) =
    pullback.fst (baseChange R c A) (𝟙 _) ≫ pullback.fst c (specMap R A) :=
  pullback.lift_fst _ _ _

theorem snd_eq_fst_comp (c : C ⟶ Spec (CommRingCat.of R)) :
    pullback.snd c (𝟙 (Spec (CommRingCat.of R))) = pullback.fst c (𝟙 _) ≫ c := by
  rw [pullback.condition, Category.comp_id]

scoped instance isClosedImmersion_rigSection {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : IsClosedImmersion (rigSection c t ε) := by
  haveI : IsSeparated (pullback.snd c t) := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by
    rw [RelPicard.rigSection, pullback.lift_snd]; infer_instance
  exact IsClosedImmersion.of_comp (rigSection c t ε) (pullback.snd c t)

theorem comap_gMap_sectionIdeal [IsSeparated c] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    (sectionIdeal c ε (𝟙 _)).comap (gMap c A) =
      sectionIdeal (baseChange R c A) (sectionBaseChange A ε) (𝟙 _) := by
  haveI : IsSeparated (baseChange R c A) := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance

  have s : IsPullback ((sectionBaseChange A ε).1 ≫ baseChange R c A) (specMap R A) (specMap R A) (ε.1 ≫ c) := by
    rw [(sectionBaseChange A ε).2, ε.2]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have t : IsPullback (baseChange R c A) (pullback.fst c (specMap R A)) (specMap R A) c :=
    (IsPullback.of_hasPullback c (specMap R A)).flip
  have sq0 : IsPullback (sectionBaseChange A ε).1 (specMap R A) (pullback.fst c (specMap R A)) ε.1 :=
    IsPullback.of_right s (sectionBaseChange_coe_fst A ε) t

  have sq1 : IsPullback (rigSection (baseChange R c A) (𝟙 _) (sectionBaseChange A ε)) (specMap R A)
      (gMap c A) (rigSection c (𝟙 _) ε) := by
    refine sq0.of_iso (Iso.refl _) (asIso (pullback.fst (baseChange R c A) (𝟙 _))).symm (Iso.refl _)
      (asIso (pullback.fst c (𝟙 _))).symm ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, RelPicard.rigSection,
        pullback.lift_fst, Category.id_comp]
    · simp
    · rw [Iso.symm_hom, asIso_inv, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc,
        IsIso.comp_inv_eq, gMap_fst]
    · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, RelPicard.rigSection,
        pullback.lift_fst, Category.id_comp]
  rw [RelPicard.sectionIdeal, RelPicard.sectionIdeal, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← sq1.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

theorem ker_lift_eq_comap_gMap_ker_lift {B₀ AB : Type u} [CommRing B₀] [CommRing AB] [Algebra R B₀] [Algebra A AB]
    (z₀ : Spec (CommRingCat.of B₀) ⟶ C) [IsClosedImmersion z₀] (hz₀ : z₀ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B₀)))
    (e : Spec (CommRingCat.of AB) ≅ pullback z₀ (pullback.fst c (specMap R A)))
    (x : Spec (CommRingCat.of AB) ⟶ pullback c (specMap R A)) (hxe : x = e.hom ≫ pullback.snd z₀ (pullback.fst c (specMap R A)))
    (hx_snd : x ≫ baseChange R c A = Spec.map (CommRingCat.ofHom (algebraMap A AB))) :
    (pullback.lift (f := baseChange R c A) (g := 𝟙 (Spec (CommRingCat.of A))) x
        (Spec.map (CommRingCat.ofHom (algebraMap A AB))) (by rw [Category.comp_id]; exact hx_snd)).ker =
      (pullback.lift (f := c) (g := 𝟙 (Spec (CommRingCat.of R))) z₀
        (Spec.map (CommRingCat.ofHom (algebraMap R B₀))) (by rw [Category.comp_id]; exact hz₀)).ker.comap (gMap c A) := by
  set zA := pullback.lift (f := baseChange R c A) (g := 𝟙 (Spec (CommRingCat.of A))) x
    (Spec.map (CommRingCat.ofHom (algebraMap A AB))) (by rw [Category.comp_id]; exact hx_snd)
  set w₀ := pullback.lift (f := c) (g := 𝟙 (Spec (CommRingCat.of R))) z₀
    (Spec.map (CommRingCat.ofHom (algebraMap R B₀))) (by rw [Category.comp_id]; exact hz₀)
  haveI : IsClosedImmersion w₀ := by
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion w₀ (pullback.fst c (𝟙 _)), pullback.lift_fst]
    infer_instance

  have sq0 : IsPullback x (e.hom ≫ pullback.fst z₀ (pullback.fst c (specMap R A))) (pullback.fst c (specMap R A)) z₀ := by
    refine (IsPullback.of_hasPullback z₀ (pullback.fst c (specMap R A))).flip.of_iso e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · rw [hxe]; simp
    · simp

  have sq1 : IsPullback zA (e.hom ≫ pullback.fst z₀ (pullback.fst c (specMap R A))) (gMap c A) w₀ := by
    refine sq0.of_iso (Iso.refl _) (asIso (pullback.fst (baseChange R c A) (𝟙 _))).symm (Iso.refl _)
      (asIso (pullback.fst c (𝟙 _))).symm ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, pullback.lift_fst]
    · simp
    · rw [Iso.symm_hom, asIso_inv, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc,
        IsIso.comp_inv_eq, gMap_fst]
    · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, pullback.lift_fst]
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← sq1.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end Compat

end AlgebraicGeometry.RelPicard.N12
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry.RelPicard.N12"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block.AlgebraicGeometry.RelPicard.N12"

open AlgebraicGeometry.RelPicard.N12 in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1.base ⊆ (U : Set C))
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]
    (B₀ : Type u) [CommRing B₀] [Algebra R B₀] [Module.Finite R B₀] [Algebra.Etale R B₀]
    (d : ℕ) (φ₀ : TensorProduct R A B₀ ≃ₐ[A] (Fin d → A))
    (z₀ : Spec (CommRingCat.of B₀) ⟶ C) [IsClosedImmersion z₀]
    (hz₀ : z₀ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B₀)))
    (hz₀U : Set.range z₀.base ⊆ (U : Set C))
    (r r' ρ : ℕ) (hρ : ρ = r + r' * d) :
    ∃ (zA : Spec (CommRingCat.of (TensorProduct R A B₀)) ⟶ pullback (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))))
      (_ : IsClosedImmersion zA)
      (_ : zA ≫ pullback.fst (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) ≫ pullback.fst c (specMap R A) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B₀)).toRingHom) ≫ z₀)
      (_ : zA ≫ pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) =
        Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A B₀))))
      (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R))))
      (E' : RelEffCartierDiv (baseChange R c A) ρ (𝟙 (Spec (CommRingCat.of A)))),
      E.SupportedIn U ∧ E'.SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) ∧
      E.I = (sectionIdeal c ε (𝟙 (Spec (CommRingCat.of R)))) ^ r *
        ((pullback.lift z₀ (Spec.map (CommRingCat.ofHom (algebraMap R B₀))) (by rw [Category.comp_id]; exact hz₀)).ker) ^ r' ∧
      E'.I = (sectionIdeal (baseChange R c A) (sectionBaseChange A ε) (𝟙 (Spec (CommRingCat.of A)))) ^ r * zA.ker ^ r' ∧
      (∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of A)), ((E'.pullbackAlong t (Category.comp_id t)).I).IsInvertible) ∧
      (∀ ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of A)} {t' : T' ⟶ Spec (CommRingCat.of A)} (ψ : SchemeHomOver t' t),
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c A) ψ)).obj
          (E'.pullbackAlong t (Category.comp_id t)).lineBundle ≅ (E'.pullbackAlong t' (Category.comp_id t')).lineBundle)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (sΩ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A))
        (φ : pullback (baseChange R c A) sΩ ≅ pullback c (sΩ ≫ specMap R A)),
        φ.hom ≫ pullback.fst c (sΩ ≫ specMap R A) =
          pullback.fst (baseChange R c A) sΩ ≫ pullback.fst c (specMap R A) →
        Nonempty ((Scheme.Modules.pullback φ.hom).obj
            (E.pullbackAlong (sΩ ≫ specMap R A) (Category.comp_id _)).lineBundle ≅
          (E'.pullbackAlong sΩ (Category.comp_id sΩ)).lineBundle)) := by

  haveI : IsSeparated (baseChange R c A) := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) :=
    smoothOfRelativeDimension_one_preimage_ι_comp_snd c U (specMap R A)

  let i2 : pullback (specMap R A) (z₀ ≫ c) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R B₀))) :=
    pullback.congrHom rfl hz₀
  let e : Spec (CommRingCat.of (TensorProduct R A B₀)) ≅ pullback z₀ (pullback.fst c (specMap R A)) :=
    (pullbackSpecIso R A B₀).symm ≪≫ i2.symm ≪≫ (pullbackSymmetry (z₀ ≫ c) (specMap R A)).symm ≪≫
      (pullbackRightPullbackFstIso c (specMap R A) z₀).symm
  let x : Spec (CommRingCat.of (TensorProduct R A B₀)) ⟶ pullback c (specMap R A) :=
    e.hom ≫ pullback.snd z₀ (pullback.fst c (specMap R A))
  have hxe : x = e.hom ≫ pullback.snd z₀ (pullback.fst c (specMap R A)) := rfl
  haveI : IsClosedImmersion (pullback.snd z₀ (pullback.fst c (specMap R A))) :=
    MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance
  haveI hxci : IsClosedImmersion x := inferInstance
  have hx_fst : x ≫ pullback.fst c (specMap R A) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B₀)).toRingHom) ≫ z₀ := by
    simp only [x, e, i2, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc, pullbackSymmetry_inv_comp_fst_assoc,
      pullback.congrHom_inv, pullback.lift_snd_assoc, Category.comp_id, pullbackSpecIso_inv_snd_assoc]
    rfl
  have hx_snd : x ≫ baseChange R c A = Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A B₀))) := by
    simp only [x, e, i2, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [show baseChange R c A = pullback.snd c (specMap R A) from rfl, pullbackRightPullbackFstIso_inv_snd_snd,
      pullbackSymmetry_inv_comp_snd, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id,
      pullbackSpecIso_inv_fst']
  let zA : Spec (CommRingCat.of (TensorProduct R A B₀)) ⟶ pullback (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) :=
    pullback.lift x (Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A B₀)))) (by rw [Category.comp_id]; exact hx_snd)
  have hzA_fst : zA ≫ pullback.fst (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) = x := pullback.lift_fst _ _ _
  have hzAci : IsClosedImmersion zA := by
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion zA
      (pullback.fst (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))), hzA_fst]
    exact hxci
  have hzA1 : zA ≫ pullback.fst (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) ≫ pullback.fst c (specMap R A) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B₀)).toRingHom) ≫ z₀ := by
    rw [← Category.assoc, hzA_fst, hx_fst]
  have hzA2 : zA ≫ pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A B₀))) := pullback.lift_snd _ _ _

  obtain ⟨Zblk, hZI, hZU⟩ := RelEffCartierDiv.exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
    R c U A B₀ d φ₀ z₀ hz₀ hz₀U
  obtain ⟨E₀, hE₀U, hE₀I⟩ := exists_sectionIdeal_pow_mul_pow c U ε hεU Zblk hZU r r'

  have hεAU : Set.range (sectionBaseChange A ε).1.base ⊆
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Set ↥(pullback c (specMap R A))) :=
    range_subset_preimage_of_comp_eq _ _ _ _ (sectionBaseChange_coe_fst A ε) U hεU
  have hxU : Set.range x.base ⊆
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Set ↥(pullback c (specMap R A))) :=
    range_subset_preimage_of_comp_eq _ _ _ _ hx_fst U hz₀U
  obtain ⟨Zblk', hZ'I, hZ'U⟩ := RelEffCartierDiv.exists_I_eq_ker_lift_and_supportedIn_of_finite_etale
    A (baseChange R c A) (pullback.fst c (specMap R A) ⁻¹ᵁ U) A (TensorProduct R A B₀) d
    ((Algebra.TensorProduct.lid A (TensorProduct R A B₀)).trans φ₀) x hx_snd hxU
  have hZ'I' : Zblk'.I = zA.ker := hZ'I
  obtain ⟨E₀', hE₀'U, hE₀'I⟩ := exists_sectionIdeal_pow_mul_pow (baseChange R c A) (pullback.fst c (specMap R A) ⁻¹ᵁ U)
    (sectionBaseChange A ε) hεAU Zblk' hZ'U r r'

  refine ⟨zA, hzAci, hzA1, hzA2, castDeg hρ.symm E₀, castDeg hρ.symm E₀', castDeg_supportedIn _ _ hE₀U,
    castDeg_supportedIn _ _ hE₀'U, ?_, ?_, ?_, ?_, ?_⟩
  · rw [castDeg_I, hE₀I, hZI]
  · rw [castDeg_I, hE₀'I, hZ'I']
  ·
    intro T t
    exact RelEffCartierDiv.isInvertible_I_of_supportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U) _
      ((castDeg_supportedIn _ _ hE₀'U).pullbackAlong t _)
  ·
    intro T T' t t' ψ
    exact RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn A (baseChange R c A)
      (pullback.fst c (specMap R A) ⁻¹ᵁ U) (castDeg hρ.symm E₀') (castDeg_supportedIn _ _ hE₀'U) ψ
  ·
    have fibreCompat : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (sΩ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A))
        (φ : pullback (baseChange R c A) sΩ ≅ pullback c (sΩ ≫ specMap R A)),
        φ.hom ≫ pullback.fst c (sΩ ≫ specMap R A) =
          pullback.fst (baseChange R c A) sΩ ≫ pullback.fst c (specMap R A) →
        Nonempty ((Scheme.Modules.pullback φ.hom).obj
            ((castDeg hρ.symm E₀).pullbackAlong (sΩ ≫ specMap R A) (Category.comp_id _)).lineBundle ≅
          ((castDeg hρ.symm E₀').pullbackAlong sΩ (Category.comp_id sΩ)).lineBundle) := by
      intro Ω _ _ sΩ φ hφ

      have hinv : ((castDeg hρ.symm E₀).pullbackAlong (sΩ ≫ specMap R A) (Category.comp_id _)).I.IsInvertible :=
        RelEffCartierDiv.isInvertible_I_of_supportedIn U _ ((castDeg_supportedIn _ _ hE₀U).pullbackAlong _ _)

      obtain ⟨eT⟩ := hinv.nonempty_pullback_invModule_iso φ.hom (hinv.comap_of_isOpenImmersion φ.hom)

      have hE'g : E₀'.I = E₀.I.comap (gMap c A) := by
        rw [hE₀'I, hZ'I', hE₀I, hZI, Scheme.IdealSheafData.comap_mul, comap_pow, comap_pow, comap_gMap_sectionIdeal,
          ker_lift_eq_comap_gMap_ker_lift c A z₀ hz₀ e x hxe hx_snd]

      have hsq : φ.hom ≫ mapOnProdOver c (sΩ ≫ specMap R A) (Category.comp_id _) =
          mapOnProdOver (baseChange R c A) sΩ (Category.comp_id sΩ) ≫ gMap c A := by
        apply pullback.hom_ext
        · rw [Category.assoc, mapOnProdOver_fst, hφ, Category.assoc, gMap_fst, mapOnProdOver_fst_assoc]
        · rw [snd_eq_fst_comp, ← Category.assoc, ← Category.assoc, Category.assoc φ.hom, mapOnProdOver_fst, hφ,
            Category.assoc (mapOnProdOver _ _ _), gMap_fst, mapOnProdOver_fst_assoc]
      have key : ((castDeg hρ.symm E₀).pullbackAlong (sΩ ≫ specMap R A) (Category.comp_id _)).I.comap φ.hom =
          ((castDeg hρ.symm E₀').pullbackAlong sΩ (Category.comp_id sΩ)).I := by
        change (E₀.I.comap (mapOnProdOver c (sΩ ≫ specMap R A) (Category.comp_id _))).comap φ.hom =
          E₀'.I.comap (mapOnProdOver (baseChange R c A) sΩ (Category.comp_id sΩ))
        rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp, hE'g]
      exact ⟨eT ≪≫ eqToIso (by rw [key])⟩
    exact fibreCompat

end S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_polarisation_pair_of_block (solution)
