-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ed54f0c4-7358-5386-bece-8470545871e4

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.IsTensorProduct
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_zeroSchemeIdeal_and_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_supportedIn
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry~Scheme.IdealSheafData.ideal_comap_of_le P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_supportedIn.AlgebraicGeometry TensorProduct nonZeroDivisors"

namespace Algebra
p2m_export "Algebra" "TensorProduct.rid ofId IsPushout TensorProduct.includeRight algebraMap TensorProduct.lTensor_ker QuasiFinite IsPushout.equiv Smooth smul_def TensorProduct.includeLeft id TensorProduct.map"
namespace IsPushout
p2m_export "Algebra.IsPushout" "equiv symm"
p2m_open "Algebra.IsPushout Algebra"

theorem ker_algebraMap_eq_map_ker
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) = (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  let e : B ⊗[R] C ≃ₐ[B] P := Algebra.IsPushout.equiv R B C P

  have h1 : algebraMap B P = e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom := by
    ext b
    simp [e]
  rw [h1, RingHom.ker_comp_of_injective _ e.toRingEquiv.injective]

  let g : R →ₐ[R] C := Algebra.ofId R C
  have h2 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom.comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom := by
    ext b
    simp [g]
  have h3 : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom =
      (RingHom.ker (algebraMap R C)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    have := Algebra.TensorProduct.lTensor_ker (A := B) g hC
    first | simpa [g] using this | (simp [g] at this; exact this) | exact this
  rw [h2, ← RingHom.comap_ker, h3]

  let r : B ⊗[R] R ≃ₐ[R] B := Algebra.TensorProduct.rid R R B
  have h4 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom =
      (r.toRingEquiv.symm : B →+* B ⊗[R] R) := by
    ext b
    apply r.toRingEquiv.injective
    simp [r]
  have h5 : (algebraMap R B) = (r.toRingEquiv : B ⊗[R] R →+* B).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    ext x
    simp [r, Algebra.smul_def]
  rw [h4, h5, ← Ideal.map_map, Ideal.comap_coe, Ideal.map_coe, Ideal.comap_symm]

end Algebra.IsPushout

namespace CommRingCat
p2m_export "CommRingCat" "hom_comp of hom_ext flat ofHom comp_apply Hom isPushout_iff_isPushout"
p2m_open "CommRingCat"

theorem ker_eq_map_ker_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr)
    (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have hw : inl.hom.comp f.hom = inr.hom.comp g.hom := by
    simpa only [CommRingCat.hom_comp] using congr(($(h.w)).hom)
  have : IsScalarTower R C P := .of_algebraMap_eq' hw
  have : Algebra.IsPushout R B C P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.IsPushout.ker_algebraMap_eq_map_ker R B C P hg

end CommRingCat

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.Opens.topIso_inv Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension IsProper Scheme.IdealSheafData.comapIso_inv_subschemeι Scheme.IdealSheafData.comap_comp isPushout_appTop_of_isPullback Scheme.Hom Scheme.Opens.ι_appIso LocallyQuasiFinite IsFinite isAffine_of_isAffineHom Scheme.Pullback.range_fst IsAffine Scheme.preimage_basicOpen Spec Spec.map Scheme Smooth Scheme.Hom.appTop Scheme.Opens.topIso_hom Scheme.Hom.comp_base Flat Scheme.Hom.finrank_of_isPullback isAffineOpen_top Scheme.fromSpecResidueField_apply Scheme.IdealSheafData.ideal_map_of_isAffineHom locallyQuasiFinite_iff_finite_preimage_singleton Scheme.Modules Scheme.Hom.ker_apply Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation Scheme.Hom.resLE_app_top Scheme.Opens.ι_image_top IsAffineHom Scheme.Pullback.exists_preimage_pullback IsFinite.of_isProper_of_locallyQuasiFinite Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.IdealSheafData Scheme.Modules.zeroSchemeIdeal RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Hom.map_appLE fromSpecResidueField Opens.topIso_inv Hom.finrank_comp_left_of_isIso IdealSheafData.support_comap IdealSheafData.comapIso_inv_subschemeι IdealSheafData.comap_comp Hom Γ Opens.ι_appIso topIso_hom Pullback.range_fst preimage_basicOpen Hom.appTop Opens.topIso_hom Hom.comp_base residueField Hom.finrank_of_isPullback affineBasicOpen affineOpens basicOpen fromSpecResidueField_apply IdealSheafData.ideal_map_of_isAffineHom Modules Hom.ker_apply Opens Hom.appLE_map Hom.app_eq_appLE Hom.resLE_app_top Opens.ι_image_top Pullback.exists_preimage_pullback restrict Hom.comp_apply Hom.appLE IdealSheafData Modules.zeroSchemeIdeal Modules.IsInvertible"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "support_comap comapIso_inv_subschemeι comap_comp comapIso map subscheme subschemeι_app_surjective ideal ideal_map_of_isAffineHom subschemeι comap support ker_subschemeι_app ideal_comap_of_isOpenImmersion invModuleSection IsInvertible resLE"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData~ideal_comap_of_le AlgebraicGeometry.Scheme~IdealSheafData.ideal_comap_of_le AlgebraicGeometry~Scheme.IdealSheafData.ideal_comap_of_le"

variable {X Y : Scheme.{u}}

theorem ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f I.subschemeι)
  have := CommRingCat.ker_eq_map_ker_of_isPushout H
    (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top X⟩)
  rw [← ker_subschemeι_app I ⟨⊤, isAffineOpen_top X⟩, comap, Scheme.Hom.ker_apply]
  exact this

set_option backward.isDefEq.respectTransparency false in

theorem ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom := by

  suffices key : ∀ (U' : X.affineOpens) (V' : Y.affineOpens),
      U' = ⟨(U : X.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using U.2⟩ →
      V' = ⟨(V : Y.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using V.2⟩ →
      ∀ (e : (V' : Y.Opens) ≤ f ⁻¹ᵁ (U' : X.Opens)),
        (I.comap f).ideal V' = (I.ideal U').map (f.appLE U' V' e).hom from
    key U V (Subtype.ext (U : X.Opens).ι_image_top.symm)
      (Subtype.ext (V : Y.Opens).ι_image_top.symm) hVU
  rintro _ _ rfl rfl e
  have : IsAffine (U : X.Opens) := U.2
  have : IsAffine (V : Y.Opens) := V.2

  have h := ideal_comap_top (I.comap (U : X.Opens).ι) (f.resLE U V hVU)
  rw [← comap_comp, Scheme.Hom.resLE_comp_ι, comap_comp,
    ideal_comap_of_isOpenImmersion (I.comap f) (V : Y.Opens).ι,
    ideal_comap_of_isOpenImmersion I (U : X.Opens).ι] at h
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at h
  convert h using 2 <;> try rfl
  congr 1
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv, eqToHom_op, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

theorem ideal_comap_of_isAffineHom (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = (I.ideal U).map (f.app U).hom := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ideal_comap_of_le I f U ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ le_rfl

end AlgebraicGeometry.Scheme.IdealSheafData

namespace ZDFlatG

theorem mem_nonZeroDivisors_of_injective {R S F : Type*} [CommRing R] [CommRing S]
    [FunLike F R S] [MulHomClass F R S] [ZeroHomClass F R S] (e : F) (he : Function.Injective e)
    {r : R} (h : e r ∈ nonZeroDivisors S) : r ∈ nonZeroDivisors R := by
  refine mem_nonZeroDivisors_iff_right.mpr fun z hz => he ?_
  rw [map_zero]
  exact (mem_nonZeroDivisors_iff_right.mp h) _ (by rw [← map_mul, hz, map_zero])

end ZDFlatG

namespace ZDHeadG

theorem finite_preimage_singleton_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [Finite P] {z : Z}
    (hz : z ∈ Set.range g.base) : (f.base ⁻¹' {z}).Finite := by
  have hr : Set.range fst.base = f.base ⁻¹' Set.range g.base := by
    rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ,
      Scheme.Pullback.range_fst]
  refine Set.Finite.subset ((Set.finite_range fst.base)) ?_
  rw [hr]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hz)

theorem finite_of_isFinite {P : Scheme.{u}} {k : Type u} [Field k] (p : P ⟶ Spec (CommRingCat.of k))
    [IsFinite p] : Finite P := by
  have h := p.finite_preimage_singleton (IsLocalRing.closedPoint k)
  exact Set.finite_univ_iff.mp (h.subset fun y _ => Subsingleton.elim _ _)

section Square

variable {𝒞 S T W : Scheme.{u}} (f : 𝒞 ⟶ S) (g : T ⟶ S) (x : W ⟶ T)
  (F : pullback f (x ≫ g) ⟶ pullback f g)
  (hF1 : F ≫ pullback.fst f g = pullback.fst f (x ≫ g))
  (hF2 : F ≫ pullback.snd f g = pullback.snd f (x ≫ g) ≫ x)

include hF1 hF2

theorem pullbackLeftPullbackSndIso_hom_comp_eq :
    (pullbackLeftPullbackSndIso f g x).hom ≫ F = pullback.fst (pullback.snd f g) x := by
  apply pullback.hom_ext
  · rw [Category.assoc, hF1, pullbackLeftPullbackSndIso_hom_fst]
  · rw [Category.assoc, hF2, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

theorem isPullback_mapOnProd :
    IsPullback F (pullback.snd f (x ≫ g)) (pullback.snd f g) x := by
  have e := pullbackLeftPullbackSndIso_hom_comp_eq f g x F hF1 hF2
  refine IsPullback.of_iso (IsPullback.of_hasPullback (pullback.snd f g) x)
    (pullbackLeftPullbackSndIso f g x) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, e]
  · rw [Iso.refl_hom, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  · simp
  · simp

theorem isPullback_snd_comap (Z : (pullback f g).IdealSheafData) :
    IsPullback (pullback.snd F Z.subschemeι) (pullback.fst F Z.subschemeι ≫ pullback.snd f (x ≫ g))
      (Z.subschemeι ≫ pullback.snd f g) x :=
  (IsPullback.of_hasPullback F Z.subschemeι).flip.paste_vert (isPullback_mapOnProd f g x F hF1 hF2)

end Square

theorem isInvertible_comap_of_isIso {X Y : Scheme.{u}} {J : Y.IdealSheafData}
    (hJ : J.IsInvertible) (e : X ⟶ Y) [IsIso e] : (J.comap e).IsInvertible := by
  intro x'
  obtain ⟨U, f, hxf, γ, hγ, hJf⟩ := hJ (e.base x')
  let U' : X.affineOpens := ⟨e ⁻¹ᵁ U.1, U.2.preimage e⟩
  let f' : Γ(X, U') := (e.app U.1).hom f
  have hbo : X.basicOpen f' = e ⁻¹ᵁ Y.basicOpen f := (Scheme.preimage_basicOpen e f).symm
  have hle : (X.affineBasicOpen f' : X.Opens) ≤ e ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) := hbo.le
  refine ⟨U', f', ?_, (e.appLE (Y.affineBasicOpen f) (X.affineBasicOpen f') hle).hom γ,
    ?_, ?_⟩
  · change x' ∈ X.basicOpen f'
    rw [hbo]; exact hxf
  ·
    have hiso : IsIso (e.appLE (Y.affineBasicOpen f) (X.affineBasicOpen f') hle) := by
      have heq : (X.affineBasicOpen f' : X.Opens) = e ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) := hbo
      rw [Scheme.Hom.appLE, show homOfLE hle = eqToHom heq from Subsingleton.elim _ _, eqToHom_op]
      infer_instance
    let ε := (asIso (e.appLE (Y.affineBasicOpen f) (X.affineBasicOpen f') hle)).commRingCatIsoToRingEquiv
    refine ZDFlatG.mem_nonZeroDivisors_of_injective ε.symm ε.symm.injective ?_
    change ε.symm (ε γ) ∈ _
    rw [RingEquiv.symm_apply_apply]
    exact hγ
  · rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le J e (Y.affineBasicOpen f)
      (X.affineBasicOpen f') hle, hJf, Ideal.map_span, Set.image_singleton]

end ZDHeadG

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [Flat f] (U : 𝒞.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ f)]
    {T : Scheme.{u}} {g : T ⟶ S} [IsLocallyNoetherian T]
    {M : (pullback f g).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f g).Modules ⟶ M) (r : ℕ)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T),
      ∃ Dx : RelEffCartierDiv f r (x ≫ g),
        Dx.I = (Scheme.Modules.zeroSchemeIdeal s).comap (mapOnProdOver f x rfl) ∧ Dx.SupportedIn U) :
    ∃ D : RelEffCartierDiv f r g,
      D.I = Scheme.Modules.zeroSchemeIdeal s ∧ D.SupportedIn U ∧
        ∃ e : M ≅ D.lineBundle, s ≫ e.hom = D.I.invModuleSection := by

  have geo : ∀ t : T, ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (x : Spec (CommRingCat.of k) ⟶ T) (pt : Spec (CommRingCat.of k)), x.base pt = t := by
    intro t
    let κ : Type u := T.residueField t
    let k : Type u := AlgebraicClosure κ
    exact ⟨k, inferInstance, inferInstance,
      Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ T.fromSpecResidueField t,
      IsLocalRing.closedPoint k,
      (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)⟩

  have hfib' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T),
      ((Scheme.Modules.zeroSchemeIdeal s).comap (pullback.fst (pullback.snd f g) x)).IsInvertible := by
    intro k _ _ x
    obtain ⟨Dx, hDx, hDxU⟩ := hfib k x
    have hinv : ((Scheme.Modules.zeroSchemeIdeal s).comap (mapOnProdOver f x rfl)).IsInvertible :=
      hDx ▸ Dx.isInvertible_I_of_supportedIn U hDxU
    rw [← ZDHeadG.pullbackLeftPullbackSndIso_hom_comp_eq f g x (mapOnProdOver f x rfl)
      (mapOnProdOver_fst f x rfl) (mapOnProdOver_snd f x rfl), Scheme.IdealSheafData.comap_comp]
    exact ZDHeadG.isInvertible_comap_of_isIso hinv _
  obtain ⟨hZinv, hZflat⟩ := hM.isInvertible_zeroSchemeIdeal_and_flat (pullback.snd f g) s hfib'
  haveI := hZflat
  set Z := Scheme.Modules.zeroSchemeIdeal s with hZdef

  haveI : IsProper (Z.subschemeι ≫ pullback.snd f g) := inferInstance
  haveI : LocallyQuasiFinite (Z.subschemeι ≫ pullback.snd f g) := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro t
    obtain ⟨k, _, _, x, pt, hpt⟩ := geo t
    obtain ⟨⟨I, hfin, hflat, hlfp, hrk⟩, hDx, -⟩ := hfib k x
    dsimp only at hDx
    subst hDx
    have h := ZDHeadG.isPullback_snd_comap f g x (mapOnProdOver f x rfl)
      (mapOnProdOver_fst f x rfl) (mapOnProdOver_snd f x rfl) Z
    haveI : Finite (Z.comap (mapOnProdOver f x rfl)).subscheme := ZDHeadG.finite_of_isFinite
      ((Z.comap (mapOnProdOver f x rfl)).subschemeι ≫ pullback.snd f (x ≫ g))
    haveI : Finite ↥(pullback (mapOnProdOver f x rfl) Z.subschemeι) :=
      Finite.of_injective _ (Z.comapIso (mapOnProdOver f x rfl)).inv.injective
    exact ZDHeadG.finite_preimage_singleton_of_isPullback h ⟨pt, hpt⟩
  haveI : IsFinite (Z.subschemeι ≫ pullback.snd f g) := IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : LocallyOfFinitePresentation (Z.subschemeι ≫ pullback.snd f g) := inferInstance

  have hrank : ∀ t : T, (Z.subschemeι ≫ pullback.snd f g).finrank t = r := by
    intro t
    obtain ⟨k, _, _, x, pt, hpt⟩ := geo t
    obtain ⟨⟨I, hfin, hflat, hlfp, hrk⟩, hDx, -⟩ := hfib k x
    dsimp only at hDx
    subst hDx
    haveI := hfin
    haveI := hflat
    have h := ZDHeadG.isPullback_snd_comap f g x (mapOnProdOver f x rfl)
      (mapOnProdOver_fst f x rfl) (mapOnProdOver_snd f x rfl) Z
    rw [← hpt, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ h pt]
    have e : pullback.fst (mapOnProdOver f x rfl) Z.subschemeι ≫ pullback.snd f (x ≫ g) =
        (Z.comapIso (mapOnProdOver f x rfl)).inv ≫
          ((Z.comap (mapOnProdOver f x rfl)).subschemeι ≫ pullback.snd f (x ≫ g)) := by
      rw [← Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι]
    rw [e, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrk pt
  obtain ⟨e, he⟩ := hM.exists_iso_invModule_zeroSchemeIdeal s hZinv

  have hsupp : ∀ z ∈ Z.support, pullback.fst f g z ∈ U := by
    intro z hz
    obtain ⟨k, _, _, x, pt, hpt⟩ := geo (pullback.snd f g z)
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f g) (g := x) z pt hpt.symm
    obtain ⟨Dx, hDx, hDxU⟩ := hfib k x
    have hcomp := ZDHeadG.pullbackLeftPullbackSndIso_hom_comp_eq f g x (mapOnProdOver f x rfl)
      (mapOnProdOver_fst f x rfl) (mapOnProdOver_snd f x rfl)
    set z' := (pullbackLeftPullbackSndIso f g x).hom w with hz'def
    have hFz' : mapOnProdOver f x rfl z' = z := by
      rw [hz'def, ← Scheme.Hom.comp_apply, hcomp, hw1]
    have hz' : z' ∈ (Z.comap (mapOnProdOver f x rfl)).support := by
      rw [Scheme.IdealSheafData.support_comap]
      show mapOnProdOver f x rfl z' ∈ (Z.support : Set _)
      rw [hFz']; exact hz
    rw [← hDx] at hz'
    have hU : pullback.fst f (x ≫ g) z' ∈ U := hDxU hz'
    rwa [← mapOnProdOver_fst f x rfl, Scheme.Hom.comp_apply, hFz'] at hU
  exact ⟨⟨Z, inferInstance, hZflat, inferInstance, hrank⟩, rfl, hsupp, e, he⟩

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_supportedIn (solution)
