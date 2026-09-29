-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/55e541fd-85e0-528b-829e-9bf61cd8245a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_FGSubalgebra
import Theorems.Thm_AlgebraicGeometry_FGSubalgebra_nonempty_isLimit_specCone
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relPicardPresheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.AffineLimit"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage IsProper Scheme.Hom exists_map_eq_top LocallyOfFiniteType Spec Spec.map Scheme Flat Spec.preimage HasRingHomProperty.Spec_iff Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules HasRingHomProperty geometrically Scheme.Modules.pullbackComp Scheme.Hom.id_preimage AffineLimit.IsLFPSurj Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap FGSubalgebra FGSubalgebra.specDiagram FGSubalgebra.specCone FGSubalgebra.nonempty_isLimit_specCone Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle relPicardPresheaf fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso FibrewiseAlgEquivZero.pullback algEquivZeroCut relSubPicPresheaf fibreModule isLFPSurj_relPicardPresheaf"
namespace LfpPicSurj
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R]

theorem twoAffineOpenCover_ext {X : Scheme.{u}} {𝒱 𝒲 : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒲.U0) (h1 : 𝒱.U1 = 𝒲.U1) : 𝒱 = 𝒲 := by
  obtain ⟨U0, U1, p1, p2, p3, p4⟩ := 𝒱
  obtain ⟨U0', U1', q1, q2, q3, q4⟩ := 𝒲
  change U0 = U0' at h0
  change U1 = U1' at h1
  subst h0
  subst h1
  rfl

theorem finrank_sectionsOf_eq_of_iso {S : Type u} [CommRing S] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of S))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank S (𝒱.sectionsOf x M).H0 = Module.finrank S (𝒱.sectionsOf x M').H0 ∧
      Module.finrank S (𝒱.sectionsOf x M).H1 = Module.finrank S (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱', hU0, hU1, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
    (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  have h𝒱 : 𝒱' = 𝒱 := twoAffineOpenCover_ext (hU0.trans (Scheme.Hom.id_preimage _)) (hU1.trans (Scheme.Hom.id_preimage _))
  subst h𝒱
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

lemma locallyOfFiniteType_Spec_algebraMap (A₀ : Type u) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
  exact RingHom.finiteType_algebraMap.mpr ‹_›

lemma specOverOfSubalgebra_comp_specOverOfLE {A : Type u} [CommRing A] [Algebra R A] (A₀ A₁ : Subalgebra R A)
    (h : A₀ ≤ A₁) : specOverOfSubalgebra R A₁ ≫ specOverOfLE R A₀ A₁ h = specOverOfSubalgebra R A₀ := by
  ext : 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

lemma exists_geometricPoint (A : Type u) [CommRing A] (P : Spec (CommRingCat.of A)) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      Set.range ⇑s ⊆ {P} := by
  refine ⟨AlgebraicClosure P.asIdeal.ResidueField, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom ((algebraMap P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField)).comp
      (algebraMap A P.asIdeal.ResidueField))), ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
  rw [Set.mem_singleton_iff]
  apply PrimeSpectrum.ext
  change Ideal.comap _ (IsLocalRing.maximalIdeal _) = P.asIdeal
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, CommRingCat.hom_ofHom, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap P.asIdeal.ResidueField _).injective,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

theorem exists_algebra_eq_specMap_comp_specMap {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A) {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) (hs : s (IsLocalRing.closedPoint k) = 𝔭) :
    ∃ (_ : Algebra 𝔭.asIdeal.ResidueField k),
      s = Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField k ≫
        Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField := by
  obtain ⟨φ, rfl⟩ : ∃ φ : A →+* k, Spec.map (CommRingCat.ofHom φ) = s :=
    ⟨(Spec.preimage s).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hker : 𝔭.asIdeal = RingHom.ker φ := by
    rw [← hs]
    change Ideal.comap φ (IsLocalRing.maximalIdeal k) = RingHom.ker φ
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hunit : 𝔭.asIdeal.primeCompl ≤ Submonoid.comap φ (IsUnit.submonoid k) := fun a ha => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun h0 => ha (show a ∈ 𝔭.asIdeal by rw [hker]; exact RingHom.mem_ker.mpr h0)
  let ψ : 𝔭.asIdeal.ResidueField →+* k := Ideal.ResidueField.lift 𝔭.asIdeal φ hker.le hunit
  letI : Algebra 𝔭.asIdeal.ResidueField k := ψ.toAlgebra
  have hcomp : (algebraMap 𝔭.asIdeal.ResidueField k).comp (algebraMap A 𝔭.asIdeal.ResidueField) = φ := by
    ext a
    exact Ideal.ResidueField.lift_algebraMap 𝔭.asIdeal φ hker.le hunit a
  refine ⟨ψ.toAlgebra, ?_⟩
  rw [Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hcomp]

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem isAlgEquivZero_fibre_pullbackAlong {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t)
    {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
    (h : IsAlgEquivZero (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) M.L)) :
    IsAlgEquivZero (fibreAt c t' s') (fibreModule c t' s' (M.pullbackAlong ψ).L) := by
  have hψ : pullback.snd c t' ≫ ψ.1 = baseChangeSnd c ψ ≫ pullback.snd c t := by
    simp only [baseChangeSnd, pullback.lift_snd]
  let e : Limits.pullback (pullback.snd c t') s' ⟶ Limits.pullback (pullback.snd c t) (s' ≫ ψ.1) :=
    pullback.map _ _ _ _ (baseChangeSnd c ψ) (𝟙 _) ψ.1 hψ (by simp)
  have he : e ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) (s' ≫ ψ.1) =
      pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ (h.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

theorem isAlgEquivZero_fibre_of_pullbackAlong {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t)
    {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
    (h : IsAlgEquivZero (fibreAt c t' s') (fibreModule c t' s' (M.pullbackAlong ψ).L)) :
    IsAlgEquivZero (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) M.L) := by

  have hbc : IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c t)
    rw [show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _), ψ.2]
    exact IsPullback.of_hasPullback c t'

  have hP : IsPullback (pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ) (pullback.snd (pullback.snd c t') s')
      (pullback.snd c t) (s' ≫ ψ.1) :=
    (IsPullback.of_hasPullback (pullback.snd c t') s').paste_horiz hbc
  let e := hP.isoPullback.inv
  have he : e ≫ fibreAt c t' s' = fibreAt c t (s' ≫ ψ.1) := hP.isoPullback_inv_snd
  refine IsAlgEquivZero.of_iso ?_ (h.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact hP.isoPullback_inv_fst)).app M.L

theorem exists_fg_preimage_eq_top {A : Type u} [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (hA₀ : A₀.FG)
    (W : (Spec (CommRingCat.of ↥A₀)).Opens) (hW : Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ⁻¹ᵁ W = ⊤) :
    ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (hle : A₀ ≤ A₁),
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) ⁻¹ᵁ W = ⊤ := by
  obtain ⟨hc⟩ := FGSubalgebra.nonempty_isLimit_specCone R A
  obtain ⟨j, f, hf⟩ := exists_map_eq_top (FGSubalgebra.specDiagram R A) (FGSubalgebra.specCone R A) hc
    (i := op ⟨A₀, hA₀⟩) W hW
  exact ⟨j.unop.1, j.unop.2, f.unop.le, hf⟩

end AlgebraicGeometry.RelPicard.LfpPicSurj

open AlgebraicGeometry.RelPicard.LfpPicSurj in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hopen : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t),
      IsOpen {x : T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)})
    (hpt : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t) (x : T)
      {k₁ : Type u} [Field k₁] [IsAlgClosed k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ T),
      Set.range ⇑s₁ ⊆ {x} → IsAlgEquivZero (fibreAt c t s₁) (fibreModule c t s₁ L.L) →
      ∀ {k₂ : Type u} [Field k₂] [IsAlgClosed k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ T),
      Set.range ⇑s₂ ⊆ {x} → IsAlgEquivZero (fibreAt c t s₂) (fibreModule c t s₂ L.L)) :
    IsLFPSurj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  classical
  intro A _ _ x

  obtain ⟨A₀, hA₀, y₀, hy₀⟩ := isLFPSurj_relPicardPresheaf R 𝒱 c ε A x.1
  obtain ⟨L₀, rfl⟩ := Quotient.exists_rep y₀
  haveI : Algebra.FiniteType R ↥A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀))) :=
    locallyOfFiniteType_Spec_algebraMap ↥A₀
  haveI : LocallyOfFiniteType (unop (op (specOver R ↥A₀))).hom := locallyOfFiniteType_Spec_algebraMap ↥A₀

  have hx2 : FibrewiseAlgEquivZero (L₀.pullbackAlong ⟨(specOverOfSubalgebra R A₀).left, Over.w _⟩) := by
    have h2 := x.2
    rw [← hy₀] at h2
    exact h2

  let W : (Spec (CommRingCat.of ↥A₀)).Opens :=
    ⟨{P | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↥A₀)),
        Set.range ⇑s ⊆ {P} → IsAlgEquivZero (fibreAt c _ s)
          (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀))) s L₀.L)},
      hopen _ L₀⟩

  have himg : Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ⁻¹ᵁ W = ⊤ := by
    refine top_le_iff.mp fun Q _ => ?_
    obtain ⟨k, _, _, s, hs⟩ := exists_geometricPoint A Q
    intro k' _ _ s' hs'
    refine hpt _ L₀ _ (s ≫ Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) ?_ ?_ s' hs'
    · rintro _ ⟨p, rfl⟩
      exact congrArg (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) (hs ⟨p, rfl⟩)
    · exact isAlgEquivZero_fibre_of_pullbackAlong c ε ⟨(specOverOfSubalgebra R A₀).left, Over.w _⟩ L₀ s (hx2 k s)

  obtain ⟨A₁, hA₁, hle, hW⟩ := exists_fg_preimage_eq_top A₀ hA₀ W himg

  refine ⟨A₁, hA₁, ⟨(relPicardPresheaf c ε).map (specOverOfLE R A₀ A₁ hle).op (Quotient.mk _ L₀), ?_⟩, ?_⟩
  · show FibrewiseAlgEquivZero (L₀.pullbackAlong ⟨(specOverOfLE R A₀ A₁ hle).left, Over.w _⟩)
    intro k _ _ s₁
    have hP : (specOverOfLE R A₀ A₁ hle).left (s₁ (IsLocalRing.closedPoint k)) ∈ W := by
      have : s₁ (IsLocalRing.closedPoint k) ∈ (⊤ : (Spec (CommRingCat.of ↥A₁)).Opens) := trivial
      rwa [← hW] at this
    refine isAlgEquivZero_fibre_pullbackAlong c ε _ L₀ s₁ (hP k (s₁ ≫ (specOverOfLE R A₀ A₁ hle).left) ?_)
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rfl
  · apply Subtype.ext
    change (relPicardPresheaf c ε).map (specOverOfSubalgebra R A₁).op
        ((relPicardPresheaf c ε).map (specOverOfLE R A₀ A₁ hle).op (Quotient.mk _ L₀)) = x.1
    rw [← types_comp_apply _ ((relPicardPresheaf c ε).map _), ← Functor.map_comp, ← op_comp,
      specOverOfSubalgebra_comp_specOverOfLE]
    exact hy₀

end S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero (solution)
