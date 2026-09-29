-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e29dc60a-71f7-5ef5-84f4-12c9ad9af76b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"

noncomputable section

namespace OpenCutTwoStrata

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem finrank_H0_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 ∧
      Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

theorem specMap_residueField_base {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A) (p : Spec (CommRingCat.of 𝔭.asIdeal.ResidueField)) :
    (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base p = 𝔭 := by
  apply PrimeSpectrum.ext
  have hp : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right p.isPrime.ne_top
  change Ideal.comap (algebraMap A 𝔭.asIdeal.ResidueField) p.asIdeal = 𝔭.asIdeal
  rw [hp, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end OpenCutTwoStrata

end

open OpenCutTwoStrata in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (Z₀ : Set ↥(Spec (CommRingCat.of R))) (hZ₀ : IsClosed Z₀)
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t) (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L) →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 : ℤ) -
              Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H1 =
            (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 : ℤ) -
              Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1)
    (hoff : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t) (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      t (s (IsLocalRing.closedPoint k)) ∉ Z₀ →
      ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
        (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H1 =
          (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1 →
        IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L))
    (hZ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), ∃ U : Set T, IsOpen U ∧
        U ∩ (⇑t) ⁻¹' Z₀ = {x : T | t x ∈ Z₀ ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
          Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)}) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t),
      IsOpen {x : T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} := by
  intro T t _ L
  classical
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t

  have chi_unit : ∀ {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s)
          (SheafOfModules.unit (pullback (pullback.snd c t) s).ringCatSheaf : (pullback (pullback.snd c t) s).Modules)).H0 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s)
          (SheafOfModules.unit (pullback (pullback.snd c t) s).ringCatSheaf : (pullback (pullback.snd c t) s).Modules)).H1 :=
    fun s 𝒲 => finrank_H0_H1_congr (fibreAt c t s) 𝒲
      (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c t) s))
  rw [isOpen_iff_forall_mem_open]
  intro x hx

  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := (⊤ : T.Opens)) trivial
  haveI : IsNoetherianRing Γ(T, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : Algebra R Γ(T, W) := Scheme.TwoAffineOpenCover.algebraOfHom t W
  set A : Type u := Γ(T, W) with hA
  set j : Spec (CommRingCat.of A) ⟶ T := hW.fromSpec with hjdef
  have hj : j ≫ t = Scheme.TwoAffineOpenCover.specMap R A := by
    have e1 : CommRingCat.ofHom (algebraMap R A) = (Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top := rfl
    rw [hjdef, Scheme.TwoAffineOpenCover.specMap, e1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
      ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW]

  set CA := pullback c (Scheme.TwoAffineOpenCover.specMap R A) with hCA
  set πA : CA ⟶ Spec (CommRingCat.of A) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A) with hπA
  set g' : CA ⟶ pullback c t := pullback.map c (Scheme.TwoAffineOpenCover.specMap R A) c t (𝟙 C) j (𝟙 _)
    (by simp) (by rw [Category.comp_id, hj]) with hg'
  have hg'fst : g' ≫ pullback.fst c t = pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A) := by
    rw [hg', pullback.lift_fst, Category.comp_id]
  have hg'snd : g' ≫ pullback.snd c t = πA ≫ j := by
    rw [hg', pullback.lift_snd]
  have hcart : IsPullback g' πA (pullback.snd c t) j := by
    refine IsPullback.of_right ?_ hg'snd (IsPullback.of_hasPullback c t)
    rw [hg'fst, hj]
    exact IsPullback.of_hasPullback c (Scheme.TwoAffineOpenCover.specMap R A)
  haveI : IsProper πA := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : Flat πA := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  let 𝒱A : CA.TwoAffineOpenCover := 𝒱.pullback c A

  let d : (pullback c t).Modules → PrimeSpectrum A → ℤ := fun M 𝔭 =>
    (Module.finrank 𝔭.asIdeal.ResidueField
        (LinearMap.ker ((𝒱A.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
          𝔭.asIdeal.ResidueField)) : ℤ) -
      Module.finrank 𝔭.asIdeal.ResidueField
        ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱A.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).M01) ⧸
          LinearMap.range ((𝒱A.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
            𝔭.asIdeal.ResidueField))
  have hdL : IsLocallyConstant (d L.L) :=
    Scheme.TwoAffineOpenCover.isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange πA 𝒱A _
      (L.isInvertible.pullback g')
  have hdO : IsLocallyConstant (d (𝟙_ (pullback c t).Modules)) :=
    Scheme.TwoAffineOpenCover.isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange πA 𝒱A _
      ((Scheme.Modules.isInvertible_unit _).pullback g')
  have hVopen : IsOpen {𝔭 : PrimeSpectrum A | d L.L 𝔭 = d (𝟙_ (pullback c t).Modules) 𝔭} := by
    have := (hdL.comp₂ hdO (· - ·)).isOpen_fiber 0
    simp only [sub_eq_zero] at this
    exact this

  have key : ∀ (𝔭 : PrimeSpectrum A) (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = j.base 𝔭 →
        ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          ((Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 : ℤ) -
              Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H1 =
            (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 : ℤ) -
              Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1 ↔
          d L.L 𝔭 = d (𝟙_ (pullback c t).Modules) 𝔭) := by
    intro 𝔭 k _ s hs
    obtain ⟨𝒲, h𝒲⟩ :=
      exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱A 𝔭 s hs
    obtain ⟨hL0, hL1⟩ := h𝒲 L.L L.isInvertible
    obtain ⟨hO0, hO1⟩ := h𝒲 (𝟙_ _) (Scheme.Modules.isInvertible_unit _)
    refine ⟨𝒲, ?_⟩
    simp only [d]
    rw [hL0, hL1, hO0, hO1]

  set S : Set T := {x : T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} with hSdef
  change x ∈ S at hx
  obtain ⟨U, hUo, hUZ⟩ := hZ t L
  set Z : Set T := (⇑t) ⁻¹' Z₀ with hZdef
  have hZcl : IsClosed Z := hZ₀.preimage t.continuous

  have geom : ∀ 𝔮 : PrimeSpectrum A, ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (sb : Spec (CommRingCat.of K) ⟶ T),
      sb.base (IsLocalRing.closedPoint K) = j.base 𝔮 ∧ Set.range ⇑sb ⊆ {j.base 𝔮} := by
    intro 𝔮
    let K : Type u := AlgebraicClosure 𝔮.asIdeal.ResidueField
    let sb : Spec (CommRingCat.of K) ⟶ T :=
      Scheme.TwoAffineOpenCover.specMap 𝔮.asIdeal.ResidueField K ≫
        Scheme.TwoAffineOpenCover.specMap A 𝔮.asIdeal.ResidueField ≫ j
    have hsb : sb.base (IsLocalRing.closedPoint K) = j.base 𝔮 := by
      change j.base ((Scheme.TwoAffineOpenCover.specMap A 𝔮.asIdeal.ResidueField).base
        ((Scheme.TwoAffineOpenCover.specMap 𝔮.asIdeal.ResidueField K).base (IsLocalRing.closedPoint K))) = j.base 𝔮
      rw [specMap_residueField_base]
    refine ⟨K, inferInstance, inferInstance, sb, hsb, ?_⟩
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint K)]
    exact hsb

  have hxr : x ∈ Set.range ⇑j.base := by
    rw [hjdef]
    change x ∈ Set.range hW.fromSpec
    rw [hW.range_fromSpec]; exact hxW
  obtain ⟨𝔭, rfl⟩ := hxr
  have h𝔭 : d L.L 𝔭 = d (𝟙_ (pullback c t).Modules) 𝔭 := by
    obtain ⟨K, _, _, sb, hsb, hrange⟩ := geom 𝔭
    obtain ⟨𝒲, hiff⟩ := key 𝔭 K sb hsb
    exact hiff.mp (hcut t L K sb (hx K sb hrange) 𝒲)

  refine ⟨(j.base '' {𝔮 : PrimeSpectrum A | d L.L 𝔮 = d (𝟙_ (pullback c t).Modules) 𝔮}) \ (Z ∩ Uᶜ), ?_, ?_, ?_⟩
  ·
    rintro y ⟨⟨𝔮, h𝔮, rfl⟩, hyZU⟩ k _ _ s hs
    by_cases hyZ : j.base 𝔮 ∈ Z
    · have hyU : j.base 𝔮 ∈ U := by
        by_contra h
        exact hyZU ⟨hyZ, h⟩
      have : j.base 𝔮 ∈ U ∩ Z := ⟨hyU, hyZ⟩
      rw [hUZ] at this
      exact this.2 k s hs
    · have hs' : s.base (IsLocalRing.closedPoint k) = j.base 𝔮 := hs ⟨_, rfl⟩
      obtain ⟨𝒲, hiff⟩ := key 𝔮 k s hs'
      refine hoff t L k s ?_ 𝒲 (hiff.mpr h𝔮)
      change t.base (s.base (IsLocalRing.closedPoint k)) ∉ Z₀
      rw [hs']
      exact hyZ
  ·
    exact (j.isOpenEmbedding.isOpenMap _ hVopen).sdiff (hZcl.inter hUo.isClosed_compl)
  ·
    refine ⟨⟨𝔭, h𝔭, rfl⟩, ?_⟩
    rintro ⟨hxZ, hxU⟩
    apply hxU
    have : j.base 𝔭 ∈ U ∩ Z := by
      rw [hUZ]
      exact ⟨hxZ, hx⟩
    exact this.1

end S_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata (solution)
