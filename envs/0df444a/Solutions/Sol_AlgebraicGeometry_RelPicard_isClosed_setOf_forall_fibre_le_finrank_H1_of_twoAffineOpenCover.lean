-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/adb42e5f-75c9-5d8b-9192-891fcd9da02b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange
import Theorems.Thm_TwoChartCech_isLocallyConstant_fibreEulerChar
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover.AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"

noncomputable section
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsProper Scheme.Modules.pullback LocallyOfFiniteType Spec Scheme IsOpenImmersion Flat IsSeparated IsAffineOpen Scheme.Modules Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.isScalarTower_sections OModulePresheaf Scheme.TwoAffineOpenCover.flat_sections_of_flat Scheme.Modules.projective_sections_of_locallyTrivial OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom Scheme.TwoAffineOpenCover.finiteType_algebraOfHom"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "fibreAt fibreModule exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField"
namespace H1UpperSemicontinuous
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem flat_prod {S : Type*} [CommRing S] (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module S N] [Module.Flat S M] [Module.Flat S N] : Module.Flat S (M × N) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have hM := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat S M)) I
  have hN := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat S N)) I
  have key' : ∀ (p : M × N) (i : I), TensorProduct.prodLeft S S M N S (LinearMap.lTensor (M × N) I.subtype (p ⊗ₜ i)) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft S S M N I (p ⊗ₜ i)) := by
    intro p i
    obtain ⟨m, n⟩ := p
    simp [TensorProduct.prodLeft_tmul, LinearMap.lTensor_tmul]
  have key : ∀ x, TensorProduct.prodLeft S S M N S (LinearMap.lTensor (M × N) I.subtype x) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft S S M N I x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul p i => exact key' p i
  intro x y hxy
  apply (TensorProduct.prodLeft S S M N I).injective
  have hxy' := congrArg (TensorProduct.prodLeft S S M N S) hxy
  rw [key, key] at hxy'
  have h1 := congrArg Prod.fst hxy'
  have h2 := congrArg Prod.snd hxy'
  simp only [LinearMap.prodMap_apply] at h1 h2
  exact Prod.ext (hM h1) (hN h2)

theorem isClosed_setOf_le_finrank_coker_cechDiff_baseChange
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of A))
    [IsProper π] [Flat π] (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum A | n ≤ Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf π M).M01) ⧸
        LinearMap.range ((𝒱.sectionsOf π M).cechDiff.baseChange 𝔭.asIdeal.ResidueField))} := by
  have flatOf : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
      Module.Flat A Γ(M, U) := by
    intro U hU
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections π M U
    haveI : Module.Flat A Γ(X, U) := Scheme.TwoAffineOpenCover.flat_sections_of_flat π U hU
    haveI : Module.Projective Γ(X, U) Γ(M, U) :=
      Scheme.Modules.projective_sections_of_locallyTrivial _ hM.1 ⟨U, hU⟩
    exact Module.Flat.trans A Γ(X, U) Γ(M, U)
  haveI : Module.Flat A (𝒱.sectionsOf π M).M0 := flatOf _ 𝒱.isAffineOpen_U0
  haveI : Module.Flat A (𝒱.sectionsOf π M).M1 := flatOf _ 𝒱.isAffineOpen_U1
  haveI : Module.Flat A (𝒱.sectionsOf π M).M01 := flatOf _ 𝒱.isAffineOpen_inf
  haveI : Module.Flat A ((𝒱.sectionsOf π M).M0 × (𝒱.sectionsOf π M).M1) := flat_prod _ _
  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial π M hM.1 𝒱.toOrderedAffineCover
  obtain ⟨hfin0, hfin1⟩ := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf
  haveI : Module.Finite A (LinearMap.ker (𝒱.sectionsOf π M).cechDiff) := hfin0
  haveI : Module.Finite A ((𝒱.sectionsOf π M).M01 ⧸ LinearMap.range (𝒱.sectionsOf π M).cechDiff) := hfin1
  set d := (𝒱.sectionsOf π M).cechDiff with hd

  let kr : PrimeSpectrum A → ℕ := fun 𝔭 => Module.finrank 𝔭.asIdeal.ResidueField
    (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField))
  let ck : PrimeSpectrum A → ℕ := fun 𝔭 => Module.finrank 𝔭.asIdeal.ResidueField
    ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf π M).M01) ⧸ LinearMap.range (d.baseChange 𝔭.asIdeal.ResidueField))
  let χ : PrimeSpectrum A → ℤ := fun 𝔭 => (kr 𝔭 : ℤ) - ck 𝔭
  have hχ : IsLocallyConstant χ := TwoChartCech.isLocallyConstant_fibreEulerChar d
  have hker : ∀ m : ℕ, IsClosed {𝔭 : PrimeSpectrum A | m ≤ kr 𝔭} := fun m => by
    have h := TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange d (𝟙 (Spec (CommRingCat.of A))) m
    first
      | simpa using h
      | (have h' := h; simp at h' ⊢; exact h')
      | (have h' := h; simp at h'; exact h')
      | exact h

  have hset : {𝔭 : PrimeSpectrum A | n ≤ ck 𝔭} =
      ⋃ e ∈ Set.range χ, (χ ⁻¹' {e} ∩ {𝔭 | Int.toNat ((n : ℤ) + e) ≤ kr 𝔭}) := by
    ext 𝔭
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_range, exists_prop]
    constructor
    · intro h
      refine ⟨χ 𝔭, ⟨𝔭, rfl⟩, rfl, ?_⟩
      rw [Int.toNat_le]
      simp only [χ]
      omega
    · rintro ⟨e, -, he, hle⟩
      rw [Int.toNat_le] at hle
      have : e = (kr 𝔭 : ℤ) - ck 𝔭 := he.symm
      omega
  change IsClosed {𝔭 : PrimeSpectrum A | n ≤ ck 𝔭}
  rw [hset]
  refine Set.Finite.isClosed_biUnion hχ.range_finite (fun e _ => ?_)
  exact (hχ.isClosed_fiber e).inter (hker _)

theorem specMap_residueField_base {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A) :
    (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base
      (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField) = 𝔭 := by
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap (algebraMap A 𝔭.asIdeal.ResidueField)
    (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField)).asIdeal = 𝔭.asIdeal
  rw [PrimeSpectrum.comap_asIdeal]
  have hbot : (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField).asIdeal = ⊥ := by
    change IsLocalRing.maximalIdeal _ = ⊥
    exact IsLocalRing.maximalIdeal_eq_bot
  rw [hbot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

theorem finrank_H1_sectionsOf_eq {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsSeparated x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒲 𝒲' : X.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf x M).H1 = Module.finrank k (𝒲'.sectionsOf x M).H1 := by
  obtain ⟨e⟩ := Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated x M hM.1 𝒲 𝒲'
  exact e.finrank_eq

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    IsClosed {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          n ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} := by
  classical
  haveI : IsSeparated c := inferInstance
  have hsep : ∀ {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T), IsSeparated (fibreAt c t s) := by
    intro k _ s
    change IsSeparated (pullback.snd (pullback.snd c t) s)
    infer_instance

  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hx

  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show x ∈ (⊤ : T.Opens) from trivial)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  haveI : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  haveI : IsNoetherianRing Γ(T, W) := Algebra.FiniteType.isNoetherianRing R _
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  set πA := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) with hπA
  haveI : IsProper πA := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : Flat πA := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  let 𝒱A := 𝒱.pullback c Γ(T, W)

  let h1 : PrimeSpectrum Γ(T, W) → ℕ := fun 𝔭 =>
    Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[Γ(T, W)] (𝒱A.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).M01) ⧸
        LinearMap.range ((𝒱A.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
          𝔭.asIdeal.ResidueField))
  have hVclosed : IsClosed {𝔭 : PrimeSpectrum Γ(T, W) | n ≤ h1 𝔭} :=
    isClosed_setOf_le_finrank_coker_cechDiff_baseChange πA 𝒱A _ (hM.pullback g') n

  have htrace : ∀ 𝔭 : PrimeSpectrum Γ(T, W),
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
        s.base (IsLocalRing.closedPoint k) = hW.fromSpec.base 𝔭 →
          ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
            n ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) ↔ n ≤ h1 𝔭 := by
    intro 𝔭
    constructor
    · intro h

      let s₀ := Scheme.TwoAffineOpenCover.specMap Γ(T, W) 𝔭.asIdeal.ResidueField ≫ hW.fromSpec
      have hs₀ : s₀.base (IsLocalRing.closedPoint _) = hW.fromSpec.base 𝔭 := by
        change hW.fromSpec.base ((Scheme.TwoAffineOpenCover.specMap Γ(T, W) 𝔭.asIdeal.ResidueField).base
          (IsLocalRing.closedPoint _)) = hW.fromSpec.base 𝔭
        rw [specMap_residueField_base]
      obtain ⟨𝒲, h𝒲⟩ := exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
        c t hW.fromSpec πA g' hcart 𝒱A 𝔭 s₀ hs₀
      have := h _ s₀ hs₀ 𝒲
      rwa [(h𝒲 M hM).2] at this
    · intro h k _ s hs 𝒲
      obtain ⟨𝒲₀, h𝒲₀⟩ := exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
        c t hW.fromSpec πA g' hcart 𝒱A 𝔭 s hs
      haveI := hsep s
      rw [finrank_H1_sectionsOf_eq (fibreAt c t s) (fibreModule c t s M) (hM.pullback _) 𝒲 𝒲₀, (h𝒲₀ M hM).2]
      exact h

  refine ⟨hW.fromSpec.base '' {𝔭 | n ≤ h1 𝔭}ᶜ, ?_, ?_, ?_⟩
  · rintro y ⟨𝔭, h𝔭, rfl⟩
    rw [Set.mem_compl_iff, Set.mem_setOf_eq]
    intro hy
    exact h𝔭 ((htrace 𝔭).mp hy)
  · exact hW.fromSpec.isOpenEmbedding.isOpenMap _ hVclosed.isOpen_compl
  · have hxr : x ∈ Set.range hW.fromSpec.base := by rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔭, rfl⟩ := hxr
    refine ⟨𝔭, ?_, rfl⟩
    rw [Set.mem_compl_iff, Set.mem_setOf_eq]
    intro h𝔭
    exact hx ((htrace 𝔭).mpr h𝔭)

end AlgebraicGeometry.RelPicard.H1UpperSemicontinuous
end

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    IsClosed {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          n ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} :=
  AlgebraicGeometry.RelPicard.H1UpperSemicontinuous.main R c 𝒱 t M hM n

end S_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover (solution)
