-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/39272171-1d2e-5409-9ab4-42b62e79c372

import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isFinite_and_finrank_mul_subscheme_comp_eq_add
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

universe u

namespace GAddSol

open CategoryTheory AlgebraicGeometry

section finiteness

variable {κ : Type u} [Field κ] {X : Scheme.{u}} (f : X ⟶ Spec (.of κ))

theorem finite_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (.of κ)) [IsFinite g]
    (y : Spec (.of κ)) : Finite Z := by
  have h := g.finite_preimage_singleton y
  have huniv : (Set.univ : Set Z) ⊆ g ⁻¹' {y} := fun z _ => by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subsingleton.elim (α := PrimeSpectrum κ) _ _
  exact Set.finite_univ_iff.mp (h.subset huniv)

theorem support_finite {I : X.IdealSheafData} [IsFinite (I.subschemeι ≫ f)] (y : Spec (.of κ)) :
    (I.support : Set X).Finite := by
  have : Finite I.subscheme := finite_of_isFinite (I.subschemeι ≫ f) y
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact Set.finite_range _

theorem isFinite_mul [IsProper f] {I J : X.IdealSheafData} [IsFinite (I.subschemeι ≫ f)]
    [IsFinite (J.subschemeι ≫ f)] (y : Spec (.of κ)) : IsFinite ((I * J).subschemeι ≫ f) := by
  have hfin : ((I * J).support : Set X).Finite := by
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
    exact (support_finite f y).union (support_finite f y)
  have : Finite (I * J).subscheme := by
    have hinj : Function.Injective (I * J).subschemeι :=
      (I * J).subschemeι.isClosedEmbedding.injective
    have hmem : ∀ z, (I * J).subschemeι z ∈ ((I * J).support : Set X) := fun z => by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self z
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun z => (⟨_, hmem z⟩ : ((I * J).support : Set X)))
      fun a b h => hinj (congrArg Subtype.val h)
  have : LocallyQuasiFinite ((I * J).subschemeι ≫ f) :=
    .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end finiteness

section chi

variable {κ : Type u} [Field κ] {X : Scheme.{u}} (f : X ⟶ Spec (.of κ)) (𝒱 : X.TwoAffineOpenCover)

noncomputable def chi (M : X.Modules) : ℤ :=
  (Module.finrank κ (𝒱.sectionsOf f M).H0 : ℤ) - Module.finrank κ (𝒱.sectionsOf f M).H1

theorem twoAffineOpenCover_eq {𝒱 𝒲 : X.TwoAffineOpenCover}
    (h0 : 𝒲.U0 = 𝒱.U0) (h1 : 𝒲.U1 = 𝒱.U1) : 𝒲 = 𝒱 := by
  cases 𝒱; cases 𝒲; simp only at h0 h1; subst h0; subst h1; rfl

theorem chi_congr {M N : X.Modules} (e : M ≅ N) : chi f 𝒱 M = chi f 𝒱 N := by
  have em : M ≅ (Scheme.Modules.pullback (Iso.refl X).hom).obj N :=
    e ≪≫ ((Scheme.Modules.pullbackId X).app N).symm
  obtain ⟨𝒲, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso f f (Iso.refl X)
      (Category.id_comp f) 𝒱 N M em
  obtain rfl : 𝒲 = 𝒱 := twoAffineOpenCover_eq h0 h1
  unfold chi
  rw [e0.finrank_eq, e1.finrank_eq]

open _root_.CategoryTheory.MonoidalCategory in

theorem chi_invModule [IsProper f] {K : X.IdealSheafData} (hK : K.IsInvertible)
    [IsFinite (K.subschemeι ≫ f)] (y : Spec (.of κ)) :
    chi f 𝒱 K.invModule = chi f 𝒱 (𝟙_ X.Modules) + (K.subschemeι ≫ f).finrank y := by
  have hpt : ∀ t : Spec (.of κ), t = y := fun t => Subsingleton.elim (α := PrimeSpectrum κ) t y
  have hdeg : ∀ t : Spec (.of κ), (K.subschemeι ≫ f).finrank t = (K.subschemeι ≫ f).finrank y :=
    fun t => by rw [hpt t]
  have hA := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq f hK
    ‹_› hdeg (𝟙_ X.Modules) (Scheme.Modules.isInvertible_unit X) 𝒱
  rw [← chi_congr f 𝒱 (λ_ K.invModule)]
  exact hA

open _root_.CategoryTheory.MonoidalCategory in

theorem finrank_mul [IsProper f] (𝒱 : X.TwoAffineOpenCover) {I J : X.IdealSheafData}
    (hI : I.IsInvertible)
    (hJ : J.IsInvertible) [IsFinite (I.subschemeι ≫ f)] [IsFinite (J.subschemeι ≫ f)]
    [IsFinite ((I * J).subschemeι ≫ f)] (y : Spec (.of κ)) :
    ((I * J).subschemeι ≫ f).finrank y =
      (I.subschemeι ≫ f).finrank y + (J.subschemeι ≫ f).finrank y := by
  have h1 := chi_invModule f 𝒱 hI y
  have h2 := chi_invModule f 𝒱 (hI.mul hJ) y
  obtain ⟨eIJ⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hI hJ
  have h3 : chi f 𝒱 (I * J).invModule = chi f 𝒱 (I.invModule ⊗ J.invModule) := chi_congr f 𝒱 eIJ
  have hpt : ∀ t : Spec (.of κ), t = y := fun t => Subsingleton.elim (α := PrimeSpectrum κ) t y
  have hdeg : ∀ t : Spec (.of κ), (J.subschemeι ≫ f).finrank t = (J.subschemeι ≫ f).finrank y :=
    fun t => by rw [hpt t]
  have h4 : chi f 𝒱 (I.invModule ⊗ J.invModule) =
      chi f 𝒱 I.invModule + (J.subschemeι ≫ f).finrank y :=
    Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq f hJ ‹_› hdeg
      I.invModule (Scheme.IdealSheafData.IsInvertible.isInvertible_invModule hI) 𝒱
  omega

end chi

end GAddSol

open CategoryTheory AlgebraicGeometry in
theorem solution
    {κ : Type u} [Field κ] {X : Scheme.{u}} (f : X ⟶ Spec (.of κ)) [IsProper f]
    (𝒱 : X.TwoAffineOpenCover) {I J : X.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) [IsFinite (I.subschemeι ≫ f)] [IsFinite (J.subschemeι ≫ f)]
    (y : Spec (.of κ)) :
    IsFinite ((I * J).subschemeι ≫ f) ∧
      ((I * J).subschemeι ≫ f).finrank y =
        (I.subschemeι ≫ f).finrank y + (J.subschemeι ≫ f).finrank y := by
  have hfin : IsFinite ((I * J).subschemeι ≫ f) := GAddSol.isFinite_mul f y
  exact ⟨hfin, GAddSol.finrank_mul f 𝒱 hI hJ y⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isFinite_and_finrank_mul_subscheme_comp_eq_add
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isFinite_and_finrank_mul_subscheme_comp_eq_add (solution)
