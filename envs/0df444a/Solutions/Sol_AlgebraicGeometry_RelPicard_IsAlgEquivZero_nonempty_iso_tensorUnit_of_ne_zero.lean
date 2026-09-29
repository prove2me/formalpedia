-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8fa43ec1-b1c1-501a-9e79-49a4b1cd61fb

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard"

namespace AlgZeroTrivGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def isoUnitOfIdempotentOfInverse {C : Type*} [Category C] [MonoidalCategory C] {N M : C}
    (e : N ≅ N ⊗ N) (p : N ⊗ M ≅ 𝟙_ C) : N ≅ 𝟙_ C :=
  (ρ_ N).symm ≪≫ whiskerLeftIso N p.symm ≪≫ (α_ N N M).symm ≪≫ whiskerRightIso e.symm M ≪≫ p

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_invModule_top_iso (Y : Scheme.{u}) :
    Nonempty ((⊤ : Y.IdealSheafData).invModule ≅ 𝟙_ Y.Modules) := by
  have hT : (⊤ : Y.IdealSheafData).IsInvertible := Scheme.IdealSheafData.isInvertible_top

  obtain ⟨m⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hT hT
  have e : (⊤ : Y.IdealSheafData).invModule ≅ (⊤ : Y.IdealSheafData).invModule ⊗ (⊤ : Y.IdealSheafData).invModule :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule (Scheme.IdealSheafData.mul_top ⊤).symm) ≪≫ m

  have hN : Scheme.Modules.IsInvertible (⊤ : Y.IdealSheafData).invModule :=
    Scheme.IdealSheafData.IsInvertible.isInvertible_invModule hT
  have hev := Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit hN
  exact ⟨isoUnitOfIdempotentOfInverse e (@asIso _ _ _ _ ((ihom.ev (⊤ : Y.IdealSheafData).invModule).app (𝟙_ Y.Modules)) hev)⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_lineBundle_iso_of_degree_zero {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f 0 g) : Nonempty (D.lineBundle ≅ 𝟙_ (pullback f g).Modules) := by
  obtain ⟨e⟩ := nonempty_invModule_top_iso (pullback f g)
  exact ⟨eqToIso (congrArg Scheme.IdealSheafData.invModule D.I_eq_top_of_degree_zero) ≪≫ e⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def isoPullbackInvPullbackObj {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] (L : Y.Modules) :
    L ≅ (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj L) :=
  ((Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).app L).symm

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem eq_zero_of_pullback_map_eq_zero {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p]
    {A B : Y.Modules} (φ : A ⟶ B) (h : (Scheme.Modules.pullback p).map φ = 0) : φ = 0 := by

  have hn : (Scheme.Modules.pullback (inv p)).map ((Scheme.Modules.pullback p).map φ) ≫
      (isoPullbackInvPullbackObj p B).inv = (isoPullbackInvPullbackObj p A).inv ≫ φ :=
    (Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).hom.naturality φ
  rw [h, Functor.map_zero, zero_comp] at hn
  exact (cancel_epi (isoPullbackInvPullbackObj p A).inv).mp (hn.symm.trans (comp_zero).symm)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem pullbackSection_ne_zero {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] {M : Y.Modules}
    (s : 𝟙_ Y.Modules ⟶ M) (hs : s ≠ 0) : Scheme.Modules.pullbackSection p s ≠ 0 := by
  intro h
  apply hs
  apply eq_zero_of_pullback_map_eq_zero p

  exact ((Scheme.Modules.pullbackUnitIso p).hom_inv_id_assoc ((Scheme.Modules.pullback p).map s)).symm.trans
    ((congrArg ((Scheme.Modules.pullbackUnitIso p).hom ≫ ·) h).trans comp_zero)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem twoAffineOpenCover_ext {Y : Scheme.{u}} {𝒲 𝒲' : Y.TwoAffineOpenCover}
    (h0 : 𝒲.U0 = 𝒲'.U0) (h1 : 𝒲.U1 = 𝒲'.U1) : 𝒲 = 𝒲' := by
  obtain ⟨U0, U1, _, _, _, _⟩ := 𝒲
  obtain ⟨U0', U1', _, _, _, _⟩ := 𝒲'
  dsimp only at h0 h1
  subst h0
  subst h1
  rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_id_opens {Y : Scheme.{u}} (U : Y.Opens) : (𝟙 Y) ⁻¹ᵁ U = U := rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem eulerChar_congr {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1
      = (Module.finrank k (𝒲.sectionsOf y M').H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M').H1 := by
  obtain ⟨𝒲', h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  have h𝒲 : 𝒲' = 𝒲 :=
    twoAffineOpenCover_ext (h0.trans (preimage_id_opens _)) (h1.trans (preimage_id_opens _))
  subst h𝒲
  exact congrArg₂ (fun m n : ℕ => (m : ℤ) - (n : ℤ)) e0.finrank_eq e1.finrank_eq

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_iso_tensorUnit_fibre {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (h0 : IsAlgEquivZero (pullback.snd f x) M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0) (𝒱 : (pullback f x).TwoAffineOpenCover) :
    Nonempty (M ≅ 𝟙_ (pullback f x).Modules) := by

  have hχ := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq (pullback.snd f x) 𝒱 M (𝟙_ _) hM
    (Scheme.Modules.isInvertible_unit _) h0

  obtain ⟨D, -, e, -⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq x hM s hs 𝒱 0
    (by rw [Nat.cast_zero, add_zero]; exact (eulerChar_congr (pullback.snd f x) 𝒱 (ρ_ M).symm).trans hχ)
  obtain ⟨e0⟩ := nonempty_lineBundle_iso_of_degree_zero D
  exact ⟨e ≪≫ e0⟩

end AlgZeroTrivGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (h0 : IsAlgEquivZero x L) (s : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by

  have hp : pullback.fst x (𝟙 _) ≫ x = pullback.snd x (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.condition.trans (Category.comp_id _)

  obtain ⟨𝒱', -, -, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd x (𝟙 (Spec (CommRingCat.of k)))) x (asIso (pullback.fst x (𝟙 _))) hp 𝒱 L
    ((Scheme.Modules.pullback (pullback.fst x (𝟙 _))).obj L) (Iso.refl _)

  obtain ⟨e⟩ := AlgZeroTrivGlue.nonempty_iso_tensorUnit_fibre (f := x) (𝟙 _) (hL.pullback _) (h0.pullback _ hp)
    (Scheme.Modules.pullbackSection _ s) (AlgZeroTrivGlue.pullbackSection_ne_zero _ s hs) 𝒱'

  exact ⟨AlgZeroTrivGlue.isoPullbackInvPullbackObj (pullback.fst x (𝟙 _)) L ≪≫ (Scheme.Modules.pullback _).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso _⟩

#print axioms solution

end S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero (solution)
