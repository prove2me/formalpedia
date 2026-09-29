-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0fdd65cd-d603-5cac-ad5c-dd33add672bb

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

section NoethBC20_block
open GoodReductionJacobian.RelativeGroupLaw

namespace NoethBC20

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem mul_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f)
    (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem one_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) : (G.one t₁).1 = (G.one t₂).1 := by
  subst h; rfl

theorem inv_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ : SchemeHomOver t₁ f) (P₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) :
    (G.inv t₁ P₁).1 = (G.inv t₂ P₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  rfl

theorem toBase_injective {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    Function.Injective
      (baseChangePointToBase ι : SchemeHomOver t' (baseChangeStr ι f) → SchemeHomOver (t' ≫ ι) f) :=
  (baseChangePointEquiv ι t').injective

section Endo

variable (φ : A ⟶ A) (hφ : φ ≫ f = f)

def bcEndo : baseChangeScheme ι f ⟶ baseChangeScheme ι f :=
  pullback.lift (pullback.fst f ι ≫ φ) (pullback.snd f ι) (by rw [Category.assoc, hφ, pullback.condition])

@[reassoc (attr := simp)]
theorem bcEndo_fst : bcEndo ι φ hφ ≫ pullback.fst f ι = pullback.fst f ι ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcEndo_snd : bcEndo ι φ hφ ≫ pullback.snd f ι = pullback.snd f ι :=
  pullback.lift_snd _ _ _

theorem bcEndo_over : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f :=
  pullback.lift_snd _ _ _

theorem bcEndo_congr {φ ψ : A ⟶ A} (h : φ = ψ) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) :
    bcEndo ι φ hφ = bcEndo ι ψ hψ := by
  subst h; rfl

theorem bcEndo_eq_id {φ : A ⟶ A} (h : φ = 𝟙 A) (hφ : φ ≫ f = f) : bcEndo ι φ hφ = 𝟙 _ := by
  subst h
  apply pullback.hom_ext
  · rw [bcEndo_fst, Category.id_comp, Category.comp_id]
  · rw [bcEndo_snd, Category.id_comp]

theorem bcEndo_eq_comp {χ ψ φ : A ⟶ A} (h : χ = ψ ≫ φ) (hχ : χ ≫ f = f) (hψ : ψ ≫ f = f) (hφ : φ ≫ f = f) :
    bcEndo ι χ hχ = bcEndo ι ψ hψ ≫ bcEndo ι φ hφ := by
  subst h
  apply pullback.hom_ext
  · simp only [bcEndo_fst, Category.assoc, bcEndo_fst_assoc]
  · simp only [bcEndo_snd, Category.assoc]

theorem toBase_pushPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (P : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι (pushPt (bcEndo ι φ hφ) h' P) = pushPt φ hφ (baseChangePointToBase ι P) := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, mapPt_coe, Category.assoc, bcEndo_fst]

theorem pushPt_bcEndo_mul (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (G.mul t P Q) = G.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    pushPt (bcEndo ι φ hφ) h' ((G.baseChange ι).mul t' P Q) =
      (G.baseChange ι).mul t' (pushPt (bcEndo ι φ hφ) h' P) (pushPt (bcEndo ι φ hφ) h' Q) := by
  apply toBase_injective ι t'
  rw [toBase_pushPt, baseChangePointToBase_mul, baseChangePointToBase_mul, H, toBase_pushPt, toBase_pushPt]

theorem pushPt_bcEndo_add (G : RelativeGroupLaw R f) {χ ψ : A ⟶ A} (hχ : χ ≫ f = f) (hψ : ψ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt χ hχ P = G.mul t (pushPt φ hφ P) (pushPt ψ hψ P))
    (hχ' : bcEndo ι χ hχ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (hφ' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (hψ' : bcEndo ι ψ hψ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    pushPt (bcEndo ι χ hχ) hχ' P =
      (G.baseChange ι).mul t' (pushPt (bcEndo ι φ hφ) hφ' P) (pushPt (bcEndo ι ψ hψ) hψ' P) := by
  apply toBase_injective ι t'
  rw [toBase_pushPt, baseChangePointToBase_mul, H, toBase_pushPt, toBase_pushPt]

end Endo

section Lev

variable (f) {C : Scheme.{u}} (lev : C ⟶ A)

abbrev bcLevScheme : Scheme.{u} :=
  pullback (lev ≫ f) ι

def bcLev : bcLevScheme ι f lev ⟶ baseChangeScheme ι f :=
  pullback.lift (pullback.fst (lev ≫ f) ι ≫ lev) (pullback.snd (lev ≫ f) ι)
    (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem bcLev_fst : bcLev ι f lev ≫ pullback.fst f ι = pullback.fst (lev ≫ f) ι ≫ lev :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcLev_snd : bcLev ι f lev ≫ pullback.snd f ι = pullback.snd (lev ≫ f) ι :=
  pullback.lift_snd _ _ _

theorem bcLev_comp_baseChangeStr : bcLev ι f lev ≫ baseChangeStr ι f = pullback.snd (lev ≫ f) ι :=
  pullback.lift_snd _ _ _

theorem isPullback_fst_bcLev :
    IsPullback (pullback.fst (lev ≫ f) ι) (bcLev ι f lev) lev (pullback.fst f ι) := by
  refine IsPullback.of_bot ?_ (bcLev_fst ι f lev).symm (IsPullback.of_hasPullback f ι)
  rw [bcLev_snd]
  exact IsPullback.of_hasPullback (lev ≫ f) ι

theorem isClosedImmersion_bcLev [IsClosedImmersion lev] : IsClosedImmersion (bcLev ι f lev) :=
  MorphismProperty.of_isPullback (isPullback_fst_bcLev ι f lev) ‹_›

theorem isFinite_bcLev_comp [IsFinite (lev ≫ f)] : IsFinite (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem flat_bcLev_comp [Flat (lev ≫ f)] : Flat (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem locallyOfFinitePresentation_bcLev_comp [LocallyOfFinitePresentation (lev ≫ f)] :
    LocallyOfFinitePresentation (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem factorsThrough_bcLev_iff {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P ↔ FactorsThrough lev (baseChangePointToBase ι P) := by
  constructor
  · rintro ⟨P₀, hP₀⟩
    refine ⟨P₀ ≫ pullback.fst (lev ≫ f) ι, ?_⟩
    rw [baseChangePointToBase_coe, ← hP₀, Category.assoc, Category.assoc, bcLev_fst]
  · rintro ⟨Q₀, hQ₀⟩
    rw [baseChangePointToBase_coe] at hQ₀
    refine ⟨pullback.lift Q₀ (P.1 ≫ pullback.snd f ι) ?_, ?_⟩
    · rw [← Category.assoc, hQ₀, Category.assoc, Category.assoc, pullback.condition]
    · apply pullback.hom_ext
      · rw [Category.assoc, bcLev_fst, ← Category.assoc, pullback.lift_fst, hQ₀]
      · rw [Category.assoc, bcLev_snd, pullback.lift_snd]

theorem toBase_nsmulPt (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (n : ℕ) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι (nsmulPt (G.baseChange ι) t' n P) =
      nsmulPt G (t' ≫ ι) n (baseChangePointToBase ι P) := by
  induction n with
  | zero => exact baseChangePointToBase_one ι G t'
  | succ n ih => simp only [nsmulPt, baseChangePointToBase_mul, ih]

theorem lev_sub_bc (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (G.mul t P Q) ∧ FactorsThrough lev (G.inv t P))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) Q →
      FactorsThrough (bcLev ι f lev) ((G.baseChange ι).mul t' P Q) ∧
        FactorsThrough (bcLev ι f lev) ((G.baseChange ι).inv t' P) := by
  intro hP hQ
  rw [factorsThrough_bcLev_iff] at hP hQ
  rw [factorsThrough_bcLev_iff, factorsThrough_bcLev_iff, baseChangePointToBase_mul, baseChangePointToBase_inv]
  exact H _ _ _ hP hQ

theorem lev_one_bc (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (G.one t))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    FactorsThrough (bcLev ι f lev) ((G.baseChange ι).one t') := by
  rw [factorsThrough_bcLev_iff, baseChangePointToBase_one]
  exact H _

theorem lev_torsion_bc (G : RelativeGroupLaw R f) (N : ℕ)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt G t N P = G.one t)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → nsmulPt (G.baseChange ι) t' N P = (G.baseChange ι).one t' := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  apply toBase_injective ι t'
  rw [toBase_nsmulPt, baseChangePointToBase_one]
  exact H _ _ hP

theorem lev_stable_bc (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev (pushPt φ hφ P))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) (pushPt (bcEndo ι φ hφ) h' P) := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  rw [factorsThrough_bcLev_iff, toBase_pushPt]
  exact H _ _ hP

end Lev

theorem geometricallyConnected_baseChangeStr [GeometricallyConnected f] :
    GeometricallyConnected (baseChangeStr ι f) :=
  inferInstance

theorem abelianSchemePropertyBundle_bc (hb : AbelianSchemePropertyBundle R f) [GeometricallyConnected f]
    (G' : RelativeGroupLaw R' (baseChangeStr ι f)) :
    AbelianSchemePropertyBundle R' (baseChangeStr ι f) where
  smooth := have := hb.smooth; inferInstance
  proper := have := hb.proper; inferInstance
  connectedFibres s := (baseChangeStr ι f).isConnected_preimage_singleton s
  hasGroupLaw := ⟨G'⟩

section Comparison

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of S))
variable (j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (j' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R'))
variable (hj : j' ≫ ι = j) (g : X ⟶ A) (hg : IsPullback g p f j)

def bcComparison : X ⟶ baseChangeScheme ι f :=
  pullback.lift g (p ≫ j') (by rw [Category.assoc, hj]; exact hg.w)

@[reassoc (attr := simp)]
theorem bcComparison_fst : bcComparison ι p j j' hj g hg ≫ pullback.fst f ι = g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcComparison_snd : bcComparison ι p j j' hj g hg ≫ pullback.snd f ι = p ≫ j' :=
  pullback.lift_snd _ _ _

theorem isPullback_bcComparison :
    IsPullback (bcComparison ι p j j' hj g hg) p (baseChangeStr ι f) j' := by
  refine IsPullback.of_right ?_ (bcComparison_snd ι p j j' hj g hg) (IsPullback.of_hasPullback f ι)
  rw [bcComparison_fst, hj]
  exact hg

theorem comp_bcComparison_eq_bcComparison_comp_bcEndo (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (actX : X ⟶ X) (hactX : actX ≫ p = p) (H : actX ≫ g = g ≫ φ) :
    actX ≫ bcComparison ι p j j' hj g hg = bcComparison ι p j j' hj g hg ≫ bcEndo ι φ hφ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcComparison_fst, bcEndo_fst, bcComparison_fst_assoc, H]
  · simp only [Category.assoc, bcComparison_snd, bcEndo_snd]
    rw [← Category.assoc, hactX]

theorem mul_coe_comp_bcComparison (GX : RelativeGroupLaw S p) (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p),
      (GX.mul t P Q).1 ≫ g =
        (G.mul (t ≫ j) ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p) :
    (GX.mul t P Q).1 ≫ bcComparison ι p j j' hj g hg =
      ((G.baseChange ι).mul (t ≫ j')
        ⟨P.1 ≫ bcComparison ι p j j' hj g hg, by
          rw [Category.assoc, (isPullback_bcComparison ι p j j' hj g hg).w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ bcComparison ι p j j' hj g hg, by
          rw [Category.assoc, (isPullback_bcComparison ι p j j' hj g hg).w, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcComparison_fst, H, baseChange_mul, baseChangePointOfBase_coe, pullback.lift_fst]
    apply mul_coe_congr G
    · rw [Category.assoc, hj]
    · simp only [baseChangePointToBase_coe, Category.assoc, bcComparison_fst]
    · simp only [baseChangePointToBase_coe, Category.assoc, bcComparison_fst]
  · have e1 : ∀ x : SchemeHomOver (t ≫ j') (baseChangeStr ι f), x.1 ≫ pullback.snd f ι = t ≫ j' :=
      fun x => x.2
    rw [e1]
    simp only [Category.assoc, bcComparison_snd]
    rw [← Category.assoc, (GX.mul t P Q).2]

section Sub

variable {C : Scheme.{u}} (lev : C ⟶ A) {XC : Scheme.{u}} (pC : XC ⟶ X) (gC : XC ⟶ C)
variable (hgC : IsPullback gC pC lev g)

def bcComparisonSub : XC ⟶ bcLevScheme ι f lev :=
  pullback.lift gC (pC ≫ p ≫ j') (by
    rw [← Category.assoc gC, hgC.w, Category.assoc, hg.w, Category.assoc, Category.assoc, hj])

@[reassoc (attr := simp)]
theorem bcComparisonSub_fst : bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ pullback.fst (lev ≫ f) ι = gC :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcComparisonSub_snd :
    bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ pullback.snd (lev ≫ f) ι = pC ≫ p ≫ j' :=
  pullback.lift_snd _ _ _

theorem bcComparisonSub_bcLev :
    bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ bcLev ι f lev = pC ≫ bcComparison ι p j j' hj g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcLev_fst, bcComparisonSub_fst_assoc, bcComparison_fst]
    exact hgC.w
  · simp only [Category.assoc, bcLev_snd, bcComparisonSub_snd, bcComparison_snd]

theorem isPullback_bcComparisonSub :
    IsPullback (bcComparisonSub ι p j j' hj g hg lev pC gC hgC) pC (bcLev ι f lev)
      (bcComparison ι p j j' hj g hg) := by
  refine IsPullback.of_right ?_ (bcComparisonSub_bcLev ι p j j' hj g hg lev pC gC hgC) (isPullback_fst_bcLev ι f lev)
  rw [bcComparisonSub_fst, bcComparison_fst]
  exact hgC

end Sub

end Comparison

end NoethBC20

end NoethBC20_block

namespace NoethKit19

theorem mul_coe_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x y : SchemeHomOver t₁ f) :
    (G.mul t₁ x y).1 = (G.mul t₂ ⟨x.1, h ▸ x.2⟩ ⟨y.1, h ▸ y.2⟩).1 := by
  subst h; rfl

section Compare

variable {R₁ : Type u} [CommRing R₁] {L : Type u} [CommRing L] [Algebra R₁ L] (T : Subalgebra R₁ L)
  {A₁ : Scheme.{u}} (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁))

theorem specMap_val_comp :
    Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R₁ L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem exists_transition :
    ∃ r : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))) ⟶
        pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))),
      r ≫ pullback.fst f₁ _ = pullback.fst f₁ _ ∧
      r ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) :=
  ⟨pullback.lift (pullback.fst f₁ _) (pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
      (by rw [Category.assoc, specMap_val_comp]; exact pullback.condition),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

variable {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of L)} (π : X ⟶ A₁)
  (hπ : IsPullback π p f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))))

theorem isPullback_comp_transition
    (r : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))) ⟶
        pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))))
    (hr_fst : r ≫ pullback.fst f₁ _ = pullback.fst f₁ _)
    (hr_snd : r ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) :
    IsPullback (hπ.isoPullback.hom ≫ r) p (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))))
      (Spec.map (CommRingCat.ofHom T.val.toRingHom)) := by
  have hg_fst : (hπ.isoPullback.hom ≫ r) ≫ pullback.fst f₁ _ = π := by
    rw [Category.assoc, hr_fst, hπ.isoPullback_hom_fst]
  have hg_snd : (hπ.isoPullback.hom ≫ r) ≫ pullback.snd f₁ _ = p ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
    rw [Category.assoc, hr_snd, ← Category.assoc, hπ.isoPullback_hom_snd]
  refine IsPullback.of_right (h₁₂ := pullback.fst f₁ _) (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))) (v₁₃ := f₁)
    ?_ hg_snd (IsPullback.of_hasPullback f₁ _)
  rw [hg_fst, specMap_val_comp]; exact hπ

variable (L₁ : RelativeGroupLaw R₁ f₁) (G : RelativeGroupLaw L p)

theorem mul_comp_transition
    (hmul : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t p),
      (G.mul t x y).1 ≫ π =
        (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ L)))
          ⟨x.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, y.2]⟩).1)
    (r : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))) ⟶
        pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))))
    (hr_fst : r ≫ pullback.fst f₁ _ = pullback.fst f₁ _)
    (hr_snd : r ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t' p) :
    (G.mul t' x y).1 ≫ (hπ.isoPullback.hom ≫ r) =
      ((L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T)))).mul
          (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
        ⟨x.1 ≫ (hπ.isoPullback.hom ≫ r), by
          rw [Category.assoc, (isPullback_comp_transition T f₁ π hπ r hr_fst hr_snd).w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ (hπ.isoPullback.hom ≫ r), by
          rw [Category.assoc, (isPullback_comp_transition T f₁ π hπ r hr_fst hr_snd).w, ← Category.assoc, y.2]⟩).1 := by
  have hg_fst : (hπ.isoPullback.hom ≫ r) ≫ pullback.fst f₁ _ = π := by
    rw [Category.assoc, hr_fst, hπ.isoPullback_hom_fst]
  have hg_snd : (hπ.isoPullback.hom ≫ r) ≫ pullback.snd f₁ _ = p ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
    rw [Category.assoc, hr_snd, ← Category.assoc, hπ.isoPullback_hom_snd]
  have ht : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ L)) =
      (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T)) := by
    rw [Category.assoc, specMap_val_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, hg_fst, hmul t' x y, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst, mul_coe_congr L₁ ht]
    congr 2
    · apply Subtype.ext
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hr_fst, IsPullback.isoPullback_hom_fst]
    · apply Subtype.ext
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hr_fst, IsPullback.isoPullback_hom_fst]
  · rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd, Category.assoc, hg_snd,
      ← Category.assoc, (G.mul t' x y).2]

end Compare

theorem bundle_baseChange {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (G : RelativeGroupLaw R f) (hb : AbelianSchemePropertyBundle R f)
    [GeometricallyConnected f] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) :
    AbelianSchemePropertyBundle R' (pullback.snd f ι) ∧ GeometricallyConnected (pullback.snd f ι) := by
  haveI : IsProper f := hb.proper
  haveI : Smooth f := hb.smooth
  exact ⟨⟨inferInstance, inferInstance, fun x => (pullback.snd f ι).isConnected_preimage_singleton x, ⟨G.baseChange ι⟩⟩,
    inferInstance⟩

theorem fg_restrictScalars {L : Type u} [CommRing L] (R₁ : Subalgebra ℤ L) (T : Subalgebra ↥R₁ L)
    (h₁ : R₁.FG) (h₂ : T.FG) : (T.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 h₁
  have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 h₂
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3

end NoethKit19

namespace EndKit19

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def Endo (G : RelativeGroupLaw R f) : Type u := SchemeHomOver f f

def Pts (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : Type u := SchemeHomOver t f

class IsComm (G : RelativeGroupLaw R f) : Prop where
  out : G.IsCommutative

variable (G : RelativeGroupLaw R f)

scoped instance : Group (Endo G) := G.pointGroup f
scoped instance {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : Group (Pts G t) := G.pointGroup t

scoped instance [IsComm G] : CommGroup (Endo G) :=
  { (inferInstance : Group (Endo G)) with mul_comm := fun x y => RelativeGroupLaw.IsCommutative.mul_comm (IsComm.out (G := G)) f x y }
scoped instance [IsComm G] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (Pts G t) :=
  { (inferInstance : Group (Pts G t)) with mul_comm := fun x y => RelativeGroupLaw.IsCommutative.mul_comm (IsComm.out (G := G)) t x y }

def Endo.mk (u : SchemeHomOver f f) : Endo G := u

def Endo.val {G : RelativeGroupLaw R f} (u : Endo G) : SchemeHomOver f f := u

def Pts.mk {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : Pts G t := P

def Pts.val {G : RelativeGroupLaw R f} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : Pts G t) : SchemeHomOver t f := P

variable {G}

@[scoped simp] theorem Endo.val_mk (u : SchemeHomOver f f) : (Endo.mk G u).val = u := rfl
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo"
@[scoped simp] theorem Pts.val_mk {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    (Pts.mk G P).val = P := rfl

p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts"
theorem Endo.mul_val (u v : Endo G) : (u * v).val = G.mul f u.val v.val := rfl
theorem Endo.one_val : (1 : Endo G).val = G.one f := rfl
theorem Endo.inv_val (u : Endo G) : (u⁻¹).val = G.inv f u.val := rfl
theorem Pts.mul_val {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P Q : Pts G t) :
    (P * Q).val = G.mul t P.val Q.val := rfl
theorem Pts.one_val {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} : (1 : Pts G t).val = G.one t := rfl
theorem Pts.inv_val {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : Pts G t) : (P⁻¹).val = G.inv t P.val := rfl

theorem Endo.ext {u v : Endo G} (h : u.val.1 = v.val.1) : u = v := Subtype.ext h
theorem Pts.ext {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : Pts G t} (h : P.val.1 = Q.val.1) : P = Q :=
  Subtype.ext h
theorem Pts.val_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} :
    Function.Injective (Pts.val : Pts G t → SchemeHomOver t f) := fun _ _ h => h

theorem pushPt_mul_coe (u v : SchemeHomOver f f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    pushPt (G.mul f u v).1 (G.mul f u v).2 P = G.mul t (pushPt u.1 u.2 P) (pushPt v.1 v.2 P) := by
  have h := G.mul_natural f t P.1 P.2 u v
  have e1 : schemeHomOverComp P.1 P.2 (G.mul f u v) = pushPt (G.mul f u v).1 (G.mul f u v).2 P := Subtype.ext rfl
  have e2 : schemeHomOverComp P.1 P.2 u = pushPt u.1 u.2 P := Subtype.ext rfl
  have e3 : schemeHomOverComp P.1 P.2 v = pushPt v.1 v.2 P := Subtype.ext rfl
  rw [e1, e2, e3] at h
  exact h

theorem pushPt_one_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    pushPt (G.one f).1 (G.one f).2 P = G.one t := by
  have h := G.one_natural f t P.1 P.2
  have e1 : schemeHomOverComp P.1 P.2 (G.one f) = pushPt (G.one f).1 (G.one f).2 P := Subtype.ext rfl
  rw [e1] at h
  exact h

def ev {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : Endo G →* Pts G t :=
  { toFun := fun u => Pts.mk G (pushPt u.val.1 u.val.2 P)
    map_one' := Pts.ext (congrArg Subtype.val (pushPt_one_coe (G := G) P))
    map_mul' := fun u v => Pts.ext (congrArg Subtype.val (pushPt_mul_coe (G := G) u.val v.val P)) }

theorem ev_apply_val {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) (u : Endo G) :
    (ev P u).val = pushPt u.val.1 u.val.2 P := rfl

structure IsHom (u : Endo G) : Prop where
  out : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    pushPt u.val.1 u.val.2 (G.mul t P Q) = G.mul t (pushPt u.val.1 u.val.2 P) (pushPt u.val.1 u.val.2 Q)

theorem IsHom.ev_mul {u : Endo G} (hu : IsHom u) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P Q : Pts G t) :
    ev (P * Q).val u = ev P.val u * ev Q.val u :=
  Pts.ext (congrArg Subtype.val (hu.out t P.val Q.val))

theorem IsHom.ev_one {u : Endo G} (hu : IsHom u) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ev (G.one t) u = (1 : Pts G t) := by
  have h := hu.ev_mul (1 : Pts G t) 1
  rw [mul_one] at h
  have h2 : ev (1 : Pts G t).val u * ev (1 : Pts G t).val u = ev (1 : Pts G t).val u * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

theorem IsHom.ev_inv [IsComm G] {u : Endo G} (hu : IsHom u) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : Pts G t) : ev (P⁻¹).val u = (ev P.val u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hu.ev_mul, inv_mul_cancel]; exact hu.ev_one t

theorem isHom_one : IsHom (1 : Endo G) := by
  refine ⟨fun t P Q => ?_⟩
  show pushPt (G.one f).1 (G.one f).2 _ = G.mul t (pushPt (G.one f).1 (G.one f).2 P) (pushPt (G.one f).1 (G.one f).2 Q)
  rw [pushPt_one_coe, pushPt_one_coe, pushPt_one_coe, G.one_mul]

theorem isHom_mul [IsComm G] {u v : Endo G} (hu : IsHom u) (hv : IsHom v) : IsHom (u * v) := by
  refine ⟨fun t P Q => ?_⟩
  have key : ev (Pts.mk G P * Pts.mk G Q).val (u * v) = ev P (u * v) * ev Q (u * v) := by
    rw [map_mul, map_mul, map_mul, hu.ev_mul, hv.ev_mul]
    simp only [Pts.val_mk]
    rw [mul_mul_mul_comm]
  exact congrArg Pts.val key

theorem isHom_inv [IsComm G] {u : Endo G} (hu : IsHom u) : IsHom u⁻¹ := by
  refine ⟨fun t P Q => ?_⟩
  have key : ev (Pts.mk G P * Pts.mk G Q).val u⁻¹ = ev P u⁻¹ * ev Q u⁻¹ := by
    rw [map_inv, map_inv, map_inv, hu.ev_mul, mul_inv]; rfl
  exact congrArg Pts.val key

def homSubgroup [IsComm G] : Subgroup (Endo G) :=
  { carrier := {u | IsHom u}
    one_mem' := isHom_one
    mul_mem' := fun hu hv => isHom_mul hu hv
    inv_mem' := fun hu => isHom_inv hu }

theorem mem_homSubgroup [IsComm G] {u : Endo G} : u ∈ homSubgroup ↔ IsHom u := Iff.rfl

def compE (u v : Endo G) : Endo G := Endo.mk G ⟨u.val.1 ≫ v.val.1, by rw [Category.assoc, v.val.2, u.val.2]⟩

@[scoped simp] theorem compE_val_coe (u v : Endo G) : (compE u v).val.1 = u.val.1 ≫ v.val.1 := rfl

end EndKit19
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19"

namespace EndKit19

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {G : RelativeGroupLaw R f}

def compLeft (w : Endo G) : Endo G →* Endo G :=
  { toFun := fun u => compE w u
    map_one' := Endo.ext (by
      rw [compE_val_coe]
      exact congrArg Subtype.val (pushPt_one_coe (G := G) w.val))
    map_mul' := fun u v => Endo.ext (by
      rw [compE_val_coe]
      exact congrArg Subtype.val (pushPt_mul_coe (G := G) u.val v.val w.val)) }

@[scoped simp] theorem compLeft_apply (w u : Endo G) : compLeft w u = compE w u := rfl

def compRight (w : Endo G) (hw : IsHom w) : Endo G →* Endo G :=
  { toFun := fun u => compE u w
    map_one' := Endo.ext (by
      rw [compE_val_coe]
      have h := congrArg Pts.val (hw.ev_one f)
      exact congrArg Subtype.val h)
    map_mul' := fun u v => Endo.ext (by
      rw [compE_val_coe]
      exact congrArg Subtype.val (hw.out f u.val v.val)) }

@[scoped simp] theorem compRight_apply (w : Endo G) (hw : IsHom w) (u : Endo G) : compRight w hw u = compE u w := rfl

theorem compE_assoc (u v w : Endo G) : compE (compE u v) w = compE u (compE v w) :=
  Endo.ext (by simp only [compE_val_coe, Category.assoc])

theorem isHom_compE {u v : Endo G} (hu : IsHom u) (hv : IsHom v) : IsHom (compE u v) := by
  refine ⟨fun t P Q => ?_⟩
  have e : ∀ X : SchemeHomOver t f, pushPt (compE u v).val.1 (compE u v).val.2 X =
      pushPt v.val.1 v.val.2 (pushPt u.val.1 u.val.2 X) := fun X => Subtype.ext (by simp [mapPt_coe, Category.assoc])
  rw [e, e, e, hu.out, hv.out]

section Lin

variable {ι : Type} [Fintype ι] {M : Type*} [CommGroup M]

def lin (Ψ : ι → M) (c : ι → ℤ) : M := ∏ i, Ψ i ^ c i

theorem lin_add (Ψ : ι → M) (c d : ι → ℤ) : lin Ψ (c + d) = lin Ψ c * lin Ψ d := by
  simp only [lin, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem lin_zero (Ψ : ι → M) : lin Ψ 0 = 1 := by
  simp only [lin, Pi.zero_apply, zpow_zero, Finset.prod_const_one]

theorem lin_zsmul (Ψ : ι → M) (n : ℤ) (c : ι → ℤ) : lin Ψ (n • c) = lin Ψ c ^ n := by
  simp only [lin, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_comm, zpow_mul]

theorem lin_sum (Ψ : ι → M) {κ : Type} (s : Finset κ) (c : κ → ι → ℤ) :
    lin Ψ (∑ k ∈ s, c k) = ∏ k ∈ s, lin Ψ (c k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, lin_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, lin_add, ih]

theorem map_lin {H : Type*} [CommGroup H] (φ : M →* H) (Ψ : ι → M) (c : ι → ℤ) :
    φ (lin Ψ c) = lin (fun i => φ (Ψ i)) c := by
  simp only [lin, map_prod, map_zpow]

theorem eq_lin_of_map_add {Λ' : Type*} [AddCommGroup Λ'] (act : Λ' → M) (hadd : ∀ x y, act (x + y) = act x * act y)
    (β : ι → Λ') (c : ι → ℤ) : act (∑ i, c i • β i) = lin (fun i => act (β i)) c := by
  let φ : Λ' →+ Additive M := AddMonoidHom.mk' (fun x => Additive.ofMul (act x)) (fun x y => by
    show Additive.ofMul (act (x + y)) = Additive.ofMul (act x) + Additive.ofMul (act y)
    rw [hadd]; rfl)
  have : Additive.toMul (φ (∑ i, c i • β i)) = act (∑ i, c i • β i) := rfl
  rw [← this, map_sum, toMul_sum]
  simp only [map_zsmul, toMul_zsmul, lin]
  rfl

variable [IsComm G]
theorem isHom_lin {Ψ : ι → Endo G} (hΨ : ∀ i, IsHom (Ψ i)) (c : ι → ℤ) : IsHom (lin Ψ c) := by
  show lin Ψ c ∈ homSubgroup
  exact Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _ (mem_homSubgroup.2 (hΨ i)) _

theorem compE_lin_lin {Ψ : ι → Endo G} (hΨ : ∀ i, IsHom (Ψ i)) (m : ι → ι → ι → ℤ)
    (hm : ∀ j k, compE (Ψ k) (Ψ j) = lin Ψ (m j k)) (c d : ι → ℤ) :
    compE (lin Ψ d) (lin Ψ c) = lin Ψ (∑ k, d k • ∑ j, c j • m j k) := by
  have h1 : compE (lin Ψ d) (lin Ψ c) = compRight (lin Ψ c) (isHom_lin hΨ c) (lin Ψ d) := rfl
  rw [h1, map_lin]
  simp only [compRight_apply]
  have h2 : ∀ k, compE (Ψ k) (lin Ψ c) = lin Ψ (∑ j, c j • m j k) := by
    intro k
    have : compE (Ψ k) (lin Ψ c) = compLeft (Ψ k) (lin Ψ c) := rfl
    rw [this, map_lin]
    simp only [compLeft_apply, hm]
    rw [lin_sum]
    show lin (fun j => lin Ψ (m j k)) c = ∏ j, lin Ψ (c j • m j k)
    simp only [lin_zsmul]; rfl
  simp only [h2]
  rw [lin_sum]
  simp only [lin_zsmul]; rfl

end Lin
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19"

end EndKit19
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19"

namespace EndKit19

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {G : RelativeGroupLaw R f}

scoped instance [IsComm G] : IsComm (G.baseChange ι) := ⟨RelativeGroupLaw.IsCommutative.baseChange ι IsComm.out⟩

def fstPt : SchemeHomOver (pullback.snd f ι ≫ ι) f := ⟨pullback.fst f ι, pullback.condition⟩

@[scoped simp] theorem fstPt_coe : (fstPt ι (f := f)).1 = pullback.fst f ι := rfl

theorem toBase_bc (u : Endo G) :
    RelativeGroupLaw.baseChangePointToBase ι (⟨NoethBC20.bcEndo ι u.val.1 u.val.2, NoethBC20.bcEndo_over ι u.val.1 u.val.2⟩ :
      SchemeHomOver (pullback.snd f ι) (pullback.snd f ι)) = pushPt u.val.1 u.val.2 (fstPt ι) :=
  Subtype.ext (by simp [RelativeGroupLaw.baseChangePointToBase_coe, NoethBC20.bcEndo_fst, mapPt_coe])

def bcHom (G : RelativeGroupLaw R f) : Endo G →* Endo (G.baseChange ι) :=
  { toFun := fun u => Endo.mk _ ⟨NoethBC20.bcEndo ι u.val.1 u.val.2, NoethBC20.bcEndo_over ι u.val.1 u.val.2⟩
    map_one' := by
      apply Endo.ext
      apply congrArg Subtype.val
      apply NoethBC20.toBase_injective ι
      show RelativeGroupLaw.baseChangePointToBase ι ⟨NoethBC20.bcEndo ι (1 : Endo G).val.1 (1 : Endo G).val.2, _⟩ =
        RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).one _)
      rw [toBase_bc, RelativeGroupLaw.baseChangePointToBase_one]
      exact pushPt_one_coe (G := G) (fstPt ι)
    map_mul' := fun u v => by
      apply Endo.ext
      apply congrArg Subtype.val
      apply NoethBC20.toBase_injective ι
      show RelativeGroupLaw.baseChangePointToBase ι ⟨NoethBC20.bcEndo ι (u * v).val.1 (u * v).val.2, _⟩ =
        RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).mul _ ⟨NoethBC20.bcEndo ι u.val.1 u.val.2, _⟩
          ⟨NoethBC20.bcEndo ι v.val.1 v.val.2, _⟩)
      rw [toBase_bc, RelativeGroupLaw.baseChangePointToBase_mul, toBase_bc, toBase_bc]
      exact pushPt_mul_coe (G := G) u.val v.val (fstPt ι) }

theorem bcHom_val_coe (u : Endo G) : (bcHom ι G u).val.1 = NoethBC20.bcEndo ι u.val.1 u.val.2 := rfl

theorem bcHom_compE (u v : Endo G) : bcHom ι G (compE u v) = compE (bcHom ι G u) (bcHom ι G v) :=
  Endo.ext (NoethBC20.bcEndo_eq_comp ι rfl (compE u v).val.2 u.val.2 v.val.2)

def idE (G : RelativeGroupLaw R f) : Endo G := Endo.mk G ⟨𝟙 A, Category.id_comp f⟩

@[scoped simp] theorem idE_val_coe : (idE G).val.1 = 𝟙 A := rfl

theorem bcHom_idE : bcHom ι G (idE G) = idE (G.baseChange ι) :=
  Endo.ext (NoethBC20.bcEndo_eq_id ι rfl (idE G).val.2)

theorem isHom_bcHom_of (u : Endo G)
    (h : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver (t' ≫ ι) f),
      pushPt u.val.1 u.val.2 (G.mul _ P Q) = G.mul _ (pushPt u.val.1 u.val.2 P) (pushPt u.val.1 u.val.2 Q)) :
    IsHom (bcHom ι G u) := by
  refine ⟨fun t' P Q => ?_⟩
  apply NoethBC20.toBase_injective ι
  show RelativeGroupLaw.baseChangePointToBase ι (pushPt (NoethBC20.bcEndo ι u.val.1 u.val.2) _ ((G.baseChange ι).mul t' P Q)) =
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).mul t' (pushPt (NoethBC20.bcEndo ι u.val.1 u.val.2) _ P)
      (pushPt (NoethBC20.bcEndo ι u.val.1 u.val.2) _ Q))
  rw [NoethBC20.toBase_pushPt, RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_mul, h, NoethBC20.toBase_pushPt,
    NoethBC20.toBase_pushPt]

variable (G)

def mulMor : pullback f f ⟶ A :=
  (G.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

def mulMorPush (u : Endo G) : pullback f f ⟶ A :=
  (G.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f ≫ u.val.1, by rw [Category.assoc, u.val.2]⟩
    ⟨pullback.snd f f ≫ u.val.1, by rw [Category.assoc, u.val.2]; exact pullback.condition.symm⟩).1

variable {G}

theorem mulMor_comp_f : mulMor G ≫ f = pullback.fst f f ≫ f := (G.mul _ _ _).2
theorem mulMorPush_comp_f (u : Endo G) : mulMorPush G u ≫ f = pullback.fst f f ≫ f := (G.mul _ _ _).2

theorem lift_comp_mulMor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P Q : SchemeHomOver t f) :
    pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulMor G = (G.mul t P Q).1 := by
  have h := G.mul_natural (pullback.fst f f ≫ f) t (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm))
    (by rw [pullback.lift_fst_assoc, P.2]) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have e1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm))
      (by rw [pullback.lift_fst_assoc, P.2]) (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = P :=
    Subtype.ext (pullback.lift_fst _ _ _)
  have e2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm))
      (by rw [pullback.lift_fst_assoc, P.2])
      (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = Q :=
    Subtype.ext (pullback.lift_snd _ _ _)
  rw [e1, e2] at h
  exact congrArg Subtype.val h

theorem lift_comp_mulMorPush {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P Q : SchemeHomOver t f) (u : Endo G) :
    pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulMorPush G u =
      (G.mul t (pushPt u.val.1 u.val.2 P) (pushPt u.val.1 u.val.2 Q)).1 := by
  have h := G.mul_natural (pullback.fst f f ≫ f) t (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm))
    (by rw [pullback.lift_fst_assoc, P.2]) ⟨pullback.fst f f ≫ u.val.1, by rw [Category.assoc, u.val.2]⟩
    ⟨pullback.snd f f ≫ u.val.1, by rw [Category.assoc, u.val.2]; exact pullback.condition.symm⟩
  have e1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm))
      (by rw [pullback.lift_fst_assoc, P.2])
      (⟨pullback.fst f f ≫ u.val.1, by rw [Category.assoc, u.val.2]⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) =
      pushPt u.val.1 u.val.2 P :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, mapPt_coe, ← Category.assoc, pullback.lift_fst])
  have e2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm))
      (by rw [pullback.lift_fst_assoc, P.2])
      (⟨pullback.snd f f ≫ u.val.1, by rw [Category.assoc, u.val.2]; exact pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst f f ≫ f) f) = pushPt u.val.1 u.val.2 Q :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, mapPt_coe, ← Category.assoc, pullback.lift_snd])
  rw [e1, e2] at h
  exact congrArg Subtype.val h

theorem isHom_bcHom_of_fst_comp_eq (u : Endo G)
    (h : pullback.fst (pullback.fst f f ≫ f) ι ≫ (mulMor G ≫ u.val.1) =
      pullback.fst (pullback.fst f f ≫ f) ι ≫ mulMorPush G u) :
    IsHom (bcHom ι G u) := by
  apply isHom_bcHom_of
  intro T t' P Q
  apply Subtype.ext
  have hπ₂ : pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ (pullback.fst f f ≫ f) = t' ≫ ι := by
    rw [← Category.assoc, pullback.lift_fst, P.2]
  have key := congrArg (fun k => pullback.lift (pullback.lift P.1 Q.1 (P.2.trans Q.2.symm)) t' hπ₂ ≫ k) h
  simp only [← Category.assoc, pullback.lift_fst] at key
  rw [lift_comp_mulMor, lift_comp_mulMorPush] at key
  exact key

theorem bcHom_eq_of_fst_comp_eq (u v : Endo G)
    (h : pullback.fst (pullback.fst f f ≫ f) ι ≫ (pullback.fst f f ≫ u.val.1) =
      pullback.fst (pullback.fst f f ≫ f) ι ≫ (pullback.fst f f ≫ v.val.1)) :
    bcHom ι G u = bcHom ι G v := by
  apply Endo.ext
  rw [bcHom_val_coe, bcHom_val_coe]
  apply pullback.hom_ext
  · rw [NoethBC20.bcEndo_fst, NoethBC20.bcEndo_fst]
    let δ : pullback f ι ⟶ pullback (pullback.fst f f ≫ f) ι :=
      pullback.lift (pullback.lift (pullback.fst f ι) (pullback.fst f ι) rfl) (pullback.snd f ι)
        (by rw [pullback.lift_fst_assoc]; exact pullback.condition)
    have key := congrArg (fun k => δ ≫ k) h
    simp only [δ, ← Category.assoc, pullback.lift_fst] at key
    simpa only [Category.assoc] using key
  · rw [NoethBC20.bcEndo_snd, NoethBC20.bcEndo_snd]

end EndKit19
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19"

namespace EndKit19

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {G : RelativeGroupLaw R f}
variable {S : Type u} [CommRing S] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of S)} {GX : RelativeGroupLaw S p}
variable {j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)} {g : X ⟶ A}

structure MulCompat (GX : RelativeGroupLaw S p) (G : RelativeGroupLaw R f) (j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
    (g : X ⟶ A) (hg : IsPullback g p f j) : Prop where
  out : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p),
    (GX.mul t P Q).1 ≫ g =
      (G.mul (t ≫ j) ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1

variable (hg : IsPullback g p f j)

def pushG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t p) : SchemeHomOver (t ≫ j) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem pushG_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t p) :
    (pushG hg P).1 = P.1 ≫ g := rfl

def liftG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver (t ≫ j) f) : SchemeHomOver t p :=
  ⟨hg.lift P.1 t P.2, hg.lift_snd _ _ _⟩

theorem pushG_liftG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver (t ≫ j) f) :
    pushG hg (liftG hg P) = P :=
  Subtype.ext (hg.lift_fst _ _ _)

theorem pushG_mul (hmul : MulCompat GX G j g hg) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P Q : SchemeHomOver t p) :
    pushG hg (GX.mul t P Q) = G.mul (t ≫ j) (pushG hg P) (pushG hg Q) :=
  Subtype.ext (hmul.out t P Q)

theorem pushG_one (hmul : MulCompat GX G j g hg) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushG hg (GX.one t) = G.one (t ≫ j) := by
  have h := pushG_mul hg hmul (GX.one t) (GX.one t)
  rw [GX.one_mul] at h
  have h2 : Pts.mk G (pushG hg (GX.one t)) * Pts.mk G (pushG hg (GX.one t)) = Pts.mk G (pushG hg (GX.one t)) * 1 := by
    rw [_root_.mul_one]; exact (congrArg (Pts.mk G) h).symm
  exact congrArg Pts.val (mul_left_cancel h2)

def pushGHom (hmul : MulCompat GX G j g hg) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) : Pts GX t →* Pts G (t ≫ j) :=
  { toFun := fun P => Pts.mk G (pushG hg P.val)
    map_one' := Pts.ext (congrArg Subtype.val (pushG_one hg hmul t))
    map_mul' := fun P Q => Pts.ext (congrArg Subtype.val (pushG_mul hg hmul P.val Q.val)) }

theorem pushGHom_val (hmul : MulCompat GX G j g hg) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : Pts GX t) :
    (pushGHom hg hmul t P).val = pushG hg P.val := rfl

theorem pushG_inv (hmul : MulCompat GX G j g hg) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t p) :
    pushG hg (GX.inv t P) = G.inv (t ≫ j) (pushG hg P) :=
  congrArg Pts.val (map_inv (pushGHom hg hmul t) (Pts.mk GX P))

def gPt : SchemeHomOver (p ≫ j) f := ⟨g, hg.w⟩

def relSubgroup (hmul : MulCompat GX G j g hg) : Subgroup (Endo GX × Endo G) :=
  MonoidHom.eqLocus ((pushGHom hg hmul p).comp (MonoidHom.fst _ _)) ((ev (gPt hg)).comp (MonoidHom.snd _ _))

theorem mem_relSubgroup_iff (hmul : MulCompat GX G j g hg) (q : Endo GX × Endo G) :
    q ∈ relSubgroup hg hmul ↔ q.1.val.1 ≫ g = g ≫ q.2.val.1 := by
  constructor
  · intro h
    have h' : (pushGHom hg hmul p) q.1 = ev (gPt hg) q.2 := h
    exact congrArg (fun P : Pts G (p ≫ j) => P.val.1) h'
  · intro h
    show (pushGHom hg hmul p) q.1 = ev (gPt hg) q.2
    exact Pts.ext h

theorem compE_mem_relSubgroup (hmul : MulCompat GX G j g hg) {uX vX : Endo GX} {u v : Endo G}
    (hu : (uX, u) ∈ relSubgroup hg hmul) (hv : (vX, v) ∈ relSubgroup hg hmul) :
    (compE uX vX, compE u v) ∈ relSubgroup hg hmul := by
  rw [mem_relSubgroup_iff] at *
  show (uX.val.1 ≫ vX.val.1) ≫ g = g ≫ (u.val.1 ≫ v.val.1)
  rw [Category.assoc, hv, ← Category.assoc, hu, Category.assoc]

theorem lin_mem_relSubgroup [IsComm GX] [IsComm G] (hmul : MulCompat GX G j g hg) {ι : Type} [Fintype ι]
    {ΦX : ι → Endo GX} {Φ : ι → Endo G} (h : ∀ i, (ΦX i, Φ i) ∈ relSubgroup hg hmul) (c : ι → ℤ) :
    (lin ΦX c, lin Φ c) ∈ relSubgroup hg hmul := by
  have e : (lin ΦX c, lin Φ c) = lin (fun i => (ΦX i, Φ i)) c := by
    ext
    · show lin ΦX c = (MonoidHom.fst _ _) (lin (fun i => (ΦX i, Φ i)) c); rw [map_lin]; rfl
    · show lin Φ c = (MonoidHom.snd _ _) (lin (fun i => (ΦX i, Φ i)) c); rw [map_lin]; rfl
  rw [e]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _ (h i) _

theorem hom_of_rel (hmul : MulCompat GX G j g hg) {uX : Endo GX} {u : Endo G} (hu : (uX, u) ∈ relSubgroup hg hmul) (hX : IsHom uX)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver (t ≫ j) f) :
    pushPt u.val.1 u.val.2 (G.mul _ P Q) = G.mul _ (pushPt u.val.1 u.val.2 P) (pushPt u.val.1 u.val.2 Q) := by
  rw [mem_relSubgroup_iff] at hu
  have eP : ∀ P' : SchemeHomOver t p, pushPt u.val.1 u.val.2 (pushG hg P') = pushG hg (pushPt uX.val.1 uX.val.2 P') :=
    fun P' => Subtype.ext (by simp only [mapPt_coe, pushG_coe, Category.assoc, hu])
  rw [← pushG_liftG hg P, ← pushG_liftG hg Q, ← pushG_mul hg hmul, eP, eP, eP, hX.out, pushG_mul hg hmul]

end EndKit19
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19"

namespace SpreadKit19

open NoethKit19 EndKit19

theorem stage_endos
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of A)} (GX : RelativeGroupLaw A p) (hX : AbelianSchemePropertyBundle A p)
    {ι : Type} [Finite ι] (φ : ι → (X ⟶ X)) (hφ : ∀ i, φ i ≫ p = p) :
    ∃ (T : Subalgebra A₀ A) (_ : T.FG)
      (A₁ : Scheme.{u}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥T)) (L₁ : RelativeGroupLaw ↥T f₁)
      (_ : AbelianSchemePropertyBundle ↥T f₁) (_ : GeometricallyConnected f₁) (_ : GX.IsCommutative → L₁.IsCommutative)
      (φ₁ : ι → (A₁ ⟶ A₁)) (_ : ∀ i, φ₁ i ≫ f₁ = f₁)
      (g : X ⟶ A₁) (hg : IsPullback g p f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))),
      MulCompat GX L₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) g hg ∧ (∀ i, φ i ≫ g = g ≫ φ₁ i) := by
  classical
  obtain ⟨R₁, hR₁fg, -, A₁, f₁, L₁, π, hπ, hb₁, hgc₁, hcomm₁, hmul₁⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
      (A₀ := A₀) GX hX ∅
  haveI : IsProper f₁ := hb₁.proper
  haveI : Smooth f₁ := hb₁.smooth
  haveI : GeometricallyConnected f₁ := hgc₁
  have he_snd : hπ.isoPullback.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ A))) = p :=
    hπ.isoPullback_hom_snd
  have he_inv_snd : hπ.isoPullback.inv ≫ p = pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ A))) := by
    rw [Iso.inv_comp_eq]; exact he_snd.symm
  have hgA : ∀ i, (hπ.isoPullback.inv ≫ φ i ≫ hπ.isoPullback.hom) ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ A))) =
      pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ A))) := by
    intro i; simp only [Category.assoc, he_snd, hφ i, he_inv_snd]
  obtain ⟨T, hTfg, -, g₀, hg₀, hcompat⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := ↥R₁) (A := A) (fun _ : ι => f₁) (fun _ : ι => f₁) (fun i => hπ.isoPullback.inv ≫ φ i ≫ hπ.isoPullback.hom) hgA ∅
  obtain ⟨r, hr_fst, hr_snd⟩ := exists_transition T f₁
  have hg := isPullback_comp_transition T f₁ π hπ r hr_fst hr_snd
  obtain ⟨hb₀, hgc₀⟩ := bundle_baseChange f₁ L₁ hb₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T)))
  have hfg : (T.restrictScalars A₀).FG := by
    have i1 : Algebra.FiniteType A₀ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 hR₁fg
    have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 hTfg
    have i3 : Algebra.FiniteType A₀ ↥T := Algebra.FiniteType.trans i1 i2
    exact (Subalgebra.fg_iff_finiteType (T.restrictScalars A₀)).2 i3
  refine ⟨T.restrictScalars A₀, hfg,
    pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T))), pullback.snd f₁ _, L₁.baseChange _, hb₀, hgc₀,
    fun hc => RelativeGroupLaw.IsCommutative.baseChange _ (hcomm₁ hc), g₀, hg₀, hπ.isoPullback.hom ≫ r, hg,
    ⟨fun t' P Q => mul_comp_transition T f₁ π hπ L₁ GX hmul₁ r hr_fst hr_snd t' P Q⟩, ?_⟩
  intro i
  rw [Category.assoc, hcompat i r r hr_fst hr_snd hr_fst hr_snd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SpreadKit19
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19"

namespace SpreadKit19

open NoethKit19 EndKit19

section Reflect2

variable {R : Type u} [CommRing R] {A₀s : Scheme.{u}} {f₀ : A₀s ⟶ Spec (CommRingCat.of R)} (L₀ : RelativeGroupLaw R f₀)
  {S : Type u} [CommRing S] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of S)} {GX : RelativeGroupLaw S p}
  {jm : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)} {g : X ⟶ A₀s} (hg : IsPullback g p f₀ jm)
  (hmc : MulCompat GX L₀ jm g hg)

theorem fst_comp_fst_comp_eq_of_rel {uX vX : Endo GX} {u v : Endo L₀} (hu : (uX, u) ∈ relSubgroup hg hmc)
    (hv : (vX, v) ∈ relSubgroup hg hmc) (he : uX.val.1 = vX.val.1) :
    pullback.fst (pullback.fst f₀ f₀ ≫ f₀) jm ≫ (pullback.fst f₀ f₀ ≫ u.val.1) =
      pullback.fst (pullback.fst f₀ f₀ ≫ f₀) jm ≫ (pullback.fst f₀ f₀ ≫ v.val.1) := by
  have hP : (pullback.fst (pullback.fst f₀ f₀ ≫ f₀) jm ≫ pullback.fst f₀ f₀) ≫ f₀ =
      pullback.snd (pullback.fst f₀ f₀ ≫ f₀) jm ≫ jm := by
    rw [Category.assoc]; exact pullback.condition
  let P : SchemeHomOver (pullback.snd (pullback.fst f₀ f₀ ≫ f₀) jm ≫ jm) f₀ := ⟨_, hP⟩
  have hPg : P.1 = (liftG hg P).1 ≫ g := (congrArg Subtype.val (pushG_liftG hg P)).symm
  rw [← Category.assoc, ← Category.assoc]
  show P.1 ≫ _ = P.1 ≫ _
  rw [hPg]
  rw [mem_relSubgroup_iff] at hu hv
  rw [Category.assoc, ← hu, Category.assoc, ← hv, he]

theorem fst_comp_mulMor_comp_eq_of_rel {uX : Endo GX} {u : Endo L₀} (hu : (uX, u) ∈ relSubgroup hg hmc) (hX : IsHom uX) :
    pullback.fst (pullback.fst f₀ f₀ ≫ f₀) jm ≫ (mulMor L₀ ≫ u.val.1) =
      pullback.fst (pullback.fst f₀ f₀ ≫ f₀) jm ≫ mulMorPush L₀ u := by
  have hP : (pullback.fst (pullback.fst f₀ f₀ ≫ f₀) jm ≫ pullback.fst f₀ f₀) ≫ f₀ =
      pullback.snd (pullback.fst f₀ f₀ ≫ f₀) jm ≫ jm := by
    rw [Category.assoc]; exact pullback.condition
  have hQ : (pullback.fst (pullback.fst f₀ f₀ ≫ f₀) jm ≫ pullback.snd f₀ f₀) ≫ f₀ =
      pullback.snd (pullback.fst f₀ f₀ ≫ f₀) jm ≫ jm := by
    rw [Category.assoc, ← pullback.condition]; exact hP
  let P : SchemeHomOver (pullback.snd (pullback.fst f₀ f₀ ≫ f₀) jm ≫ jm) f₀ := ⟨_, hP⟩
  let Q : SchemeHomOver (pullback.snd (pullback.fst f₀ f₀ ≫ f₀) jm ≫ jm) f₀ := ⟨_, hQ⟩
  have hw : pullback.fst (pullback.fst f₀ f₀ ≫ f₀) jm = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]
  rw [hw, ← Category.assoc, lift_comp_mulMor, lift_comp_mulMorPush]
  exact congrArg Subtype.val (hom_of_rel hg hmc hu hX _ P Q)

end Reflect2
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19"

theorem stage_autoHom
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of A)} (GX : RelativeGroupLaw A p) (hX : AbelianSchemePropertyBundle A p)
    (σ : X ⟶ X) (hσp : σ ≫ p = p) (hσiso : IsIso σ) (hσhom : IsHom (Endo.mk GX ⟨σ, hσp⟩)) :
    ∃ (T : Subalgebra A₀ A) (_ : T.FG)
      (A₁ : Scheme.{u}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥T)) (L₁ : RelativeGroupLaw ↥T f₁)
      (_ : AbelianSchemePropertyBundle ↥T f₁) (_ : GeometricallyConnected f₁) (_ : GX.IsCommutative → L₁.IsCommutative)
      (σ₁ : SchemeHomOver f₁ f₁) (_ : IsIso σ₁.1) (_ : IsHom (Endo.mk L₁ σ₁))
      (g : X ⟶ A₁) (hg : IsPullback g p f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))),
      MulCompat GX L₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) g hg ∧ σ ≫ g = g ≫ σ₁.1 := by
  classical
  have hιp : inv σ ≫ p = p := by rw [IsIso.inv_comp_eq, hσp]
  obtain ⟨T₁, hT₁fg, A₁, f₁, L₁, hb₁, hgc₁, hc₁, φ₁, hφ₁, g₁, hg₁, hmc₁, hcompat₁⟩ :=
    stage_endos (A₀ := A₀) GX hX (fun b : Bool => cond b σ (inv σ)) (fun b => by cases b <;> assumption)
  haveI : IsProper f₁ := hb₁.proper
  haveI : Smooth f₁ := hb₁.smooth
  haveI : LocallyOfFiniteType f₁ := inferInstance
  haveI : GeometricallyConnected f₁ := hgc₁

  let Φσ : Endo L₁ := Endo.mk L₁ ⟨φ₁ true, hφ₁ true⟩
  let Φι : Endo L₁ := Endo.mk L₁ ⟨φ₁ false, hφ₁ false⟩
  let Sσ : Endo GX := Endo.mk GX ⟨σ, hσp⟩
  let Sι : Endo GX := Endo.mk GX ⟨inv σ, hιp⟩
  have hrσ : (Sσ, Φσ) ∈ relSubgroup hg₁ hmc₁ := (mem_relSubgroup_iff hg₁ hmc₁ _).2 (hcompat₁ true)
  have hrι : (Sι, Φι) ∈ relSubgroup hg₁ hmc₁ := (mem_relSubgroup_iff hg₁ hmc₁ _).2 (hcompat₁ false)
  have hid : (idE GX, idE L₁) ∈ relSubgroup hg₁ hmc₁ := by
    rw [mem_relSubgroup_iff]; show 𝟙 X ≫ g₁ = g₁ ≫ 𝟙 A₁; rw [Category.id_comp, Category.comp_id]

  let a : Fin 3 → (pullback f₁ f₁ ⟶ A₁) :=
    ![mulMor L₁ ≫ Φσ.val.1, pullback.fst f₁ f₁ ≫ (compE Φσ Φι).val.1, pullback.fst f₁ f₁ ≫ (compE Φι Φσ).val.1]
  let b : Fin 3 → (pullback f₁ f₁ ⟶ A₁) :=
    ![mulMorPush L₁ Φσ, pullback.fst f₁ f₁ ≫ (idE L₁).val.1, pullback.fst f₁ f₁ ≫ (idE L₁).val.1]
  have ha : ∀ i, a i ≫ f₁ = pullback.fst f₁ f₁ ≫ f₁ := by
    intro i; fin_cases i
    · show (mulMor L₁ ≫ Φσ.val.1) ≫ f₁ = _; rw [Category.assoc, Φσ.val.2, mulMor_comp_f]
    · show (pullback.fst f₁ f₁ ≫ (compE Φσ Φι).val.1) ≫ f₁ = _; rw [Category.assoc, (compE Φσ Φι).val.2]
    · show (pullback.fst f₁ f₁ ≫ (compE Φι Φσ).val.1) ≫ f₁ = _; rw [Category.assoc, (compE Φι Φσ).val.2]
  have hb : ∀ i, b i ≫ f₁ = pullback.fst f₁ f₁ ≫ f₁ := by
    intro i; fin_cases i
    · show mulMorPush L₁ Φσ ≫ f₁ = _; rw [mulMorPush_comp_f]
    · show (pullback.fst f₁ f₁ ≫ (idE L₁).val.1) ≫ f₁ = _; rw [Category.assoc, (idE L₁).val.2]
    · show (pullback.fst f₁ f₁ ≫ (idE L₁).val.1) ≫ f₁ = _; rw [Category.assoc, (idE L₁).val.2]
  have hab : ∀ i, pullback.fst (pullback.fst f₁ f₁ ≫ f₁) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A))) ≫ a i =
      pullback.fst (pullback.fst f₁ f₁ ≫ f₁) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A))) ≫ b i := by
    intro i; fin_cases i
    · exact fst_comp_mulMor_comp_eq_of_rel L₁ hg₁ hmc₁ hrσ hσhom
    · exact fst_comp_fst_comp_eq_of_rel L₁ hg₁ hmc₁ (compE_mem_relSubgroup hg₁ hmc₁ hrσ hrι) hid (IsIso.hom_inv_id σ)
    · exact fst_comp_fst_comp_eq_of_rel L₁ hg₁ hmc₁ (compE_mem_relSubgroup hg₁ hmc₁ hrι hrσ) hid (IsIso.inv_hom_id σ)
  obtain ⟨T₂, hT₂fg, -, hT⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType (A₀ := ↥T₁) (A := A)
      (fun _ : Fin 3 => pullback.fst f₁ f₁ ≫ f₁) (fun _ => f₁) a b ha hb hab ∅

  let ι₂ := Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))
  have hhom : IsHom (bcHom (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) L₁ Φσ) :=
    isHom_bcHom_of_fst_comp_eq _ Φσ (hT 0)
  have h1 : compE (bcHom (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) L₁ Φσ)
      (bcHom (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) L₁ Φι) = idE _ := by
    have h := bcHom_eq_of_fst_comp_eq (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) (compE Φσ Φι) (idE L₁) (hT 1)
    rwa [bcHom_compE, bcHom_idE] at h
  have h2 : compE (bcHom (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) L₁ Φι)
      (bcHom (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) L₁ Φσ) = idE _ := by
    have h := bcHom_eq_of_fst_comp_eq (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) (compE Φι Φσ) (idE L₁) (hT 2)
    rwa [bcHom_compE, bcHom_idE] at h
  have hiso : IsIso (bcHom (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) L₁ Φσ).val.1 :=
    ⟨⟨(bcHom (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) L₁ Φι).val.1,
      congrArg (fun w : Endo _ => w.val.1) h1, congrArg (fun w : Endo _ => w.val.1) h2⟩⟩
  have hj : Spec.map (CommRingCat.ofHom T₂.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂)) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A)) := specMap_val_comp T₂
  have hgT := NoethBC20.isPullback_bcComparison (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) p
    (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A))) (Spec.map (CommRingCat.ofHom T₂.val.toRingHom)) hj g₁ hg₁
  obtain ⟨hbT, hgcT⟩ := bundle_baseChange f₁ L₁ hb₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂)))
  have hfg : (T₂.restrictScalars A₀).FG := by
    have i1 : Algebra.FiniteType A₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).1 hT₁fg
    have i2 : Algebra.FiniteType ↥T₁ ↥T₂ := (Subalgebra.fg_iff_finiteType _).1 hT₂fg
    have i3 : Algebra.FiniteType A₀ ↥T₂ := Algebra.FiniteType.trans i1 i2
    exact (Subalgebra.fg_iff_finiteType (T₂.restrictScalars A₀)).2 i3
  refine ⟨T₂.restrictScalars A₀, hfg, pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))), pullback.snd f₁ _,
    L₁.baseChange _, hbT, hgcT, fun hc => RelativeGroupLaw.IsCommutative.baseChange _ (hc₁ hc),
    (bcHom (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) L₁ Φσ).val, hiso, hhom,
    NoethBC20.bcComparison (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))) p
      (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A))) (Spec.map (CommRingCat.ofHom T₂.val.toRingHom)) hj g₁ hg₁,
    hgT, ⟨fun t' P Q => NoethBC20.mul_coe_comp_bcComparison _ p _ _ hj g₁ hg₁ GX L₁ hmc₁.out t' P Q⟩, ?_⟩
  exact NoethBC20.comp_bcComparison_eq_bcComparison_comp_bcEndo _ p _ _ hj g₁ hg₁ (φ₁ true) (hφ₁ true) σ hσp (hcompat₁ true)

end SpreadKit19
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Endo P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19.Pts P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso.EndKit19"

open scoped TensorProduct
open AlgebraicGeometry.PolarisedAbelianScheme NoethKit19 EndKit19 SpreadKit19

theorem solution
    {g d n : ℕ} {k : Type} [Field k] (u : PolarisedAbelianScheme g d n k)
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ (R : Subalgebra ℤ k) (_ : R.FG)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (σ₀ : SchemeHomOver f₀ f₀) (_ : IsIso σ₀.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (x y : SchemeHomOver t f₀),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) σ₀ =
          L₀.mul t (NeronModelInfra.schemeHomOverComp x σ₀) (NeronModelInfra.schemeHomOverComp y σ₀))
      (gA : u.A ⟶ A₀) (hg : CategoryTheory.IsPullback gA u.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
        (u.L.mul t x y).1 ≫ gA =
          (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      σ.1 ≫ gA = gA ≫ σ₀.1 := by
  classical
  have hσhom : IsHom (Endo.mk u.L ⟨σ.1, σ.2⟩) := ⟨fun t P Q => hσ t P Q⟩
  obtain ⟨T, hTfg, A₁, f₁, L₁, hb₁, hgc₁, -, σ₁, hiso, hhom, g, hg, hmc, hcompat⟩ :=
    stage_autoHom (A₀ := ℤ) u.L u.bundle σ.1 σ.2 hσiso hσhom
  exact ⟨T, hTfg, A₁, f₁, L₁, hb₁, hgc₁, σ₁, hiso, fun t x y => hhom.out t x y, g, hg, hmc.out, hcompat⟩

end
end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_comp_eq_comp_of_isIso (solution)
