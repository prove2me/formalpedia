-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4f9b8398-2a57-596f-8215-d5fef0b6e3d8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq
p2m_attr_erase "instance" "MvFormalGroup.instIsCommAddMv CerednikDrinfeld.BruhatTits.instGraphActionGLTree CerednikDrinfeld.BruhatTits.instMulActionGLVertex CerednikDrinfeld.BruhatTits.instGraphActionPGLTree CerednikDrinfeld.BruhatTits.instMulActionPGLVertex CerednikDrinfeld.Mumford.dartAction CerednikDrinfeld.FormalODModule.isComm MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid CerednikDrinfeld.ShimuraCurveModel.instFieldFc CerednikDrinfeld.ShimuraCurveModel.isCurveOverC CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeF CerednikDrinfeld.ShimuraCurveModel.instFieldF CerednikDrinfeld.ShimuraCurveModel.instAlgebraFbar CerednikDrinfeld.ShimuraCurveModel.instAlgebraFc CerednikDrinfeld.ShimuraCurveModel.instFieldFbar CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeC CerednikDrinfeld.ShimuraCurveModel.instFiniteTors CerednikDrinfeld.ShimuraCurveModel.isCurveOverF CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeBar CerednikDrinfeld.ShimuraCurveModel.isCurveOverBar CerednikDrinfeld.ShimuraCurveModel.instAlgebraF IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv"
p2m_attr_erase "instance" "AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CerednikDrinfeld.TwoPlaceTorsionDatum.instAddCommGroup CerednikDrinfeld.TwoPlaceTorsionDatum.instFinite CerednikDrinfeld.JPrimeTorsionDatum.instAddCommGroup CerednikDrinfeld.JPrimeTorsionDatum.instFinite kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec AlgebraicGeometry.Scheme.nilpPoints_map_val LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply CerednikDrinfeld.BruhatTits.vertPermHom_apply CerednikDrinfeld.BruhatTits.gl_smul_mk CerednikDrinfeld.BruhatTits.pgl_mk_smul CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply"
p2m_attr_erase "simp" "ModularCurve.degreeOn_apply CerednikDrinfeld.SpecialFormal.Rigidified.mk.injEq CerednikDrinfeld.FormalODModule.actRingHom_apply CerednikDrinfeld.SpecialFormalODModule.mk.sizeOf_spec CerednikDrinfeld.FormalODModule.Hom.mk.injEq CerednikDrinfeld.FormalODModule.map_id CerednikDrinfeld.SpecialFormal.Series.map_id CerednikDrinfeld.SpecialFormal.Rigidified.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.twist_obj CerednikDrinfeld.SpecialFormalODModule.mk.injEq CerednikDrinfeld.FormalODModule.map_varpi CerednikDrinfeld.FormalODModule.map_act CerednikDrinfeld.SpecialFormal.ModuliPackage.mk.injEq CerednikDrinfeld.FormalODModule.mk.injEq CerednikDrinfeld.FormalODModule.Hom.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.mk.sizeOf_spec CerednikDrinfeld.FormalODModule.map_F CerednikDrinfeld.SpecialFormal.Rigidified.map_n CerednikDrinfeld.SpecialFormal.Rigidified.map_ρ CerednikDrinfeld.SpecialFormal.IsLawHom.toHom_toPowerSeries CerednikDrinfeld.SpecialFormal.Series.map_ringHom_id CerednikDrinfeld.FormalODModule.actEnd_toPowerSeries CerednikDrinfeld.SpecialFormal.Rigidified.map_X CerednikDrinfeld.FormalODModule.varpiEnd_toPowerSeries CerednikDrinfeld.FormalODModule.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.mk.injEq CerednikDrinfeld.ShimuraCurveModel.coe_torsionHecke_apply CerednikDrinfeld.ShimuraCurveModel.galJ_apply CerednikDrinfeld.ShimuraCurveModel.heckeGenJ_apply CerednikDrinfeld.ShimuraCurveModel.coe_torsionGal_apply CerednikDrinfeld.ShimuraCurveModel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.signTwist_heckeGen CerednikDrinfeld.ShimuraCurveModel.coe_restrictTors_apply Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star ModularCurve.UniformizedHeckeCurve.mk.sizeOf_spec ModularCurve.UniformizedHeckeCurve.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul CerednikDrinfeld.TwoPlaceTorsionDatum.snd_T CerednikDrinfeld.TwoPlaceTorsionDatum.snd_toric CerednikDrinfeld.TwoPlaceTorsionDatum.mk.injEq CerednikDrinfeld.TwoPlaceTorsionDatum.fst_T CerednikDrinfeld.TwoPlaceTorsionDatum.mk.sizeOf_spec CerednikDrinfeld.TwoPlaceTorsionDatum.fst_D CerednikDrinfeld.TwoPlaceTorsionDatum.snd_D CerednikDrinfeld.TwoPlaceTorsionDatum.fst_toric ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd GoodReductionJacobian.BareDeformation.mk.sizeOf_spec GoodReductionJacobian.BareDeformation.mk.injEq GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace InvIsoDesc16

section Generic

universe w v' u' vv uu

p2m_open "Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

variable {C : Type uu} [Category.{vv} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

set_option backward.isDefEq.respectTransparency false in

theorem pullHom_map_gen {X Y Y' : C} {N N' : F.obj (.mk (op X))} (φ : N ⟶ N') (f₁ : Y ⟶ X) (g : Y' ⟶ Y)
    (g₁ : Y' ⟶ X) (hg₁ : g ≫ f₁ = g₁) :
    pullHom (F := F) (M₁ := N) (M₂ := N') (f₁ := f₁) (f₂ := f₁)
      ((F.map f₁.op.toLoc).toFunctor.map φ) g g₁ g₁ hg₁ hg₁ = (F.map g₁.op.toLoc).toFunctor.map φ := by
  dsimp only [pullHom]
  have nat := Pseudofunctor.mapComp'_hom_naturality F f₁.op.toLoc g.op.toLoc g₁.op.toLoc (by rw [← hg₁]; rfl) φ
  rw [← Category.assoc, ← nat]
  erw [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

theorem sandwich {D : Type*} [Category D] {P Q R S T : D} (a : P ⟶ Q) (x : Q ⟶ R) (bh : R ⟶ S) (bi : S ⟶ R)
    (hb : bh ≫ bi = 𝟙 R) (y : R ⟶ T) {V : D} (c : T ⟶ V) :
    (a ≫ x ≫ bh) ≫ (bi ≫ y ≫ c) = a ≫ (x ≫ y) ≫ c := by
  simp only [Category.assoc]
  rw [reassoc_of% hb]

set_option backward.isDefEq.respectTransparency false in

theorem comm_of_cover {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (M M' : F.obj (.mk (op S)))
    (e : ∀ i, ((F.toDescentData f).obj M).obj i ⟶ ((F.toDescentData f).obj M').obj i)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    {J : Type w} {U : J → C} (g : ∀ j, U j ⟶ Y)
    (hinj : ∀ (φ ψ : (F.map f₁.op.toLoc).toFunctor.obj (((F.toDescentData f).obj M).obj i₁) ⟶
        (F.map f₂.op.toLoc).toFunctor.obj (((F.toDescentData f).obj M').obj i₂)),
      (∀ j, (F.map (g j).op.toLoc).toFunctor.map φ = (F.map (g j).op.toLoc).toFunctor.map ψ) → φ = ψ)
    (g₂ : ∀ j, U j ⟶ X i₂) (hg₂ : ∀ j, g j ≫ f₂ = g₂ j)
    (hpiece : ∀ j,
      (F.map (g j ≫ f₁).op.toLoc).toFunctor.map (e i₁) ≫
          ((F.toDescentData f).obj M').hom (g j ≫ q) (i₁ := i₁) (i₂ := i₂) (g j ≫ f₁) (g₂ j)
            (by rw [Category.assoc, hf₁]) (by rw [← hg₂, Category.assoc, hf₂]) =
        ((F.toDescentData f).obj M).hom (g j ≫ q) (i₁ := i₁) (i₂ := i₂) (g j ≫ f₁) (g₂ j)
            (by rw [Category.assoc, hf₁]) (by rw [← hg₂, Category.assoc, hf₂]) ≫
          (F.map (g₂ j).op.toLoc).toFunctor.map (e i₂)) :
    (F.map f₁.op.toLoc).toFunctor.map (e i₁) ≫
        ((F.toDescentData f).obj M').hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ =
      ((F.toDescentData f).obj M).hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map (e i₂) := by
  apply hinj
  intro j

  refine (((F.map (g j).op.toLoc).toFunctor.map_comp _ _).trans ?_).trans ((F.map (g j).op.toLoc).toFunctor.map_comp _ _).symm
  have e1 := map_eq_pullHom ((F.map f₁.op.toLoc).toFunctor.map (e i₁)) (g j) (g j ≫ f₁) (g j ≫ f₁) rfl rfl
  have e1' := pullHom_map_gen F (e i₁) f₁ (g j) (g j ≫ f₁) rfl
  have e2 := map_eq_pullHom (((F.toDescentData f).obj M').hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂) (g j) (g j ≫ f₁) (g₂ j)
      rfl (hg₂ j)
  have e2' := ((F.toDescentData f).obj M').pullHom_hom (g j) q (g j ≫ q) rfl (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂
      (g j ≫ f₁) (g₂ j) rfl (hg₂ j)
  have e3 := map_eq_pullHom (((F.toDescentData f).obj M).hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂) (g j) (g j ≫ f₁) (g₂ j)
      rfl (hg₂ j)
  have e3' := ((F.toDescentData f).obj M).pullHom_hom (g j) q (g j ≫ q) rfl (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂
      (g j ≫ f₁) (g₂ j) rfl (hg₂ j)
  have e4 := map_eq_pullHom ((F.map f₂.op.toLoc).toFunctor.map (e i₂)) (g j) (g₂ j) (g₂ j) (hg₂ j) (hg₂ j)
  have e4' := pullHom_map_gen F (e i₂) f₂ (g j) (g₂ j) (hg₂ j)
  rw [e1'] at e1
  rw [e2'] at e2
  rw [e3'] at e3
  rw [e4'] at e4

  have L := (congrArg₂ (· ≫ ·) e1 e2).trans
    (sandwich _ _ _ _ (Cat.Hom.hom_inv_id_toNatTrans_app _ _) _ _)
  have R := (congrArg₂ (· ≫ ·) e3 e4).trans
    (sandwich _ _ _ _ (Cat.Hom.hom_inv_id_toNatTrans_app _ _) _ _)
  refine L.trans (Eq.trans ?_ R.symm)
  exact congrArg (fun t => _ ≫ t ≫ _) (hpiece j)

end Generic

theorem comp_toLoc {X Y Z : Scheme.{0}} (u : X ⟶ Y) (v : Y ⟶ Z) :
    v.op.toLoc ≫ u.op.toLoc = (u ≫ v).op.toLoc := rfl

theorem τl_eqToHom {B : Type*} [Bicategory B] {a b : Bicategory.Adj B} {u v : a ⟶ b} (h : u = v) :
    (eqToHom h).τl = eqToHom (congrArg (fun w : a ⟶ b => w.l) h) := by
  subst h
  simp

theorem toNatTrans_app_eqToHom {C D : Cat.{0, 1}} {u v : C ⟶ D} (h : u = v) (X : C) :
    (eqToHom h).toNatTrans.app X = eqToHom (by rw [h]) := by
  subst h
  simp

theorem L2core' {A : Scheme.{0}} (nn T : A ⟶ A) (fg : (LocallyDiscrete.mk (Opposite.op A)) ⟶ (LocallyDiscrete.mk (Opposite.op A)))
    (h : nn.op.toLoc ≫ T.op.toLoc = fg) (M : A.Modules) :
    (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).mapComp' nn.op.toLoc T.op.toLoc fg h).hom.toNatTrans.app M =
      eqToHom (by subst h; rfl) ≫ (Scheme.Modules.pullbackComp T nn).inv.app M := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.comp_mapComp]
  simp only [eqToHom_refl, Category.id_comp, Iso.trans_hom]
  simp [Bicategory.Adj.forget₁, Scheme.Modules.pseudofunctor_mapComp_hom_τl]
  rfl

theorem L2core {A : Scheme.{0}} (nn T : A ⟶ A) (hx : T ≫ nn = nn) (h₀₂ : nn.op.toLoc ≫ T.op.toLoc = nn.op.toLoc)
    (M : A.Modules) :
    (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).mapComp' nn.op.toLoc T.op.toLoc nn.op.toLoc h₀₂).hom.toNatTrans.app M = (transportIso hx M).inv := by
  rw [L2core' nn T nn.op.toLoc h₀₂ M]
  simp only [transportIso, Iso.trans_inv, Iso.app_inv, Scheme.Modules.pullbackCongr, eqToIso.inv, eqToHom_app]
  rfl

set_option backward.defeqAttrib.useBackward true in
theorem L2 {A : Scheme.{0}} (nn : A ⟶ A) (M : A.Modules) {Y : Scheme.{0}} (q g : Y ⟶ A) (T : A ⟶ A)
    (hx : T ≫ nn = nn) (hq : g ≫ nn = q) (hq' : (g ≫ T) ≫ nn = q) (i₁ i₂ : Unit) :
    ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => nn)).obj M).hom q (i₁ := i₁) (i₂ := i₂) g (g ≫ T) hq hq' =
      (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map g.op.toLoc).toFunctor.map (transportIso hx M).inv ≫
        (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).mapComp' T.op.toLoc g.op.toLoc (g ≫ T).op.toLoc (comp_toLoc g T)).inv.toNatTrans.app
          ((Scheme.Modules.pullback nn).obj M) := by
  have h₀₂ : nn.op.toLoc ≫ T.op.toLoc = nn.op.toLoc := by rw [comp_toLoc, hx]
  try simp only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom]
  rw [Pseudofunctor.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app ((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁) nn.op.toLoc T.op.toLoc g.op.toLoc
    nn.op.toLoc (g ≫ T).op.toLoc q.op.toLoc h₀₂ (comp_toLoc g T) (by rw [comp_toLoc, hq]) M]
  rw [L2core nn T hx h₀₂ M]
  rfl

theorem KT {A : Scheme.{0}} (nn : A ⟶ A) {M M' : A.Modules}
    (e₀ : (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map nn.op.toLoc).toFunctor.obj M ⟶ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map nn.op.toLoc).toFunctor.obj M')
    (T : A ⟶ A) (hx : T ≫ nn = nn)
    (hsq' : (transportIso hx M).inv ≫ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map T.op.toLoc).toFunctor.map e₀ = e₀ ≫ (transportIso hx M').inv)
    {Y : Scheme.{0}} (q g : Y ⟶ A) (hq : g ≫ nn = q) (hq' : (g ≫ T) ≫ nn = q) (i₁ i₂ : Unit) :
    (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map g.op.toLoc).toFunctor.map e₀ ≫
        ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => nn)).obj M').hom q (i₁ := i₁) (i₂ := i₂) g (g ≫ T) hq hq' =
      ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => nn)).obj M).hom q (i₁ := i₁) (i₂ := i₂) g (g ≫ T) hq hq' ≫
        (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (g ≫ T).op.toLoc).toFunctor.map e₀ := by
  rw [L2 nn M' q g T hx hq hq' i₁ i₂, L2 nn M q g T hx hq hq' i₁ i₂]
  erw [Category.assoc]
  erw [← Pseudofunctor.mapComp'_inv_naturality ((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁) T.op.toLoc g.op.toLoc (g ≫ T).op.toLoc (comp_toLoc g T) e₀]
  have E := congrArg (fun φ => φ ≫ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).mapComp' T.op.toLoc g.op.toLoc (g ≫ T).op.toLoc (comp_toLoc g T)).inv.toNatTrans.app
      ((Scheme.Modules.pullback nn).obj M')) (((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map g.op.toLoc).toFunctor.congr_map hsq').symm)
  have mc₁ := (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map g.op.toLoc).toFunctor.map_comp e₀ (transportIso hx M').inv
  have mc₂ := (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map g.op.toLoc).toFunctor.map_comp (transportIso hx M).inv ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map T.op.toLoc).toFunctor.map e₀)
  beta_reduce at E
  have E' := ((congrArg (fun φ => φ ≫ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).mapComp' T.op.toLoc g.op.toLoc (g ≫ T).op.toLoc (comp_toLoc g T)).inv.toNatTrans.app
      ((Scheme.Modules.pullback nn).obj M')) mc₁).symm.trans E).trans
    (congrArg (fun φ => φ ≫ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).mapComp' T.op.toLoc g.op.toLoc (g ≫ T).op.toLoc (comp_toLoc g T)).inv.toNatTrans.app
      ((Scheme.Modules.pullback nn).obj M')) mc₂)
  beta_reduce at E'
  first
    | simpa only [Category.assoc] using E'
    | (have h' := E'; simp only [Category.assoc] at h' ⊢; exact h')
    | (have h' := E'; simp only [Category.assoc] at h'; exact h')
    | exact E'

set_option maxHeartbeats 6400000 in

theorem keyLemma
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 𝓜' : A.Modules)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (e₀ : (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (L.schemeNsmul n).op.toLoc).toFunctor.obj 𝓜 ⟶ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (L.schemeNsmul n).op.toLoc).toFunctor.obj 𝓜')
    (HSQ : ∀ (P : L.AlgPoints hc k), n • P = 0 →
      ∀ (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n),
        (transportIso hx 𝓜).inv ≫ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (translation f L (RelativeGroupLaw.AlgPoints.toPoint P)).op.toLoc).toFunctor.map e₀ =
          e₀ ≫ (transportIso hx 𝓜').inv)
    ⦃Y : Scheme.{0}⦄ (q : Y ⟶ A) ⦃i₁ i₂ : Unit⦄ (f₁ f₂ : Y ⟶ A)
    (hf₁ : f₁ ≫ (fun _ : Unit => L.schemeNsmul n) i₁ = q) (hf₂ : f₂ ≫ (fun _ : Unit => L.schemeNsmul n) i₂ = q) :
    (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₁.op.toLoc).toFunctor.map e₀ ≫
        ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => L.schemeNsmul n)).obj 𝓜').hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ =
      ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => L.schemeNsmul n)).obj 𝓜).hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ ≫
        (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₂.op.toLoc).toFunctor.map e₀ := by
  classical
  have hf₁' : f₁ ≫ L.schemeNsmul n = q := hf₁
  have hf₂' : f₂ ≫ L.schemeNsmul n = q := hf₂
  obtain ⟨U, hU, hUrel⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq
      k f L hc hA g hdim n hn f₁ f₂ (hf₁'.trans hf₂'.symm)

  have hcov : ∀ y : ↥Y, ∃ P, y ∈ Set.range (U P).ι.base := by
    intro y
    have hy : y ∈ ((⨆ P, U P : Y.Opens) : Set ↥Y) := by rw [hU]; trivial
    obtain ⟨P, hP⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨P, by rw [Scheme.Opens.range_ι]; exact hP⟩
  have hinj := (AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover (fun P => (U P).ι) hcov
      ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₁.op.toLoc).toFunctor.obj ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓜))
      ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₂.op.toLoc).toFunctor.obj ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓜'))).1

  have hinj' : ∀ (φ ψ : (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₁.op.toLoc).toFunctor.obj (((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => L.schemeNsmul n)).obj 𝓜).obj i₁) ⟶
      (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₂.op.toLoc).toFunctor.obj (((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => L.schemeNsmul n)).obj 𝓜').obj i₂)),
      (∀ P, (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (U P).ι.op.toLoc).toFunctor.map φ = (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (U P).ι.op.toLoc).toFunctor.map ψ) → φ = ψ := by
    intro φ ψ hφψ
    apply hinj
    apply Pseudofunctor.DescentData.hom_ext
    intro P
    simp only [Pseudofunctor.toDescentData_map_hom]
    exact hφψ P
  refine comm_of_cover ((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁) (fun _ : Unit => L.schemeNsmul n) 𝓜 𝓜' (fun _ => e₀) q f₁ f₂ hf₁ hf₂
    (fun P => (U P).ι) hinj'
    (fun P => ((U P).ι ≫ f₁) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P.1)) ?_ ?_
  · intro P
    show (U P).ι ≫ f₂ = ((U P).ι ≫ f₁) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P.1)
    rw [Category.assoc]
    exact hUrel P
  · intro P
    have hP : n • P.1 = 0 := P.2
    have hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P.1) ≫ L.schemeNsmul n = L.schemeNsmul n :=
      AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero k f L hc P.1 n hP
    have hq₁ : ((U P).ι ≫ f₁) ≫ L.schemeNsmul n = (U P).ι ≫ q := by rw [Category.assoc, hf₁']
    have hq₂ : (((U P).ι ≫ f₁) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P.1)) ≫ L.schemeNsmul n = (U P).ι ≫ q := by
      rw [Category.assoc, hx, Category.assoc, hf₁']
    exact KT (L.schemeNsmul n) e₀ (translation f L (RelativeGroupLaw.AlgPoints.toPoint P.1)) hx (HSQ P.1 hP hx)
      ((U P).ι ≫ q) ((U P).ι ≫ f₁) hq₁ hq₂ i₁ i₂

end InvIsoDesc16

set_option maxHeartbeats 6400000 in
open InvIsoDesc16 in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 𝓜' : A.Modules)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (e₀ : (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (L.schemeNsmul n).op.toLoc).toFunctor.obj 𝓜 ⟶ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (L.schemeNsmul n).op.toLoc).toFunctor.obj 𝓜')
    (HSQ : ∀ (P : L.AlgPoints hc k), n • P = 0 →
      ∀ (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n),
        (transportIso hx 𝓜).inv ≫ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (translation f L (RelativeGroupLaw.AlgPoints.toPoint P)).op.toLoc).toFunctor.map e₀ =
          e₀ ≫ (transportIso hx 𝓜').inv)
    ⦃Y : Scheme.{0}⦄ (q : Y ⟶ A) ⦃i₁ i₂ : Unit⦄ (f₁ f₂ : Y ⟶ A)
    (hf₁ : f₁ ≫ (fun _ : Unit => L.schemeNsmul n) i₁ = q) (hf₂ : f₂ ≫ (fun _ : Unit => L.schemeNsmul n) i₂ = q) :
    (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₁.op.toLoc).toFunctor.map e₀ ≫
        ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => L.schemeNsmul n)).obj 𝓜').hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ =
      ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => L.schemeNsmul n)).obj 𝓜).hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ ≫
        (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₂.op.toLoc).toFunctor.map e₀ := by
  exact keyLemma k f L hc hA 𝓜 𝓜' g hdim n hn e₀ HSQ q f₁ f₂ hf₁ hf₂

end S_AlgebraicGeometry_RiemannForm_map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq (solution)
