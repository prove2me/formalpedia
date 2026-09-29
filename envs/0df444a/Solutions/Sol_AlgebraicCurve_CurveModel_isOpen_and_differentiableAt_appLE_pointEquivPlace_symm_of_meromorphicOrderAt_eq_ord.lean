-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/16909426-f52d-59c0-8a39-ad052bdc7ff9

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve Topology
open scoped Manifold ContDiff

namespace SecHolo16

variable {F : Type} [Field F] [Algebra ℂ F]

theorem base_closedPoint_mem_iff {X : Scheme.{0}} (p : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens) :
    ⊤ ≤ p ⁻¹ᵁ U ↔ p.base (IsLocalRing.closedPoint ℂ) ∈ U := by
  constructor
  · intro h
    have : IsLocalRing.closedPoint ℂ ∈ p ⁻¹ᵁ U := h (Set.mem_univ _)
    exact this
  · intro h
    rw [Scheme.preimage_eq_top_of_closedPoint_mem p h]

theorem evalAt_sub_algebraMap (v : Place ℂ F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hc : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hfc : f - algebraMap ℂ F c ∈ v.toValuationSubring := v.toValuationSubring.toSubring.sub_mem hf hc
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hfc, v.algebraMap_evalAt hv hf]
  have : (⟨f - algebraMap ℂ F c, hfc⟩ : v.toValuationSubring) = ⟨f, hf⟩ - algebraMap ℂ v.toValuationSubring c := by
    apply Subtype.ext; rfl
  rw [this, map_sub]
  rfl

end SecHolo16

open SecHolo16 in
theorem solution
    (F : Type) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (M : CurveModel ℂ F)
    (U : M.C.Opens) (t : Γ(M.C, U)) :
    IsOpen {v : Place ℂ F | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U} ∧
      ∃ G : Place ℂ F → ℂ,
        (∀ (v : Place ℂ F) (h : ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U),
          G v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((M.pointEquivPlace.symm v).1.appLE U ⊤ h) t)) ∧
        ∀ v : Place ℂ F, ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U →
          DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) := by
  classical

  have hx : ∀ v, M.pointEquivPlace (M.pointEquivPlace.symm v) = v := fun v => by simp

  have hS : ∀ v, (⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U ↔ (M.pointEquivPlace.symm v).1.base (IsLocalRing.closedPoint ℂ) ∈ U) :=
    fun v => base_closedPoint_mem_iff (M.pointEquivPlace.symm v).1 U

  have hopen : IsOpen {v : Place ℂ F | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U} := by
    by_cases hU : (U : Set M.C).Nonempty
    · haveI : QuasiCompact M.toBase := inferInstance
      have hfin : ((U : Set M.C)ᶜ).Finite := AlgebraicCurve.finite_compl_of_isOpen M.toBase U hU

      have hinj : Function.Injective (fun v : Place ℂ F => (M.pointEquivPlace.symm v).1.base (IsLocalRing.closedPoint ℂ)) := by
        intro v w hvw
        have := (pointEquivClosedPoint M.toBase).injective
          (a₁ := M.pointEquivPlace.symm v) (a₂ := M.pointEquivPlace.symm w) (Subtype.ext hvw)
        have := congrArg M.pointEquivPlace this
        rwa [hx, hx] at this
      have hcf : ({v : Place ℂ F | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U}ᶜ).Finite := by
        have : {v : Place ℂ F | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U}ᶜ =
            (fun v : Place ℂ F => (M.pointEquivPlace.symm v).1.base (IsLocalRing.closedPoint ℂ)) ⁻¹' ((U : Set M.C)ᶜ) := by
          ext v; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage, hS v]; rfl
        rw [this]
        exact hfin.preimage (hinj.injOn)
      have : IsClosed ({v : Place ℂ F | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U}ᶜ) := hcf.isClosed
      simpa using this
    · have : {v : Place ℂ F | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U} = ∅ := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hU ⟨_, (hS v).1 h⟩
      rw [this]; exact isOpen_empty
  refine ⟨hopen, ⟨fun v => if hv : ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U then
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((M.pointEquivPlace.symm v).1.appLE U ⊤ hv) t) else 0, ?_, ?_⟩⟩
  · intro v hv; simp only [dif_pos hv]
  · intro v₀ hv₀
    have hx₀ : (M.pointEquivPlace.symm v₀).1.base (IsLocalRing.closedPoint ℂ) ∈ U := (hS v₀).1 hv₀
    haveI : Nonempty U := ⟨⟨_, hx₀⟩⟩

    set f : F := M.ffEquiv.symm (M.C.germToFunctionField U t) with hf

    have hval : ∀ (v : Place ℂ F) (hv : ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U),
        f ∈ v.toValuationSubring ∧
        v.evalAt f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((M.pointEquivPlace.symm v).1.appLE U ⊤ hv) t) := by
      intro v hv
      have hxU : (M.pointEquivPlace.symm v).1.base (IsLocalRing.closedPoint ℂ) ∈ U := (hS v).1 hv
      obtain ⟨hmem, -, hev⟩ :=
        AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo M (M.pointEquivPlace.symm v)
          (M.C.presheaf.germ U _ hxU t)
      have hgerm : (algebraMap (M.C.presheaf.stalk ((M.pointEquivPlace.symm v).1.base (IsLocalRing.closedPoint ℂ))) M.C.functionField)
          (M.C.presheaf.germ U _ hxU t) = M.C.germToFunctionField U t := by
        letI := M.C.presheaf.algebra_section_stalk (⟨_, hxU⟩ : U)
        haveI hst := functionField_isScalarTower M.C U ⟨_, hxU⟩
        have h1 := (IsScalarTower.algebraMap_apply Γ(M.C, U)
          (M.C.presheaf.stalk (((⟨_, hxU⟩ : U) : M.C))) M.C.functionField t).symm
        exact h1
      rw [hgerm, hx] at hmem hev
      refine ⟨hmem, ?_⟩
      rw [hev]

      have key := Scheme.germ_stalkClosedPointTo (M.pointEquivPlace.symm v).1 U hxU
      have := congrArg (fun φ => φ.hom t) key
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      rw [show (M.C.presheaf.germ U _ hxU t) = (M.C.presheaf.germ U _ hxU).hom t from rfl] at *
      rw [this]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE]
      rfl

    have heval_const : ∀ (v : Place ℂ F) (c : ℂ), v.evalAt (algebraMap ℂ F c) = c := by
      intro v c
      have hv := AlgebraicCurve.CurveModel.isRational_pointEquivPlace M (M.pointEquivPlace.symm v)
      rw [hx] at hv
      apply v.algebraMap_residueField_injective
      rw [v.algebraMap_evalAt hv (v.algebraMap_mem' c)]
      have : (⟨algebraMap ℂ F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) = algebraMap ℂ v.toValuationSubring c :=
        Subtype.ext rfl
      rw [this]; rfl
    have hrat : ∀ v : Place ℂ F, v.IsRational := fun v => by
      have hv := AlgebraicCurve.CurveModel.isRational_pointEquivPlace M (M.pointEquivPlace.symm v)
      rwa [hx] at hv
    set c₀ : ℂ := extChartAt 𝓘(ℂ, ℂ) v₀ v₀ with hc₀
    set c : ℂ := v₀.evalAt f with hc
    have hsymm0 : (extChartAt 𝓘(ℂ, ℂ) v₀).symm c₀ = v₀ := by rw [hc₀]; exact extChartAt_to_inv (I := 𝓘(ℂ, ℂ)) v₀

    have hN : (extChartAt 𝓘(ℂ, ℂ) v₀).symm ⁻¹' {v : Place ℂ F | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ U} ∈ 𝓝 c₀ := by
      apply (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v₀).preimage_mem_nhds
      rw [hsymm0]; exact hopen.mem_nhds hv₀

    have heq : (fun z : ℂ => (if hv : ⊤ ≤ (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)).1 ⁻¹ᵁ U then
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z))).1.appLE U ⊤ hv) t)
          else 0)) =ᶠ[𝓝 c₀]
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z) (f - algebraMap ℂ F c) + c) := by
      filter_upwards [hN] with z hz
      have hz' : ⊤ ≤ (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)).1 ⁻¹ᵁ U := hz
      obtain ⟨hmemz, hvalz⟩ := hval _ hz'
      rw [dif_pos hz', ← hvalz, evalAt_sub_algebraMap _ (hrat _) hmemz c]
      ring
    refine (Filter.EventuallyEq.differentiableAt_iff heq).2 ?_
    by_cases hf0 : f - algebraMap ℂ F c = 0
    ·
      have : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z) (f - algebraMap ℂ F c) + c) = fun _ => c := by
        funext z; rw [hf0, show (0 : F) = algebraMap ℂ F 0 from (map_zero _).symm, heval_const]; simp
      rw [this]; exact differentiableAt_const c
    ·
      obtain ⟨hmer, hord⟩ := hF (f - algebraMap ℂ F c) hf0 v₀
      obtain ⟨hmem0, hval0⟩ := hval v₀ hv₀
      have hmem0' : f - algebraMap ℂ F c ∈ v₀.toValuationSubring :=
        v₀.toValuationSubring.toSubring.sub_mem hmem0 (v₀.algebraMap_mem' c)
      have hzero : v₀.evalAt (f - algebraMap ℂ F c) = 0 := by
        rw [evalAt_sub_algebraMap _ (hrat _) hmem0 c, hc]; ring
      have hord1 : 1 ≤ v₀.ord (f - algebraMap ℂ F c) :=
        (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord v₀ (hrat v₀) hf0 hmem0').1 hzero
      have hpos : 0 < meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z) (f - algebraMap ℂ F c)) c₀ := by
        rw [hc₀, hord]
        exact_mod_cast hord1
      have hval_c₀ : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v₀).symm c₀) (f - algebraMap ℂ F c) = 0 := by
        rw [hsymm0]; exact hzero
      have han : AnalyticAt ℂ (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z) (f - algebraMap ℂ F c)) c₀ :=
        AnalyticAt.of_meromorphicOrderAt_pos hpos hval_c₀
      exact han.differentiableAt.add (differentiableAt_const c)

end S_AlgebraicCurve_CurveModel_isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord (solution)
