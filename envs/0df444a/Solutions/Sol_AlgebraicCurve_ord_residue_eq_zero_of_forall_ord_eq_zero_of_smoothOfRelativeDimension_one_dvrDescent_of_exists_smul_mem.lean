-- Prove2me | solution 1 for AlgebraicCurve.ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/42c6d960-b0cc-53c6-9de6-996f9d6ce93a

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
import Theorems.Thm_NeronModelInfra_existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring
import Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
import Theorems.Thm_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring
import Theorems.Thm_AlgebraicCurve_mem_localRing_of_mem_integers_of_forall_mem_valuationSubring_of_mem_smoothLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve TopologicalSpace

universe v w

namespace GC3b21

open IsLocalRing

theorem rankOne_and_ne_univ_of_liesOverPrime (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime)
    (hO : O.LiesOverPrime p) :
    (∀ a b : ↥O, a ∈ maximalIdeal ↥O → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n) ∧ ((O : Set (AlgebraicClosure ℚ)) ≠ Set.univ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun a b ha hb => ?_, fun huniv => ?_⟩
  · by_cases ha0 : a = 0
    · exact ⟨1, by simp [ha0]⟩
    · exact ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal O hO b hb a ha ha0
  · have hpO : (p : AlgebraicClosure ℚ) ∈ O := O.nonunits_le hO
    have hpm : (⟨(p : AlgebraicClosure ℚ), hpO⟩ : ↥O) ∈ maximalIdeal ↥O := (ValuationSubring.coe_mem_nonunits_iff).mp hO
    have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hinv : (p : AlgebraicClosure ℚ)⁻¹ ∈ O := by
      have : (p : AlgebraicClosure ℚ)⁻¹ ∈ (O : Set (AlgebraicClosure ℚ)) := huniv.symm ▸ Set.mem_univ _
      exact this
    apply (IsLocalRing.mem_maximalIdeal _).mp hpm
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    simp [mul_inv_cancel₀ hp0]

theorem isUnit_iff_residue_ne_zero {F K : Type*} [Field F] [Field K] (𝒪 : ValuationSubring F) (res : ↥𝒪 →+* K)
    (hker : RingHom.ker res = maximalIdeal ↥𝒪) (g : ↥𝒪) : IsUnit g ↔ res g ≠ 0 := by
  rw [ne_eq, ← RingHom.mem_ker, hker]
  exact ⟨fun hu hm => (IsLocalRing.mem_maximalIdeal _).mp hm hu,
    fun h => by by_contra hu; exact h ((IsLocalRing.mem_maximalIdeal _).mpr hu)⟩

end GC3b21

namespace GC3b21

theorem mem_of_ord_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ≠ 0) (h : v.ord f = 0) : f ∈ v.toValuationSubring := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥v.toValuationSubring)
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
  rw [h, zpow_zero, mul_one] at hu
  rw [hu]
  exact (u : ↥v.toValuationSubring).2

end GC3b21

namespace GC3b21

theorem genericPoint_ne_of_mem_closedPoints {K : Type} [Field K] {L : Type*} [Field L] [Algebra K L]
    (M : CurveModel K L) (x : ↥M.C) (hx : x ∈ closedPoints ↥M.C) : x ≠ genericPoint ↥M.C := by
  intro h
  apply (M.placeOfPoint ⟨x, hx⟩).ne_top'
  have hsurj : Function.Surjective (algebraMap (M.C.presheaf.stalk x) M.C.functionField) := by
    intro w
    have e : Inseparable x (genericPoint ↥M.C) := Inseparable.of_eq h
    refine ⟨(M.C.presheaf.stalkCongr e).inv w, ?_⟩
    rw [RingHom.algebraMap_toAlgebra]
    exact CategoryTheory.Iso.inv_hom_id_apply (M.C.presheaf.stalkCongr e) w
  ext z
  simp only [ValuationSubring.mem_top, iff_true]
  have hz : z ∈ (M.placeOfPoint ⟨x, hx⟩).toValuationSubring.toSubring := by
    rw [← M.range_stalk_eq ⟨x, hx⟩]
    obtain ⟨s, hs⟩ := hsurj (M.ffEquiv z)
    exact ⟨s, by simp [hs]⟩
  exact hz

end GC3b21

namespace GC3b21

universe u in

private theorem _root_.GC3b21.algebraMap_germ {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : ↥X) (hx : x ∈ U) [Nonempty U]
    (s : X.presheaf.obj (Opposite.op U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = X.germToFunctionField U s := by
  rw [RingHom.algebraMap_toAlgebra]
  change (X.presheaf.germ U x hx ≫ X.presheaf.stalkSpecializes _).hom s = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

p2m_export "GC3b21" "algebraMap_germ"
universe u in

theorem germToFunctionField_app_baseSection {Y X : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    {R S : Type u} [CommRing R] [CommRing S] (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of S))
    (ι : R →+* S) (hsq : g ≫ πX = πY ≫ Spec.map (CommRingCat.ofHom ι)) (a : R)
    [Nonempty (g ⁻¹ᵁ (⊤ : X.Opens))] :
    Y.germToFunctionField (g ⁻¹ᵁ ⊤) ((g.app ⊤) (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) =
      SemistableModel.baseToFunctionField πY (ι a) := by
  have h2 : g.appTop (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) =
      πY.appTop ((Spec.map (CommRingCat.ofHom ι)).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) := by
    have := congrArg (fun g' => (Scheme.Hom.appTop g').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) hsq
    simpa [Scheme.Hom.comp_appTop] using this
  have h3 : (Spec.map (CommRingCat.ofHom ι)).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (ι a) := by
    have := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι))) a
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  change (Y.presheaf.germ ⊤ (genericPoint ↥Y) _).hom (g.appTop (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) =
    (Y.presheaf.germ ⊤ (genericPoint ↥Y) trivial).hom (πY.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv (ι a)))
  rw [h2, h3]

universe u in

theorem nonempty_preimage_of_mem {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] [IsIntegral Y] [IsIntegral X]
    (U : X.Opens) (x : ↥X) (hx : x ∈ U) : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint ↥Y, ?_⟩⟩
  show f.base (genericPoint ↥Y) ∈ U
  rw [genericPoint_eq_of_isOpenImmersion]
  exact ((genericPoint_spec ↥X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

end GC3b21

namespace GC3b21

open IsLocalRing

section Base

variable (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ)

theorem isLocalization_away (hO : O.LiesOverPrime p)
    (hrk : ∀ a b : ↥O, a ∈ maximalIdeal ↥O → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n) (hp : p.Prime) :
    IsLocalization.Away ((⟨(p : AlgebraicClosure ℚ), O.nonunits_le hO⟩ : ↥O)) (AlgebraicClosure ℚ) := by
  set p' : ↥O := ⟨(p : AlgebraicClosure ℚ), O.nonunits_le hO⟩ with hp'
  have hpm : p' ∈ maximalIdeal ↥O := (ValuationSubring.coe_mem_nonunits_iff).mp hO
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [map_pow]
    exact pow_ne_zero _ (by simpa [hp'] using hp0)
  · intro z
    by_cases hz : z ∈ O
    · exact ⟨(⟨z, hz⟩, 1), by simp⟩
    · have hz0 : z ≠ 0 := fun h => hz (h ▸ O.zero_mem)
      have hzi : z⁻¹ ∈ O := (O.mem_or_inv_mem z).resolve_left hz
      have hb : (⟨z⁻¹, hzi⟩ : ↥O) ≠ 0 := by
        simp only [ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]; exact inv_ne_zero hz0
      obtain ⟨n, c, hc⟩ := hrk p' ⟨z⁻¹, hzi⟩ hpm hb
      refine ⟨(c, ⟨p' ^ n, n, rfl⟩), ?_⟩
      have hc' : ((p' : ↥O) : AlgebraicClosure ℚ) ^ n = z⁻¹ * (c : AlgebraicClosure ℚ) := by
        have h1 := congrArg (fun t : ↥O => (t : AlgebraicClosure ℚ)) hc
        simpa using h1
      show z * algebraMap (↥O) (AlgebraicClosure ℚ) (p' ^ n) = algebraMap (↥O) (AlgebraicClosure ℚ) c
      simp only [map_pow]
      change z * (p' : AlgebraicClosure ℚ) ^ n = (c : AlgebraicClosure ℚ)
      rw [hc', ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  · intro x y hxy
    exact ⟨1, by simpa using Subtype.ext hxy⟩

theorem isOpenImmersion_specMap_subtype (hO : O.LiesOverPrime p)
    (hrk : ∀ a b : ↥O, a ∈ maximalIdeal ↥O → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n) (hp : p.Prime) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) := by
  haveI := isLocalization_away O p hO hrk hp
  exact IsOpenImmersion.of_isLocalization (R := ↥O) (S := AlgebraicClosure ℚ)
    ((⟨(p : AlgebraicClosure ℚ), O.nonunits_le hO⟩ : ↥O))

end Base

section FF

universe u

noncomputable def ffIso {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] [IsIntegral Y] [IsIntegral X] :
    X.functionField ≅ Y.functionField :=
  X.presheaf.stalkCongr (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion f).symm) ≪≫
    asIso (f.stalkMap (genericPoint ↥Y))

theorem germToFunctionField_ffIso_hom {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] [IsIntegral Y] [IsIntegral X]
    (U : X.Opens) [hU : Nonempty U] [hV : Nonempty (f ⁻¹ᵁ U)] :
    X.germToFunctionField U ≫ (ffIso f).hom = f.app U ≫ Y.germToFunctionField (f ⁻¹ᵁ U) := by
  simp only [ffIso, Scheme.germToFunctionField, Iso.trans_hom, asIso_hom, TopCat.Presheaf.stalkCongr]
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]

theorem ffIso_hom_germToFunctionField {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] [IsIntegral Y] [IsIntegral X]
    (U : X.Opens) [hU : Nonempty U] [hV : Nonempty (f ⁻¹ᵁ U)] (s : X.presheaf.obj (Opposite.op U)) :
    (ffIso f).hom (X.germToFunctionField U s) = Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  have h := germToFunctionField_ffIso_hom f U
  have h2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) s
  simpa using h2

theorem germTop_ffIso_hom {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] [IsIntegral Y] [IsIntegral X] :
    X.presheaf.germ ⊤ (genericPoint X) trivial ≫ (ffIso f).hom = f.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) trivial := by
  simp only [ffIso, Iso.trans_hom, asIso_hom, TopCat.Presheaf.stalkCongr]
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact Scheme.Hom.germ_stalkMap f ⊤ (genericPoint Y) trivial

theorem ffIso_hom_baseToFunctionField {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] [IsIntegral Y] [IsIntegral X]
    {R S : Type u} [CommRing R] [CommRing S] (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of S))
    (ι : R →+* S) (hsq : f ≫ πX = πY ≫ Spec.map (CommRingCat.ofHom ι)) (a : R) :
    (ffIso f).hom (SemistableModel.baseToFunctionField πX a) = SemistableModel.baseToFunctionField πY (ι a) := by
  simp only [SemistableModel.baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  have h1 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (germTop_ffIso_hom f))
    (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1
  rw [h1]
  have h2 : f.appTop (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) =
      πY.appTop ((Spec.map (CommRingCat.ofHom ι)).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) := by
    have := congrArg (fun g => (Scheme.Hom.appTop g).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) hsq
    simpa [Scheme.Hom.comp_appTop] using this
  have h3 : (Spec.map (CommRingCat.ofHom ι)).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (ι a) := by
    have := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι))) a
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  rw [h2, h3]

end FF

end GC3b21

namespace GC3b21

open IsLocalRing

theorem residue_eq_residue_iff {R : Type*} [CommRing R] [IsLocalRing R] (x y : R) :
    IsLocalRing.residue R x = IsLocalRing.residue R y ↔ x - y ∈ maximalIdeal R := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

section Transport

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F] {F₀ : Type*} [Field F₀] [Algebra K F₀]

noncomputable def comapPlace (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) : Place K F where
  toValuationSubring := P₀.toValuationSubring.comap (φ : F →+* F₀)
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap]
    simpa using P₀.algebraMap_mem' a
  ne_top' := by
    intro h
    apply P₀.ne_top'
    ext y
    simp only [ValuationSubring.mem_top, iff_true]
    have : φ.symm y ∈ P₀.toValuationSubring.comap (φ : F →+* F₀) := h.symm ▸ ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap] at this
    simpa using this
  isPrincipalIdealRing' := by
    haveI := P₀.isPrincipalIdealRing'
    let g : ↥P₀.toValuationSubring →+* ↥(P₀.toValuationSubring.comap (φ : F →+* F₀)) :=
      { toFun := fun y => ⟨φ.symm y, by rw [ValuationSubring.mem_comap]; simpa using y.2⟩
        map_one' := by ext; simp
        map_mul' := by intros; ext; simp
        map_zero' := by ext; simp
        map_add' := by intros; ext; simp }
    refine IsPrincipalIdealRing.of_surjective g ?_
    rintro ⟨x, hx⟩
    refine ⟨⟨φ x, by simpa [ValuationSubring.mem_comap] using hx⟩, ?_⟩
    ext; simp [g]

theorem mem_comapPlace_iff (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) (f : F) :
    f ∈ (comapPlace φ P₀).toValuationSubring ↔ φ f ∈ P₀.toValuationSubring := ValuationSubring.mem_comap

noncomputable def comapPlaceHom (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) :
    ↥(comapPlace φ P₀).toValuationSubring →+* ↥P₀.toValuationSubring where
  toFun w := ⟨φ (w : F), (mem_comapPlace_iff φ P₀ w).mp w.2⟩
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

theorem comapPlaceHom_apply (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) (w : ↥(comapPlace φ P₀).toValuationSubring) :
    (comapPlaceHom φ P₀ w : F₀) = φ (w : F) := rfl

theorem comapPlaceHom_algebraMap (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) (c : K) :
    comapPlaceHom φ P₀ (algebraMap K _ c) = algebraMap K _ c := by
  ext; simp [comapPlaceHom_apply]

theorem mem_maximalIdeal_of_map (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) (w : ↥(comapPlace φ P₀).toValuationSubring)
    (h : comapPlaceHom φ P₀ w ∈ maximalIdeal ↥P₀.toValuationSubring) : w ∈ maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal] at h ⊢
  exact fun hu => h (hu.map _)

theorem isRational_comapPlace (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) (h : P₀.IsRational) :
    (comapPlace φ P₀).IsRational := by
  intro z
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨c, hc⟩ := h (IsLocalRing.residue _ (comapPlaceHom φ P₀ y))
  refine ⟨c, ?_⟩
  change IsLocalRing.residue _ (algebraMap K _ c) = IsLocalRing.residue _ y
  change IsLocalRing.residue _ (algebraMap K _ c) = IsLocalRing.residue _ _ at hc
  rw [residue_eq_residue_iff] at hc ⊢
  apply mem_maximalIdeal_of_map φ P₀
  rwa [map_sub, comapPlaceHom_algebraMap]

theorem evalAt_comapPlace (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) (h : P₀.IsRational) (f : F)
    (hf : φ f ∈ P₀.toValuationSubring) :
    (comapPlace φ P₀).evalAt f = P₀.evalAt (φ f) := by
  have hf' : f ∈ (comapPlace φ P₀).toValuationSubring := (mem_comapPlace_iff φ P₀ f).mpr hf
  have hrat := isRational_comapPlace φ P₀ h
  apply (comapPlace φ P₀).algebraMap_residueField_injective
  rw [(comapPlace φ P₀).algebraMap_evalAt hrat hf']
  have h0 := P₀.algebraMap_evalAt h hf
  change IsLocalRing.residue _ (algebraMap K _ _) = _ at h0
  change _ = IsLocalRing.residue _ (algebraMap K _ _)
  rw [residue_eq_residue_iff] at h0 ⊢
  apply mem_maximalIdeal_of_map φ P₀
  rw [map_sub, comapPlaceHom_algebraMap]
  rw [← neg_mem_iff, neg_sub]
  exact h0

end Transport

end GC3b21

namespace GC3b21

open IsLocalRing

section Transport2

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F] {F₀ : Type*} [Field F₀] [Algebra K F₀]

theorem isRational_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).surjective

theorem ord_comapPlace (φ : F ≃ₐ[K] F₀) (P₀ : Place K F₀) (f : F) :
    (comapPlace φ P₀).ord f = P₀.ord (φ f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥(comapPlace φ P₀).toValuationSubring)
  obtain ⟨u, hu⟩ := (comapPlace φ P₀).exists_unit_mul_zpow hf hϖ

  let ρ : ↥(comapPlace φ P₀).toValuationSubring ≃+* ↥P₀.toValuationSubring :=
    RingEquiv.ofBijective (comapPlaceHom φ P₀) ⟨fun a b h => by
        apply Subtype.ext
        have := congrArg (fun w : ↥P₀.toValuationSubring => (w : F₀)) h
        simpa [comapPlaceHom_apply] using this,
      fun y => ⟨⟨φ.symm y, by rw [mem_comapPlace_iff]; simpa using y.2⟩, by ext; simp [comapPlaceHom_apply]⟩⟩
  have hϖ' : Irreducible (ρ ϖ) := (MulEquiv.irreducible_iff ρ.toMulEquiv).mpr hϖ
  conv_rhs => rw [hu, map_mul, map_zpow₀]
  have h1 : φ ((u : ↥(comapPlace φ P₀).toValuationSubring) : F) = ((Units.map ρ.toMonoidHom u : (↥P₀.toValuationSubring)ˣ) : ↥P₀.toValuationSubring) := rfl
  have h2 : φ (ϖ : F) = (ρ ϖ : F₀) := rfl
  rw [h1, h2, P₀.ord_unit_smul_zpow _ hϖ']

theorem mem_localRing_refl_iff {X : Scheme} [IsIntegral X] {L : Type*} [Field L] (φ : L ≃+* X.functionField)
    (x : ↥X) (f : L) :
    φ f ∈ SemistableModel.localRing X (RingEquiv.refl _) x ↔ f ∈ SemistableModel.localRing X φ x := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply] at hσ ⊢
    rw [RingEquiv.symm_apply_eq]
    simpa using hσ
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply] at hσ ⊢
    rw [← hσ]
    simp

end Transport2

end GC3b21

namespace GC3bD6
open AlgebraicCurve IsLocalRing

section Composite
variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem evalAt_add (P : Place L F) (hP : P.IsRational) {f g : F}
    (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  apply P.algebraMap_residueField_injective
  rw [map_add, P.algebraMap_evalAt hP hf, P.algebraMap_evalAt hP hg, P.algebraMap_evalAt hP (add_mem hf hg),
    ← map_add]
  rfl

theorem evalAt_mul' (P : Place L F) (hP : P.IsRational) {f g : F}
    (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f * g) = P.evalAt f * P.evalAt g := by
  apply P.algebraMap_residueField_injective
  rw [map_mul, P.algebraMap_evalAt hP hf, P.algebraMap_evalAt hP hg, P.algebraMap_evalAt hP (mul_mem hf hg),
    ← map_mul]
  rfl

theorem evalAt_neg (P : Place L F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt (-f) = -P.evalAt f := by
  apply P.algebraMap_residueField_injective
  rw [map_neg, P.algebraMap_evalAt hP hf, P.algebraMap_evalAt hP (neg_mem hf), ← map_neg]
  rfl

theorem evalAt_zero (P : Place L F) : P.evalAt (0 : F) = 0 := by
  rw [P.evalAt_of_mem (zero_mem _)]
  have : (⟨(0 : F), zero_mem _⟩ : P.toValuationSubring) = 0 := rfl
  rw [this, map_zero, ← map_zero (algebraMap L P.ResidueField), P.residueInv_algebraMap]

theorem evalAt_eq_zero_of_not_isUnit (P : Place L F) {f : F} (hf : f ∈ P.toValuationSubring)
    (h : ¬ IsUnit (⟨f, hf⟩ : P.toValuationSubring)) : P.evalAt f = 0 := by
  rw [P.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h),
    ← map_zero (algebraMap L P.ResidueField), P.residueInv_algebraMap]

theorem isUnit_of_evalAt_ne_zero (P : Place L F) {f : F} (hf : f ∈ P.toValuationSubring)
    (h : P.evalAt f ≠ 0) : IsUnit (⟨f, hf⟩ : P.toValuationSubring) := by
  by_contra hu; exact h (evalAt_eq_zero_of_not_isUnit P hf hu)

theorem inv_mem_of_isUnit (P : Place L F) {f : F} (hf : f ∈ P.toValuationSubring)
    (h : IsUnit (⟨f, hf⟩ : P.toValuationSubring)) : f⁻¹ ∈ P.toValuationSubring := by
  obtain ⟨u, hu⟩ := h
  have h1 : f * (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) = 1 := by
    have h2 : ((u : P.toValuationSubring) : F) * (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    have h3 : ((u : P.toValuationSubring) : F) = f := by rw [hu]
    rwa [h3] at h2
  rw [inv_eq_of_mul_eq_one_right h1]; exact Subtype.mem _

theorem evalAt_inv' (P : Place L F) (hP : P.IsRational) {f : F}
    (hf : f ∈ P.toValuationSubring) (hfi : f⁻¹ ∈ P.toValuationSubring) :
    P.evalAt f⁻¹ = (P.evalAt f)⁻¹ := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have h0 : P.evalAt (0 : F) = 0 := evalAt_zero P
    rw [inv_zero, h0, inv_zero]
  apply P.algebraMap_residueField_injective
  rw [P.algebraMap_evalAt hP hfi, map_inv₀, P.algebraMap_evalAt hP hf]
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul]
  have : (⟨f, hf⟩ : P.toValuationSubring) * ⟨f⁻¹, hfi⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hf0)
  rw [this, map_one]

def compositeVS (A : ValuationSubring L) (P : Place L F) (hP : P.IsRational) : ValuationSubring F where
  carrier := {f | f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A}
  mul_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    exact ⟨mul_mem hf hg, by rw [evalAt_mul' P hP hf hg]; exact mul_mem hfA hgA⟩
  one_mem' := ⟨one_mem _, by rw [Place.evalAt_one]; exact one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    exact ⟨add_mem hf hg, by rw [evalAt_add P hP hf hg]; exact add_mem hfA hgA⟩
  zero_mem' := ⟨zero_mem _, by rw [evalAt_zero]; exact zero_mem _⟩
  neg_mem' := by
    rintro f ⟨hf, hfA⟩
    exact ⟨neg_mem hf, by rw [evalAt_neg P hP hf]; exact neg_mem hfA⟩
  mem_or_inv_mem' := by
    intro f
    by_cases hf : f ∈ P.toValuationSubring
    · by_cases hfA : P.evalAt f ∈ A
      · exact Or.inl ⟨hf, hfA⟩
      ·
        right
        have hf0 : P.evalAt f ≠ 0 := fun h => hfA (h ▸ zero_mem _)
        have hfi : f⁻¹ ∈ P.toValuationSubring :=
          inv_mem_of_isUnit P hf (isUnit_of_evalAt_ne_zero P hf hf0)
        refine ⟨hfi, ?_⟩
        rw [evalAt_inv' P hP hf hfi]
        exact (A.mem_or_inv_mem _).resolve_left hfA
    ·
      right
      have hfi : f⁻¹ ∈ P.toValuationSubring := (P.toValuationSubring.mem_or_inv_mem f).resolve_left hf
      refine ⟨hfi, ?_⟩
      have hnu : ¬ IsUnit (⟨f⁻¹, hfi⟩ : P.toValuationSubring) := fun hu =>
        hf (by simpa using inv_mem_of_isUnit P hfi hu)
      rw [evalAt_eq_zero_of_not_isUnit P hfi hnu]
      exact zero_mem _

theorem mem_compositeVS_iff (A : ValuationSubring L) (P : Place L F) (hP : P.IsRational) (f : F) :
    f ∈ compositeVS A P hP ↔ f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A := Iff.rfl

theorem evalAt_algebraMap (P : Place L F) (c : L) : P.evalAt (algebraMap L F c) = c := by
  rw [P.evalAt_of_mem (P.algebraMap_mem' c)]
  have : (⟨algebraMap L F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) = algebraMap L P.toValuationSubring c := rfl
  rw [this, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply L P.toValuationSubring P.ResidueField c,
    P.residueInv_algebraMap]

theorem evalAt_eq_of_sub_algebraMap_mem_nonunits (P : Place L F) (hP : P.IsRational) {g : F} (hg : g ∈ P.toValuationSubring)
    (c : L) (h : g - algebraMap L F c ∈ P.toValuationSubring.nonunits) : P.evalAt g = c := by
  have hc : algebraMap L F c ∈ P.toValuationSubring := P.algebraMap_mem' c
  have hsub : g - algebraMap L F c ∈ P.toValuationSubring := sub_mem hg hc
  have hnu : ¬ IsUnit (⟨g - algebraMap L F c, hsub⟩ : P.toValuationSubring) := by
    intro hu
    rcases (ValuationSubring.mem_nonunits_iff_or _).1 h with h0 | hni
    · obtain ⟨u, hu⟩ := hu
      exact u.ne_zero (by rw [hu]; exact Subtype.ext h0)
    · exact hni (inv_mem_of_isUnit P hsub hu)
  have h0 := evalAt_eq_zero_of_not_isUnit P hsub hnu
  rw [sub_eq_add_neg, evalAt_add P hP hg (neg_mem hc), evalAt_neg P hP hc, evalAt_algebraMap, ← sub_eq_add_neg,
    sub_eq_zero] at h0
  exact h0

end Composite

theorem appLE_congr_hom {X Y : AlgebraicGeometry.Scheme} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

end GC3bD6

theorem GC3b21.red_eq_of_centred
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀]
    [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O₀))) π₀)
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)

    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)

    (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K)
    (h𝒪F : ∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)))
    (hres : ∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s)))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1)

    (hrk : ∀ a b : ↥O, a ∈ IsLocalRing.maximalIdeal ↥O → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (φ : F ≃+* X.functionField)
    (hφ : ∀ (U : X.Opens) [Nonempty U]
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U)),
        φ.symm (X.germToFunctionField U s) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
            (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)))
    (hφa : ∀ a : ↥O, φ (algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ)) =
        SemistableModel.baseToFunctionField π a)
    (Q : Place (IsLocalRing.ResidueField ↥O) K) (P : Place (AlgebraicClosure ℚ) F)
    (hP : ∀ f : F, f ∈ SemistableModel.localRing X φ (((𝔐k.pointEquivPlace.symm Q).1 ≫ ek ≫
          pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))) →
      f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ O,
        (IsUnit (⟨P.evalAt f, h⟩ : ↥O) ↔ ∃ f' ∈ SemistableModel.localRing X φ (((𝔐k.pointEquivPlace.symm Q).1 ≫ ek ≫
          pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))), f * f' = 1)) :
    red P = Q := by
  classical

  set fst := pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)) with hfstdef
  set fstk := pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) with hfstkdef
  set zQ := (𝔐k.pointEquivPlace.symm Q) with hzQdef
  set xQ : ↥X := (zQ.1 ≫ ek ≫ fstk).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) with hxQdef

  have hPrat : P.IsRational := by
    have := AlgebraicCurve.CurveModel.isRational_pointEquivPlace 𝔐 (𝔐.pointEquivPlace.symm P)
    simpa using this

  have hinj : ∀ x : ↥X, Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    fun x => IsFractionRing.injective _ _

  let W : ValuationSubring F := GC3bD6.compositeVS O P hPrat
  have hW : ∀ f : F, f ∈ W ↔ f ∈ P.toValuationSubring ∧ P.evalAt f ∈ O := fun f => Iff.rfl
  let V : ValuationSubring X.functionField := W.comap (φ.symm : X.functionField ≃+* F).toRingHom
  have hV : ∀ s : X.functionField, s ∈ V ↔ φ.symm s ∈ W := fun s => ValuationSubring.mem_comap

  have hloc : ∀ s : X.presheaf.stalk xQ,
      φ.symm (algebraMap (X.presheaf.stalk xQ) X.functionField s) ∈ SemistableModel.localRing X φ xQ :=
    fun s => ⟨s, rfl⟩
  have h₁ : ∀ s : X.presheaf.stalk xQ, algebraMap (X.presheaf.stalk xQ) X.functionField s ∈ V := by
    intro s
    rw [hV, hW]
    obtain ⟨h1, h2, -⟩ := hP _ (hloc s)
    exact ⟨h1, h2⟩
  have h₁' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk xQ),
      algebraMap (X.presheaf.stalk xQ) X.functionField s ∈ V.nonunits := by
    intro s hs
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_contra hcon
    push_neg at hcon
    obtain ⟨hs0, hsinv⟩ := hcon

    set g : F := φ.symm (algebraMap (X.presheaf.stalk xQ) X.functionField s) with hgdef
    obtain ⟨hg1, hg2, hgiff⟩ := hP g (hloc s)
    have hgi : g⁻¹ ∈ W := by
      have := (hV _).1 hsinv
      rwa [map_inv₀] at this
    obtain ⟨hgi1, hgi2⟩ := (hW _).1 hgi
    have hunit : IsUnit (⟨P.evalAt g, hg2⟩ : ↥O) := by
      have hg0 : g ≠ 0 := by
        intro h0; apply hs0
        have : φ.symm (algebraMap (X.presheaf.stalk xQ) X.functionField s) = φ.symm 0 := by rw [map_zero]; exact h0
        exact φ.symm.injective this
      have hmul : (⟨P.evalAt g, hg2⟩ : ↥O) * ⟨P.evalAt g⁻¹, hgi2⟩ = 1 := by
        apply Subtype.ext
        show P.evalAt g * P.evalAt g⁻¹ = 1
        rw [← GC3bD6.evalAt_mul' P hPrat hg1 hgi1, mul_inv_cancel₀ hg0, Place.evalAt_one]
      exact isUnit_iff_exists_inv.2 ⟨_, hmul⟩
    obtain ⟨g', hg', hgg'⟩ := hgiff.1 hunit
    obtain ⟨s', hs'⟩ := hg'

    have hss' : s * s' = 1 := by
      apply hinj xQ
      apply φ.symm.injective
      rw [map_mul, map_mul, map_one, map_one]
      change g * _ = 1
      convert hgg' using 2
      exact hs'
    exact (IsLocalRing.mem_maximalIdeal _).1 hs (isUnit_iff_exists_inv.2 ⟨_, hss'⟩)

  let xP : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X := (𝔐.pointEquivPlace.symm P).1 ≫ e ≫ fst
  have hxP : xP ≫ π = Spec.map (CommRingCat.ofHom O.subtype) ≫ 𝟙 (Spec (CommRingCat.of ↥O)) := by
    show ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ≫ π = _
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e, he, ← Category.assoc,
      (𝔐.pointEquivPlace.symm P).2, Category.id_comp, Category.comp_id]
  obtain ⟨Pt, hPt, -⟩ := NeronModelInfra.existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring O π
    (𝟙 (Spec (CommRingCat.of ↥O))) xP hxP
  set x' : ↥X := Pt.1.base (IsLocalRing.closedPoint ↥O) with hx'def

  set pt₀ := IsLocalRing.closedPoint (AlgebraicClosure ℚ) with hpt₀
  set z := 𝔐.pointEquivPlace.symm P with hzdef
  have hzP : 𝔐.pointEquivPlace z = P := by rw [hzdef, Equiv.apply_symm_apply]
  have hPt_mem : ∀ (U : X.Opens), x' ∈ U → ∀ q : ↥(Spec (CommRingCat.of ↥O)), Pt.1.base q ∈ U := by
    intro U hxU q
    exact ((IsLocalRing.specializes_closedPoint q).map Pt.1.base.hom.continuous).mem_open U.2 hxU
  have hy : xP.base pt₀ = Pt.1.base ((Spec.map (CommRingCat.ofHom O.subtype)).base pt₀) := by
    rw [← hPt]; rfl

  have key : ∀ (U : X.Opens) (hxU : x' ∈ U) (sec : X.presheaf.obj (Opposite.op U)),
      φ.symm (algebraMap (X.presheaf.stalk x') X.functionField (X.presheaf.germ U x' hxU sec)) ∈ P.toValuationSubring ∧
      P.evalAt (φ.symm (algebraMap (X.presheaf.stalk x') X.functionField (X.presheaf.germ U x' hxU sec))) =
        ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).hom (Pt.1.appLE U ⊤ (fun q _ => hPt_mem U hxU q) sec) : AlgebraicClosure ℚ) := by
    intro U hxU sec
    haveI : Nonempty U := ⟨⟨x', hxU⟩⟩
    have hyU : xP.base pt₀ ∈ U := by rw [hy]; exact hPt_mem U hxU _
    haveI hne : Nonempty ((e ≫ fst) ⁻¹ᵁ U) := ⟨⟨z.1.base pt₀, hyU⟩⟩

    have hgerm : algebraMap (X.presheaf.stalk x') X.functionField (X.presheaf.germ U x' hxU sec) =
        X.germToFunctionField U sec :=
      TopCat.Presheaf.germ_stalkSpecializes_apply _ hxU (genericPoint_specializes x') sec
    rw [hgerm, hφ U hne sec]

    have hz : ⊤ ≤ z.1 ⁻¹ᵁ ((e ≫ fst) ⁻¹ᵁ U) := by
      intro q _
      obtain rfl : q = pt₀ := Subsingleton.elim _ _
      exact hyU
    obtain ⟨hmem, hval⟩ :=
      AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
        𝔐 ((e ≫ fst) ⁻¹ᵁ U) (((e ≫ fst).app U).hom sec) z hz
    rw [hzP] at hmem hval
    refine ⟨hmem, ?_⟩
    rw [GC3bD6.evalAt_eq_of_sub_algebraMap_mem_nonunits P hPrat hmem _ hval]

    have hPtU : ⊤ ≤ Pt.1 ⁻¹ᵁ U := fun q _ => hPt_mem U hxU q
    have hxPU : ⊤ ≤ xP ⁻¹ᵁ U := hz

    have e1 : z.1.appLE ((e ≫ fst) ⁻¹ᵁ U) ⊤ hz (((e ≫ fst).app U).hom sec) = (xP.appLE U ⊤ hxPU).hom sec := by
      show ((e ≫ fst).app U ≫ z.1.appLE ((e ≫ fst) ⁻¹ᵁ U) ⊤ hz).hom sec = _
      rw [← Scheme.Hom.comp_appLE]

    have e2 : xP.appLE U ⊤ hxPU = (Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1).appLE U ⊤ (hPt.symm ▸ hxPU) :=
      GC3bD6.appLE_congr_hom hPt.symm U ⊤ hxPU

    have e3 : (Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1).appLE U ⊤ (hPt.symm ▸ hxPU) =
        Pt.1.appLE U ⊤ hPtU ≫ (Spec.map (CommRingCat.ofHom O.subtype)).appLE ⊤ ⊤ (fun _ _ => trivial) :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm

    have e4 : (Spec.map (CommRingCat.ofHom O.subtype)).appLE ⊤ ⊤ (fun _ _ => trivial) =
        (Spec.map (CommRingCat.ofHom O.subtype)).appTop := by
      simp [Scheme.Hom.appTop, Scheme.Hom.appLE]
    have e5 : ∀ t, (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom
        ((Spec.map (CommRingCat.ofHom O.subtype)).appTop t) =
          O.subtype ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).hom t) := by
      intro t
      have h := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom O.subtype))
      rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
      first
        | exact DFunLike.congr_fun h t
        | simp
        | (have h' := DFunLike.congr_fun h t; simp only [RingHom.comp_apply] at h'; exact h')
    rw [e1, e2, e3, e4, CommRingCat.hom_comp, RingHom.comp_apply, e5]
    rfl
  have h₂ : ∀ s : X.presheaf.stalk x', algebraMap (X.presheaf.stalk x') X.functionField s ∈ V := by
    intro s
    obtain ⟨U, hxU, sec, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s
    obtain ⟨hmem, hval⟩ := key U hxU sec
    rw [hV, hW]
    exact ⟨hmem, by rw [hval]; exact Subtype.mem _⟩
  have h₂' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x'),
      algebraMap (X.presheaf.stalk x') X.functionField s ∈ V.nonunits := by
    intro s hs
    obtain ⟨U, hxU, sec, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s
    obtain ⟨hmem, hval⟩ := key U hxU sec

    have hrm : (Scheme.ΓSpecIso (CommRingCat.of ↥O)).hom (Pt.1.appLE U ⊤ (fun q _ => hPt_mem U hxU q) sec) ∈
        IsLocalRing.maximalIdeal ↥O := by
      set r : ↥O := (Scheme.ΓSpecIso (CommRingCat.of ↥O)).hom (Pt.1.appLE U ⊤ (fun q _ => hPt_mem U hxU q) sec) with hrdef

      have hloc' : IsLocalHom (Pt.1.stalkMap (IsLocalRing.closedPoint ↥O)).hom := inferInstance
      have h1 : (Pt.1.stalkMap (IsLocalRing.closedPoint ↥O)).hom (X.presheaf.germ U x' hxU sec) ∈
          IsLocalRing.maximalIdeal _ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (IsLocalRing.mem_maximalIdeal _).1 hs (hloc'.map_nonunit _ hu)

      have h2 : (Pt.1.stalkMap (IsLocalRing.closedPoint ↥O)).hom (X.presheaf.germ U x' hxU sec) =
          (Spec (CommRingCat.of ↥O)).presheaf.germ ⊤ (IsLocalRing.closedPoint ↥O) trivial
            (Pt.1.appLE U ⊤ (fun q _ => hPt_mem U hxU q) sec) := by
        rw [Scheme.Hom.germ_stalkMap_apply]
        show _ = (Spec (CommRingCat.of ↥O)).presheaf.germ ⊤ (IsLocalRing.closedPoint ↥O) trivial
          (((Pt.1.app U) ≫ (Spec (CommRingCat.of ↥O)).presheaf.map (homOfLE (fun q _ => hPt_mem U hxU q)).op).hom sec)
        rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
      have h3 : (Spec (CommRingCat.of ↥O)).presheaf.germ ⊤ (IsLocalRing.closedPoint ↥O) trivial
            (Pt.1.appLE U ⊤ (fun q _ => hPt_mem U hxU q) sec) =
          letI : Algebra ↥O ((Spec.structureSheaf ↥O).presheaf.stalk (IsLocalRing.closedPoint ↥O)) := inferInstance
          algebraMap ↥O ((Spec.structureSheaf ↥O).presheaf.stalk (IsLocalRing.closedPoint ↥O)) r := by
        rw [StructureSheaf.stalkAlgebra_map]
        have : Pt.1.appLE U ⊤ (fun q _ => hPt_mem U hxU q) sec = (Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv r := by
          rw [hrdef, ← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
        rw [this, Scheme.ΓSpecIso_inv]
        exact (congrArg (fun φ' => φ'.hom r) (StructureSheaf.algebraMap_germ (R := ↥O) ⊤ (IsLocalRing.closedPoint ↥O) trivial))
      rw [h2, h3] at h1
      letI : Algebra ↥O ((Spec.structureSheaf ↥O).presheaf.stalk (IsLocalRing.closedPoint ↥O)) := inferInstance
      haveI := StructureSheaf.IsLocalization.to_stalk ↥O (IsLocalRing.closedPoint ↥O)
      by_contra hr
      have hru : IsUnit r := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hr
      have := ((IsLocalization.AtPrime.isUnit_to_map_iff
        ((Spec.structureSheaf ↥O).presheaf.stalk (IsLocalRing.closedPoint ↥O)) (IsLocalRing.closedPoint ↥O).asIdeal r).2
        (show r ∈ (IsLocalRing.maximalIdeal ↥O).primeCompl from fun h => hr h))
      exact (IsLocalRing.mem_maximalIdeal _).1 h1 this
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_contra hcon
    push_neg at hcon
    obtain ⟨hs0, hsinv⟩ := hcon
    set g : F := φ.symm (algebraMap (X.presheaf.stalk x') X.functionField (X.presheaf.germ U x' hxU sec)) with hgdef
    have hgi : g⁻¹ ∈ W := by
      have := (hV _).1 hsinv
      rwa [map_inv₀] at this
    obtain ⟨hgi1, hgi2⟩ := (hW _).1 hgi
    have hg0 : g ≠ 0 := by
      intro h0; apply hs0
      have : φ.symm (algebraMap (X.presheaf.stalk x') X.functionField (X.presheaf.germ U x' hxU sec)) = φ.symm 0 := by
        rw [map_zero]; exact h0
      exact φ.symm.injective this
    apply (IsLocalRing.mem_maximalIdeal _).1 hrm
    refine isUnit_iff_exists_inv.2 ⟨⟨P.evalAt g⁻¹, hgi2⟩, Subtype.ext ?_⟩
    show ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).hom (Pt.1.appLE U ⊤ (fun q _ => hPt_mem U hxU q) sec) : AlgebraicClosure ℚ)
      * P.evalAt g⁻¹ = 1
    rw [← hval, ← GC3bD6.evalAt_mul' P hPrat hmem hgi1, mul_inv_cancel₀ hg0, Place.evalAt_one]

  have hcentre : x' = xQ :=
    AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated π V x' xQ h₂ h₂' h₁ h₁'

  have hk := hred P Pt hPt.symm
  set zP := (𝔐k.pointEquivPlace.symm (red P)) with hzPdef
  have hpt : (zP.1 ≫ ek ≫ fstk).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) = xQ := by
    rw [hk, ← hcentre]
    show Pt.1.base ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))) = Pt.1.base (IsLocalRing.closedPoint ↥O)
    congr 1
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥O)

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion (ek ≫ fstk) := inferInstance
  have hinjk : Function.Injective (ek ≫ fstk).base := (ek ≫ fstk).isClosedEmbedding.injective
  have hzz : zP.1.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) =
      zQ.1.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) := by
    apply hinjk
    show (zP.1 ≫ ek ≫ fstk).base _ = (zQ.1 ≫ ek ≫ fstk).base _
    rw [hpt]
  have hz : zP.1 = zQ.1 := AlgebraicGeometry.ext_of_apply_closedPoint_eq 𝔐k.toBase zP.2 zQ.2 hzz
  have : zP = zQ := Subtype.ext hz
  rw [hzPdef, hzQdef] at this
  exact 𝔐k.pointEquivPlace.symm.injective this

theorem solution
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    (j : O₀ →+* ↥O) (hj : Function.Injective j)
    (hju : ∀ n : ℕ, ¬ p ∣ n → IsUnit ((n : ℕ) : O₀))
    {X₀ : Scheme.{0}} (π₀ : X₀ ⟶ Spec (CommRingCat.of O₀)) [IsProper π₀]
    [SmoothOfRelativeDimension 1 π₀] [GeometricallyIntegral π₀]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O₀))) π₀)
    (e₀ : X ⟶ pullback π₀ (Spec.map (CommRingCat.ofHom j))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd π₀ (Spec.map (CommRingCat.ofHom j)) = π)

    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)

    (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K)
    (h𝒪F : ∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)))
    (hres : ∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s)))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F)

    (he1 : ∀ f : F, f ≠ 0 → ∃ c : AlgebraicClosure ℚ, ∃ h : c • f ∈ 𝒪F, res ⟨c • f, h⟩ ≠ 0)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1) :
    ∀ (g : F) (hg : g ∈ 𝒪F), res ⟨g, hg⟩ ≠ 0 →
      ∀ Q : Place (IsLocalRing.ResidueField ↥O) K,
        (∀ P : Place (AlgebraicClosure ℚ) F, red P = Q → P.ord g = 0) → Q.ord (res ⟨g, hg⟩) = 0 := by
  intro g hg hg0 Q hQ
  classical

  haveI hsmooth : Smooth π := SmoothOfRelativeDimension.smooth 1 π

  obtain ⟨hrk, hOuniv⟩ := GC3b21.rankOne_and_ne_univ_of_liesOverPrime O p hp hO
  haveI : HenselianLocalRing ↥O := ValuationSubring.henselianLocalRing_of_isAlgClosed O

  set ξ : ↥X := (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
      (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) with hξdef

  set xQ : ↥X := ((𝔐k.pointEquivPlace.symm Q).1 ≫ ek ≫
      pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) with hxQdef

  haveI hopenO : IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) :=
    GC3b21.isOpenImmersion_specMap_subtype O p hO hrk hp
  haveI hf₀ : IsOpenImmersion (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) := inferInstance
  have hsq : (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ≫ π =
      𝔐.toBase ≫ Spec.map (CommRingCat.ofHom O.subtype) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  let φ : F ≃+* X.functionField :=
    𝔐.ffEquiv.trans (GC3b21.ffIso (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))).commRingCatIsoToRingEquiv.symm
  have hφ : ∀ a : ↥O, φ (algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ)) =
      SemistableModel.baseToFunctionField π a := by
    intro a
    show (GC3b21.ffIso (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))).commRingCatIsoToRingEquiv.symm
      (𝔐.ffEquiv (algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))) = _
    rw [RingEquiv.symm_apply_eq, 𝔐.ffEquiv_algebraMap]
    exact (GC3b21.ffIso_hom_baseToFunctionField _ π 𝔐.toBase O.subtype hsq a).symm
  have hφsec : ∀ (U : X.Opens) [Nonempty U]
      (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
      (s : X.presheaf.obj (Opposite.op U)),
      φ.symm (X.germToFunctionField U s) =
        𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
          (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) := by
    intro U _ hV s
    show 𝔐.ffEquiv.symm ((GC3b21.ffIso (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))).commRingCatIsoToRingEquiv
      (X.germToFunctionField U s)) = _
    congr 1
    exact GC3b21.ffIso_hom_germToFunctionField _ U s

  have hq2 : (𝔐k.pointEquivPlace.symm Q).1 ≫ 𝔐k.toBase = 𝟙 _ := (𝔐k.pointEquivPlace.symm Q).2
  have hcompk : ((𝔐k.pointEquivPlace.symm Q).1 ≫ ek ≫
      pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ≫ π =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc ek, hek, ← Category.assoc, hq2,
      Category.id_comp]
  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue ↥O)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue ↥O))
  have hx : π.base xQ = IsLocalRing.closedPoint ↥O := by
    rw [hxQdef]
    change ((((𝔐k.pointEquivPlace.symm Q).1 ≫ ek ≫
      pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ≫ π).base
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))) = _
    rw [hcompk]
    exact Spec_closedPoint
  have hξ : π.base ξ = IsLocalRing.closedPoint ↥O := by
    rw [hξdef]
    change ((pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) ≫ π).base
      (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))))) = _
    rw [pullback.condition]
    change (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).base
      ((pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
        (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))))) = _
    rw [Subsingleton.elim ((pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base _)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))]
    exact Spec_closedPoint

  have hx'cl : IsClosed ({((𝔐k.pointEquivPlace.symm Q).1 ≫ ek).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))} :
        Set ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) := by
    have h1 : IsClosed ({((𝔐k.pointEquivPlace.symm Q).1).base
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))} : Set ↥𝔐k.C) :=
      mem_closedPoints_iff.mp (pointEquivClosedPoint 𝔐k.toBase (𝔐k.pointEquivPlace.symm Q)).2
    have h2 := (ek.homeomorph.isClosedMap) _ h1
    simpa [Set.image_singleton] using h2
  have hxQcl : IsClosed ({xQ} : Set ↥X) := by
    have h2 := (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).isClosedEmbedding.isClosedMap
      _ hx'cl
    rw [Set.image_singleton] at h2
    simpa [hxQdef, Scheme.Hom.comp_apply] using h2
  have hxc : ∀ y : ↥X, xQ ⤳ y → y = xQ := by
    intro y hy
    rw [specializes_iff_mem_closure, hxQcl.closure_eq] at hy
    exact hy
  have hxs : xQ ∈ π.smoothLocus := by rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  have hξx : ξ ⤳ xQ := by
    rw [hξdef, hxQdef, Scheme.Hom.comp_apply]
    exact ((genericPoint_spec _).specializes (Set.mem_univ _)).map
      (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base.hom.continuous
  have hne : ξ ≠ xQ := by
    intro h
    rw [hξdef, hxQdef, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    have h1 := (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).isClosedEmbedding.injective h
    rw [← genericPoint_eq_of_isOpenImmersion ek] at h1
    have h2 := ek.homeomorph.injective h1
    exact GC3b21.genericPoint_ne_of_mem_closedPoints 𝔐k _
      (pointEquivClosedPoint 𝔐k.toBase (𝔐k.pointEquivPlace.symm Q)).2 h2.symm

  have h𝒪Fφ : 𝒪F.toSubring = SemistableModel.localRing X φ ξ := by
    ext f
    rw [ValuationSubring.mem_toSubring]
    constructor
    · intro hf
      obtain ⟨U, hξU, hV, s, t, hunit, heq⟩ := (h𝒪F f).mp hf
      haveI : Nonempty U := ⟨⟨ξ, hξU⟩⟩
      rw [← hφsec U hV t, ← hφsec U hV s, ← GC3b21.algebraMap_germ U ξ hξU t,
        ← GC3b21.algebraMap_germ U ξ hξU s] at heq
      obtain ⟨u, hu⟩ := hunit
      have hne : φ.symm (algebraMap (X.presheaf.stalk ξ) X.functionField (X.presheaf.germ U ξ hξU t)) ≠ 0 := by
        rw [← hu, map_ne_zero_iff _ φ.symm.injective,
          map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk ξ) X.functionField)]
        exact u.ne_zero
      refine ⟨X.presheaf.germ U ξ hξU s * ↑u⁻¹, ?_⟩
      simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply]
      have hf' := (eq_mul_inv_iff_mul_eq₀ hne).mpr heq
      rw [eq_comm, hf', ← hu, map_mul, map_mul, map_units_inv, map_inv₀]
    · rintro ⟨σ, hσ⟩
      obtain ⟨U, hξU, s, hs⟩ := X.presheaf.germ_exist σ
      haveI : Nonempty U := ⟨⟨ξ, hξU⟩⟩
      have hV := GC3b21.nonempty_preimage_of_mem (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) U ξ hξU
      refine (h𝒪F f).mpr ⟨U, hξU, hV, s, 1, by rw [map_one]; exact isUnit_one, ?_⟩
      rw [← hφsec U hV 1, ← hφsec U hV s, map_one, map_one, mul_one, ← GC3b21.algebraMap_germ U ξ hξU s, hs, ← hσ]
      rfl

  have hsqk : (ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ≫ π =
      𝔐k.toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hek]
  haveI hne𝔐 : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ (⊤ : X.Opens)) :=
    ⟨⟨genericPoint ↥𝔐.C, trivial⟩⟩
  haveI hne𝔐k : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ
      (⊤ : X.Opens)) := ⟨⟨genericPoint ↥𝔐k.C, trivial⟩⟩
  haveI hneX : Nonempty ((⊤ : X.Opens)) := ⟨⟨ξ, trivial⟩⟩
  have hcompat : ∀ (a : ↥O) (h : algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) ∈ 𝒪F),
      res ⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), h⟩ =
        algebraMap (IsLocalRing.ResidueField ↥O) K (IsLocalRing.residue ↥O a) := by
    intro a h
    have hRs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
        (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app ⊤).hom
          (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) := by
      rw [← hφsec ⊤ hne𝔐, RingEquiv.symm_apply_eq, hφ a]
      rfl
    have hmem : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
        (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app ⊤).hom
          (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv a)))) ∈ 𝒪F := by rw [hRs]; exact h
    have h1 := hres ⊤ hne𝔐 hne𝔐k _ hmem
    have key : (⟨_, hmem⟩ : ↥𝒪F) = ⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), h⟩ := Subtype.ext hRs
    rw [key] at h1
    rw [h1, RingEquiv.symm_apply_eq, 𝔐k.ffEquiv_algebraMap]
    exact GC3b21.germToFunctionField_app_baseSection _ π 𝔐k.toBase (IsLocalRing.residue ↥O) hsqk a

  have hprolong : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) F x ∈ 𝒪F ↔ x ∈ O := by
    have hin : ∀ x : AlgebraicClosure ℚ, x ∈ O → algebraMap (AlgebraicClosure ℚ) F x ∈ 𝒪F := by
      intro x hx
      rw [← ValuationSubring.mem_toSubring, h𝒪Fφ]
      refine ⟨X.presheaf.germ ⊤ ξ trivial (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv ⟨x, hx⟩)), ?_⟩
      simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply]
      rw [GC3b21.algebraMap_germ ⊤ ξ trivial, RingEquiv.symm_apply_eq]
      exact (hφ ⟨x, hx⟩).symm
    intro x
    refine ⟨fun hxF => ?_, hin x⟩
    by_contra hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ O.zero_mem)
    have hxi : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
    have hxim : (⟨x⁻¹, hxi⟩ : ↥O) ∈ IsLocalRing.maximalIdeal ↥O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu⟩ := hu
      apply hx
      have h1 : x⁻¹ * (((u⁻¹ : (↥O)ˣ) : ↥O) : AlgebraicClosure ℚ) = 1 := by
        have h2 := congrArg (fun z : ↥O => (z : AlgebraicClosure ℚ)) u.mul_inv
        simpa [hu] using h2
      rw [← inv_inv x, inv_eq_of_mul_eq_one_right h1]
      exact ((u⁻¹ : (↥O)ˣ) : ↥O).2
    have hyF : algebraMap (AlgebraicClosure ℚ) F x⁻¹ ∈ 𝒪F := hin _ hxi
    have hres0 : res ⟨algebraMap (AlgebraicClosure ℚ) F x⁻¹, hyF⟩ = 0 := by
      have h1 := hcompat ⟨x⁻¹, hxi⟩ hyF
      rw [h1, (IsLocalRing.residue_eq_zero_iff _).mpr hxim, map_zero]
    have hym : (⟨algebraMap (AlgebraicClosure ℚ) F x⁻¹, hyF⟩ : ↥𝒪F) ∈ IsLocalRing.maximalIdeal ↥𝒪F := by
      rw [← hker]; exact hres0
    apply (IsLocalRing.mem_maximalIdeal _).mp hym
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap (AlgebraicClosure ℚ) F x, hxF⟩, Subtype.ext ?_⟩
    show algebraMap (AlgebraicClosure ℚ) F x⁻¹ * algebraMap (AlgebraicClosure ℚ) F x = 1
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]

  have hcentred : ∀ P : Place (AlgebraicClosure ℚ) F,
      (∀ f : F, f ∈ SemistableModel.localRing X φ xQ → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ O,
        (IsUnit (⟨P.evalAt f, h⟩ : ↥O) ↔ ∃ f' ∈ SemistableModel.localRing X φ xQ, f * f' = 1)) →
      red P = Q := fun P hP =>
    GC3b21.red_eq_of_centred O p hp hO X π O₀ j hj hju π₀ ε₀ e₀ he₀ F 𝔐 e he K 𝔐k ek hek 𝒪F res h𝒪F hres hsurj hker
      red hred hrk φ hφsec hφ Q P (by simpa only [hxQdef] using hP)

  have hQeq' : Q = 𝔐k.placeOfPoint (pointEquivClosedPoint 𝔐k.toBase (𝔐k.pointEquivPlace.symm Q)) := by
    rw [← CurveModel.pointEquivPlace_apply, Equiv.apply_symm_apply]
  have hreadQ : ∀ (f : F), f ∈ SemistableModel.localRing X φ xQ → ∀ (hf : f ∈ 𝒪F),
      res ⟨f, hf⟩ ∈ Q.toValuationSubring := by
    intro f hfS hf
    obtain ⟨σ, hσ⟩ := hfS
    obtain ⟨U, hxU, s, hs⟩ := X.presheaf.germ_exist σ
    haveI : Nonempty U := ⟨⟨xQ, hxU⟩⟩
    have hV := GC3b21.nonempty_preimage_of_mem (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) U xQ hxU
    have hx'U : ((𝔐k.pointEquivPlace.symm Q).1).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) ∈
        (ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U := by
      show (ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base _ ∈ U
      rw [← Scheme.Hom.comp_apply, ← hxQdef]
      exact hxU
    have hW : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U) :=
      ⟨⟨_, hx'U⟩⟩
    have hfR : f = 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
        (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) := by
      rw [← hφsec U hV s, ← GC3b21.algebraMap_germ U xQ hxU s, hs, ← hσ]
      rfl
    have hmem : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
        (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F := hfR ▸ hf
    have h1 := hres U hV hW s hmem
    have key : (⟨f, hf⟩ : ↥𝒪F) = ⟨_, hmem⟩ := Subtype.ext hfR
    rw [key, h1, hQeq']

    have hr := 𝔐k.range_stalk_eq (pointEquivClosedPoint 𝔐k.toBase (𝔐k.pointEquivPlace.symm Q))
    rw [← ValuationSubring.mem_toSubring, ← hr]
    refine ⟨𝔐k.C.presheaf.germ _ _ hx'U (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue ↥O)))).app U).hom s), ?_⟩
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply]
    congr 1
    exact GC3b21.algebraMap_germ _ _ hx'U _

  have hgu : IsUnit (⟨g, hg⟩ : ↥𝒪F) := (GC3b21.isUnit_iff_residue_ne_zero 𝒪F res hker _).mpr hg0
  have hg_ne : g ≠ 0 := by
    rintro rfl
    have h0 : (⟨0, hg⟩ : ↥𝒪F) = 0 := rfl
    exact hg0 (by rw [h0, map_zero])
  have hgi : g⁻¹ ∈ 𝒪F := by
    obtain ⟨u, hu⟩ := hgu
    have h1 : g * (((u⁻¹ : (↥𝒪F)ˣ) : ↥𝒪F) : F) = 1 := by
      have h2 := congrArg (fun z : ↥𝒪F => (z : F)) u.mul_inv
      simpa [hu] using h2
    rw [inv_eq_of_mul_eq_one_right h1]
    exact ((u⁻¹ : (↥𝒪F)ˣ) : ↥𝒪F).2

  have memP : ∀ P : Place (AlgebraicClosure ℚ) F,
      (∀ f : F, f ∈ SemistableModel.localRing X φ xQ → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ O,
        (IsUnit (⟨P.evalAt f, h⟩ : ↥O) ↔ ∃ f' ∈ SemistableModel.localRing X φ xQ, f * f' = 1)) →
      g ∈ P.toValuationSubring ∧ g⁻¹ ∈ P.toValuationSubring := by
    intro P hP
    have h0 : P.ord g = 0 := hQ P (hcentred P hP)
    exact ⟨GC3b21.mem_of_ord_eq_zero P hg_ne h0,
      GC3b21.mem_of_ord_eq_zero P (inv_ne_zero hg_ne) (by rw [Place.ord_inv, h0, neg_zero])⟩

  letI algQ : Algebra (AlgebraicClosure ℚ) ↥X.functionField :=
    (φ.toRingHom.comp (algebraMap (AlgebraicClosure ℚ) F)).toAlgebra
  let φₐ : F ≃ₐ[AlgebraicClosure ℚ] ↥X.functionField := AlgEquiv.ofRingEquiv (f := φ) (fun c => rfl)
  have hφₐ : ∀ f : F, φₐ f = φ f := fun f => rfl
  haveI hcurve₀ : IsCurveOver (AlgebraicClosure ℚ) ↥X.functionField :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      𝔐.toBase (GC3b21.ffIso (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))).commRingCatIsoToRingEquiv
      (fun a => by
        change (GC3b21.ffIso (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))).commRingCatIsoToRingEquiv
          ((GC3b21.ffIso (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))).commRingCatIsoToRingEquiv.symm
            (𝔐.ffEquiv (algebraMap (AlgebraicClosure ℚ) F a))) = _
        rw [RingEquiv.apply_symm_apply, 𝔐.ffEquiv_algebraMap])
  haveI hEFT₀ : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥X.functionField :=
    Algebra.EssFiniteType.of_surjective φₐ.toAlgHom φₐ.surjective
  have hφ₀ : ∀ a : ↥O, (RingEquiv.refl ↥X.functionField)
      (algebraMap (AlgebraicClosure ℚ) ↥X.functionField (a : AlgebraicClosure ℚ)) =
        SemistableModel.baseToFunctionField π a := fun a => hφ a

  have hcT : ∀ P₀ : Place (AlgebraicClosure ℚ) ↥X.functionField,
      (∀ f₀ : ↥X.functionField, f₀ ∈ SemistableModel.localRing X (RingEquiv.refl _) xQ →
        f₀ ∈ P₀.toValuationSubring ∧ ∃ h : P₀.evalAt f₀ ∈ O,
          (IsUnit (⟨P₀.evalAt f₀, h⟩ : ↥O) ↔ ∃ f' ∈ SemistableModel.localRing X (RingEquiv.refl _) xQ, f₀ * f' = 1)) →
      (∀ f : F, f ∈ SemistableModel.localRing X φ xQ →
        f ∈ (GC3b21.comapPlace φₐ P₀).toValuationSubring ∧ ∃ h : (GC3b21.comapPlace φₐ P₀).evalAt f ∈ O,
          (IsUnit (⟨(GC3b21.comapPlace φₐ P₀).evalAt f, h⟩ : ↥O) ↔
            ∃ f' ∈ SemistableModel.localRing X φ xQ, f * f' = 1)) := by
    intro P₀ hP₀ f hf
    obtain ⟨h1, h2, h3⟩ := hP₀ (φ f) ((GC3b21.mem_localRing_refl_iff φ xQ f).mpr hf)
    have hev : (GC3b21.comapPlace φₐ P₀).evalAt f = P₀.evalAt (φ f) :=
      GC3b21.evalAt_comapPlace φₐ P₀ (GC3b21.isRational_of_isAlgClosed P₀) f h1
    refine ⟨(GC3b21.mem_comapPlace_iff φₐ P₀ f).mpr h1, ?_⟩
    rw [hev]
    refine ⟨h2, h3.trans ⟨?_, ?_⟩⟩
    · rintro ⟨f', hf', hff'⟩
      refine ⟨φ.symm f', (GC3b21.mem_localRing_refl_iff φ xQ _).mp (by simpa using hf'), ?_⟩
      apply φ.injective
      rw [map_mul, RingEquiv.apply_symm_apply, hff', map_one]
    · rintro ⟨f', hf', hff'⟩
      exact ⟨φ f', (GC3b21.mem_localRing_refl_iff φ xQ _).mpr hf', by rw [← map_mul, hff', map_one]⟩

  letI algk : Algebra (IsLocalRing.ResidueField ↥O) ↥𝔐k.C.functionField := 𝔐k.functionFieldAlgebra
  let ψ : K ≃ₐ[IsLocalRing.ResidueField ↥O] ↥𝔐k.C.functionField := 𝔐k.ffAlgEquiv
  let 𝒪₀ : ValuationSubring ↥X.functionField := 𝒪F.comap (φ.symm : ↥X.functionField →+* F)
  have hmem𝒪₀ : ∀ w : ↥X.functionField, w ∈ 𝒪₀ ↔ φ.symm w ∈ 𝒪F := fun w => ValuationSubring.mem_comap
  let ρ : ↥𝒪₀ →+* ↥𝒪F :=
    { toFun := fun w => ⟨φ.symm (w : ↥X.functionField), (hmem𝒪₀ w).mp w.2⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hρ : ∀ w : ↥𝒪₀, (ρ w : F) = φ.symm (w : ↥X.functionField) := fun w => rfl
  have hρbij : Function.Bijective ρ := by
    refine ⟨fun a b h => Subtype.ext (φ.symm.injective (by simpa [hρ] using congrArg (fun w : ↥𝒪F => (w : F)) h)),
      fun y => ⟨⟨φ (y : F), (hmem𝒪₀ _).mpr (by simpa using y.2)⟩, Subtype.ext (by simp [hρ])⟩⟩
  let ρe : ↥𝒪₀ ≃+* ↥𝒪F := RingEquiv.ofBijective ρ hρbij
  let resd₀ : ↥𝒪₀ →+* ↥𝔐k.C.functionField := (ψ : K →+* ↥𝔐k.C.functionField).comp (res.comp ρ)
  have hresd₀ : ∀ w : ↥𝒪₀, resd₀ w = ψ (res (ρ w)) := fun w => rfl
  have hsurj₀ : Function.Surjective resd₀ := ψ.surjective.comp (hsurj.comp hρbij.2)
  have hunit_iff : ∀ w : ↥𝒪₀, IsUnit (ρ w) ↔ IsUnit w := fun w =>
    ⟨fun h => by
      have h2 := h.map ρe.symm.toMonoidHom
      have h3 : ρe.symm.toMonoidHom (ρ w) = w := by
        show ρe.symm (ρe w) = w
        exact ρe.symm_apply_apply w
      rwa [h3] at h2,
    fun h => h.map ρ⟩
  have hker₀ : RingHom.ker resd₀ = IsLocalRing.maximalIdeal ↥𝒪₀ := by
    ext w
    rw [RingHom.mem_ker, hresd₀, map_eq_zero_iff _ ψ.injective, ← RingHom.mem_ker, hker,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, hunit_iff]
  have hcompat₀ : ∀ (a : ↥O) (h : algebraMap (AlgebraicClosure ℚ) ↥X.functionField (a : AlgebraicClosure ℚ) ∈ 𝒪₀),
      resd₀ ⟨_, h⟩ = algebraMap (IsLocalRing.ResidueField ↥O) ↥𝔐k.C.functionField (IsLocalRing.residue ↥O a) := by
    intro a h
    rw [hresd₀, ← ψ.commutes]
    congr 1
    have hmem : algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) ∈ 𝒪F := by
      have h' := (hmem𝒪₀ _).mp h
      have h'' : φ.symm (algebraMap (AlgebraicClosure ℚ) ↥X.functionField (a : AlgebraicClosure ℚ)) =
          algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) := φ.symm_apply_apply _
      rwa [h''] at h'
    rw [← hcompat a hmem]
    congr 1
    apply Subtype.ext
    show φ.symm (φ (algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))) = _
    exact φ.symm_apply_apply _
  have h𝒪₀ : 𝒪₀.toSubring = SemistableModel.localRing X (RingEquiv.refl _) ξ := by
    ext w
    rw [ValuationSubring.mem_toSubring, hmem𝒪₀, ← ValuationSubring.mem_toSubring, h𝒪Fφ,
      ← GC3b21.mem_localRing_refl_iff φ ξ, RingEquiv.apply_symm_apply]
  have hprolong₀ : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥X.functionField x ∈ 𝒪₀ ↔ x ∈ O := by
    intro x
    rw [hmem𝒪₀, ← hprolong x]
    change φ.symm (φ (algebraMap (AlgebraicClosure ℚ) F x)) ∈ 𝒪F ↔ _
    rw [φ.symm_apply_apply]

  have he1₀ : ∀ f₀ : ↥X.functionField, f₀ ≠ 0 →
      ∃ c : AlgebraicClosure ℚ, ∃ h : c • f₀ ∈ 𝒪₀, resd₀ ⟨c • f₀, h⟩ ≠ 0 := by
    intro f₀ hf₀
    obtain ⟨c, h, hne'⟩ := he1 (φ.symm f₀) (by simpa using hf₀)
    have hcf : c • f₀ = φ (c • φ.symm f₀) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingEquiv.apply_symm_apply]
      rfl
    have hmem : c • f₀ ∈ 𝒪₀ := by rw [hmem𝒪₀, hcf, φ.symm_apply_apply]; exact h
    refine ⟨c, hmem, ?_⟩
    rw [hresd₀, map_ne_zero_iff _ ψ.injective]
    have hρc : ρ ⟨c • f₀, hmem⟩ = ⟨c • φ.symm f₀, h⟩ := Subtype.ext (by
      show φ.symm (c • f₀) = c • φ.symm f₀
      rw [hcf, φ.symm_apply_apply])
    rw [hρc]
    exact hne'
  let R₀ : RegularProlongation O ↥X.functionField ↥𝔐k.C.functionField :=
    { integers := 𝒪₀, residue := resd₀, algebraMap_mem_iff := hprolong₀, residue_surjective := hsurj₀,
      ker_residue := hker₀, residue_algebraMap := fun a => hcompat₀ a _, exists_smul_mem := he1₀ }
  have hR₀ : R₀.integers.toSubring = SemistableModel.localRing X (RingEquiv.refl _) ξ := h𝒪₀

  have hLOC : ∀ f : F, f ∈ 𝒪F → (∀ P : Place (AlgebraicClosure ℚ) F,
      (∀ f₁ : F, f₁ ∈ SemistableModel.localRing X φ xQ → f₁ ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f₁ ∈ O,
        (IsUnit (⟨P.evalAt f₁, h⟩ : ↥O) ↔ ∃ f' ∈ SemistableModel.localRing X φ xQ, f₁ * f' = 1)) →
      f ∈ P.toValuationSubring) → f ∈ SemistableModel.localRing X φ xQ := by
    intro f hf hfP
    have hf₀ : φ f ∈ R₀.integers := (hmem𝒪₀ _).mpr (by rw [φ.symm_apply_apply]; exact hf)
    have h0 := AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_valuationSubring_of_mem_smoothLocus O hrk hOuniv X π
      (RingEquiv.refl _) hφ₀ xQ hx hxc hxs ξ hξx hne hξ R₀ hR₀ (φ f) hf₀
      (fun P₀ hP₀ => (GC3b21.mem_comapPlace_iff φₐ P₀ f).mp (hfP _ (hcT P₀ hP₀)))
    exact (GC3b21.mem_localRing_refl_iff φ xQ f).mp h0
  have hgS : g ∈ SemistableModel.localRing X φ xQ := hLOC g hg (fun P hP => (memP P hP).1)
  have hgiS : g⁻¹ ∈ SemistableModel.localRing X φ xQ := hLOC g⁻¹ hgi (fun P hP => (memP P hP).2)

  obtain ⟨hS𝒪₀, Q', -, hQ'read, -, hQ'unit, -, hQ'uniq⟩ :=
    AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring O hrk hOuniv X π (RingEquiv.refl _) hφ₀ xQ hx hxc hxs ξ hξx hne hξ 𝒪₀ resd₀ hsurj₀ hker₀ hcompat₀ h𝒪₀
  let Q₀ : Place (IsLocalRing.ResidueField ↥O) ↥𝔐k.C.functionField := GC3b21.comapPlace ψ.symm Q
  have hQ₀mem : ∀ r : K, ψ r ∈ Q₀.toValuationSubring ↔ r ∈ Q.toValuationSubring := fun r => by
    change ψ r ∈ (GC3b21.comapPlace ψ.symm Q).toValuationSubring ↔ _
    rw [GC3b21.mem_comapPlace_iff, AlgEquiv.symm_apply_apply]
  have hQeq : Q₀ = Q' := hQ'uniq Q₀ (fun f₀ => ⟨hS𝒪₀ f₀, by
    rw [hresd₀, hQ₀mem]
    have hf : φ.symm (f₀ : ↥X.functionField) ∈ SemistableModel.localRing X φ xQ :=
      (GC3b21.mem_localRing_refl_iff φ xQ _).mp (by simpa using f₀.2)
    exact hreadQ _ hf _⟩)
  have hgS₀ : φ g ∈ SemistableModel.localRing X (RingEquiv.refl _) xQ :=
    (GC3b21.mem_localRing_refl_iff φ xQ g).mpr hgS
  have hgiS₀ : φ g⁻¹ ∈ SemistableModel.localRing X (RingEquiv.refl _) xQ :=
    (GC3b21.mem_localRing_refl_iff φ xQ _).mpr hgiS
  have hunitS₀ : IsUnit (⟨φ g, hgS₀⟩ : ↥(SemistableModel.localRing X (RingEquiv.refl _) xQ)) :=
    isUnit_iff_exists_inv.mpr ⟨⟨φ g⁻¹, hgiS₀⟩, Subtype.ext (by
      show φ g * φ g⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hg_ne, map_one])⟩
  have h := ((hQ'unit ⟨φ g, hgS₀⟩ (hS𝒪₀ _)).mp hunitS₀).1
  rw [hresd₀, ← hQeq, GC3b21.ord_comapPlace, AlgEquiv.symm_apply_apply] at h
  have hρg : ρ ⟨φ g, hS𝒪₀ ⟨φ g, hgS₀⟩⟩ = ⟨g, hg⟩ := Subtype.ext (by rw [hρ]; exact φ.symm_apply_apply g)
  rw [hρg] at h
  exact h

end S_AlgebraicCurve_ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem
end P2MW
export P2MW.S_AlgebraicCurve_ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem (solution)
