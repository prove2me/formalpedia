-- Prove2me | solution 1 for AlgebraicCurve.lSpaceOn_setOf_centre_eq_span_integralClosure_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/eab58404-6e1a-5ea2-8916-eeedde54679c

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicCurve_mem_integralClosure_iff_forall_place
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_lSpaceOn_setOf_centre_eq_span_integralClosure_mul
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise

namespace HoloICAux

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover IsLocalRing"

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]

theorem mem_iff_adicValuation_le_one {K : Type u} [Field K] [Algebra k K] (v : Place k K) (f : K) :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  constructor
  · intro hf
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : K) from rfl, v.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  · intro hle
    by_contra hf
    have hf0 : f ≠ 0 := fun h => hf (h ▸ v.toValuationSubring.zero_mem)
    have hfi : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
    have hnu : ¬ IsUnit (⟨f⁻¹, hfi⟩ : v.toValuationSubring) := by
      intro hu
      apply hf
      obtain ⟨w, hw⟩ := hu.exists_left_inv
      have hw' : (w : K) * f⁻¹ = 1 := by
        have := congrArg Subtype.val hw
        simpa using this
      have hwf : (w : K) = f := by
        rw [← mul_inv_cancel_right₀ (inv_ne_zero hf0) (w : K), hw', one_mul, inv_inv]
      rw [← hwf]; exact w.2
    have hlt : v.adicValuation f⁻¹ < 1 := by
      rw [show f⁻¹ = ((⟨f⁻¹, hfi⟩ : v.toValuationSubring) : K) from rfl, v.adicValuation_coe,
        IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem, Place.heightOneSpectrum_asIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnu
    have h1 : 1 < v.adicValuation f := (Valuation.one_lt_val_iff _ hf0).mpr hlt
    exact (not_lt.mpr hle) h1

theorem germ_res_apply' {U V : C.Opens} (h : V ≤ U) (hV : genericPoint C ∈ V) (s : Γ(C, U)) :
    (C.presheaf.germ V (genericPoint C) hV).hom ((C.presheaf.map (homOfLE h).op).hom s) =
      (C.presheaf.germ U (genericPoint C) (h hV)).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res]

theorem algebraMap_eq_germ (U : C.Opens) (hU : genericPoint C ∈ U) (a : k) :
    letI := (baseToFunctionField c).toAlgebra
    algebraMap k C.functionField a =
      (C.presheaf.germ U (genericPoint C) hU).hom ((c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) := by
  have : c.appLE ⊤ U le_top = c.appTop ≫ C.presheaf.map (homOfLE le_top).op := rfl
  rw [this, CommRingCat.hom_comp, RingHom.comp_apply, germ_res_apply' le_top hU]
  rfl

theorem germ_eq_algebraMap_germ (U : C.Opens) (hU : genericPoint C ∈ U) (z : C) (hz : z ∈ U) (s : Γ(C, U)) :
    (C.presheaf.germ U (genericPoint C) hU).hom s =
      algebraMap (C.presheaf.stalk z) C.functionField ((C.presheaf.germ U z hz).hom s) := by
  change _ = (C.presheaf.germ U z hz ≫ C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom s
  rw [TopCat.Presheaf.germ_stalkSpecializes]

theorem isIntegral_iff_isIntegral_range {A K : Type u} [CommRing A] [Field K] (φ : A →+* K) (f : K) :
    (letI := φ.toAlgebra; IsIntegral A f) ↔ IsIntegral φ.range f := by
  letI := φ.toAlgebra
  constructor
  · rintro ⟨p, hp, hpf⟩
    refine ⟨p.map φ.rangeRestrict, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpf
  · rintro ⟨q, hq, hqf⟩
    obtain ⟨p, hpq, -, hp⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective φ.rangeRestrict_surjective q) hq
    refine ⟨p, hp, ?_⟩
    have : (algebraMap (↥φ.range) K).comp φ.rangeRestrict = algebraMap A K := RingHom.ext fun _ => rfl
    rw [← this, ← Polynomial.eval₂_map, hpq]
    exact hqf

end HoloICAux

namespace LocICAux

open IsLocalRing

theorem mem_of_isIntegral {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] (v : Place k K)
    {A : Type u} [CommRing A] (φ : A →+* K) (hφ : ∀ s, φ s ∈ v.toValuationSubring) (f : K)
    (hf : letI := φ.toAlgebra; IsIntegral A f) : f ∈ v.toValuationSubring := by
  letI := φ.toAlgebra
  obtain ⟨p, hp, hpf⟩ := hf
  let ψ : A →+* v.toValuationSubring := φ.codRestrict v.toValuationSubring hφ
  have hint : IsIntegral v.toValuationSubring f := by
    refine ⟨p.map ψ, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpf
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.toValuationSubring) (K := K)).mp hint
  rw [← hy]
  exact y.2

theorem isIso_stalkSpecializes_of_eq {X : TopCat.{u}} (P : TopCat.Presheaf CommRingCat.{u} X)
    {x y : X} (e : x = y) (h : x ⤳ y) : IsIso (P.stalkSpecializes h) := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

theorem centred_fromSpec {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]
    {U : C.Opens} (hUaff : IsAffineOpen U) (hη : genericPoint C ∈ U) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ (v : Place k C.functionField)
      (_hAv : ∀ s : Γ(C, U), (C.presheaf.germ U (genericPoint C) hη).hom s ∈ v.toValuationSubring)
      (y : PrimeSpectrum Γ(C, U))
      (_hy : ∀ s : Γ(C, U), s ∈ y.asIdeal ↔ v.adicValuation ((C.presheaf.germ U (genericPoint C) hη).hom s) < 1),
    ∀ t : C.presheaf.stalk (hUaff.fromSpec y),
      v.adicValuation (algebraMap (C.presheaf.stalk (hUaff.fromSpec y)) C.functionField t) ≤ 1 ∧
      (t ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk (hUaff.fromSpec y)) →
        v.adicValuation (algebraMap (C.presheaf.stalk (hUaff.fromSpec y)) C.functionField t) < 1) := by
  classical
  letI := (baseToFunctionField c).toAlgebra
  intro v hAv y hy
  set A := (C.presheaf.germ U (genericPoint C) hη).hom with hAdef
  set z : C := hUaff.fromSpec y with hzdef
  have hzU : z ∈ U := by
    have : z ∈ Set.range hUaff.fromSpec := ⟨y, rfl⟩
    rwa [hUaff.range_fromSpec] at this
  letI := C.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  haveI : IsLocalization.AtPrime (C.presheaf.stalk z) y.asIdeal := hUaff.isLocalization_stalk' y hzU
  have hφ : ∀ s : Γ(C, U), algebraMap (C.presheaf.stalk z) C.functionField (algebraMap Γ(C, U) (C.presheaf.stalk z) s) = A s :=
    fun s => by rw [hAdef, HoloICAux.germ_eq_algebraMap_germ U hη z hzU]; rfl
  have hvalle : ∀ s : Γ(C, U), v.adicValuation (A s) ≤ 1 := fun s =>
    (HoloICAux.mem_iff_adicValuation_le_one v _).mp (hAv s)
  have hval1 : ∀ s : Γ(C, U), s ∉ y.asIdeal → v.adicValuation (A s) = 1 := by
    intro s hs
    rw [hy] at hs
    exact le_antisymm (hvalle s) (not_lt.mp hs)
  intro t
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl t
  have hs : (s : Γ(C, U)) ∉ y.asIdeal := s.2
  have heq : v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField (IsLocalization.mk' (C.presheaf.stalk z) a s)) =
      v.adicValuation (A a) := by
    have h1 := IsLocalization.mk'_spec (C.presheaf.stalk z) a s
    have h2 := congrArg (fun w => v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField w)) h1
    simp only [map_mul, hφ, hval1 s hs, mul_one] at h2
    exact h2
  refine ⟨heq ▸ hvalle a, fun ht => ?_⟩
  rw [heq, ← hy]
  exact (IsLocalization.AtPrime.mk'_mem_maximal_iff (C.presheaf.stalk z) y.asIdeal a s).mp ht

end LocICAux

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (hpts : ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C))
    (U : C.Opens) [Nonempty U] (hUaff : IsAffineOpen U)
    (z : C) (hzU : z ∈ U) (hz : IsClosed ({z} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField) =
      Submodule.span k ((integralClosure Γ(C, U) C.functionField : Set C.functionField) *
        Set.range (algebraMap (C.presheaf.stalk z) C.functionField)) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI : IsCurveOver k C.functionField := hK
  haveI : PerfectField k := inferInstance
  haveI := AlgebraicCurve.essFiniteType_functionField c
  have hη : genericPoint C ∈ U := ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  set A : Γ(C, U) →+* C.functionField := algebraMap Γ(C, U) C.functionField with hAdef
  have hA : ∀ s, A s = (C.presheaf.germ U (genericPoint C) hη).hom s := fun s => rfl
  set φ : C.presheaf.stalk z →+* C.functionField := algebraMap (C.presheaf.stalk z) C.functionField with hφdef

  let 𝔭 : Ideal Γ(C, U) := (hUaff.primeIdealOf ⟨z, hzU⟩).asIdeal
  letI := C.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  haveI : IsScalarTower Γ(C, U) (C.presheaf.stalk z) C.functionField :=
    AlgebraicGeometry.functionField_isScalarTower (U := U) (x := ⟨z, hzU⟩)
  haveI : IsLocalization.AtPrime (C.presheaf.stalk z) 𝔭 := hUaff.isLocalization_stalk ⟨z, hzU⟩
  have hφA : ∀ s : Γ(C, U), φ (algebraMap Γ(C, U) (C.presheaf.stalk z) s) = A s :=
    fun s => by rw [hA, HoloICAux.germ_eq_algebraMap_germ U hη z hzU]; rfl
  have hconst : ∀ a : k, ∃ t : C.presheaf.stalk z, algebraMap k C.functionField a = φ t := fun a =>
    ⟨algebraMap Γ(C, U) (C.presheaf.stalk z) ((c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)), by
      rw [hφA, hA]; exact HoloICAux.algebraMap_eq_germ c U hη a⟩

  have hOv : ∀ v : Place k C.functionField, (∀ s : C.presheaf.stalk z,
        v.adicValuation (φ s) ≤ 1 ∧ (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) → v.adicValuation (φ s) < 1)) →
      (∀ t, φ t ∈ v.toValuationSubring) ∧ (∀ s : Γ(C, U), A s ∈ v.toValuationSubring) := by
    intro v hv
    have h1 : ∀ t, φ t ∈ v.toValuationSubring := fun t => (HoloICAux.mem_iff_adicValuation_le_one v _).mpr (hv t).1
    exact ⟨h1, fun s => hφA s ▸ h1 _⟩
  apply le_antisymm
  ·
    intro f hf
    rw [AlgebraicCurve.mem_lSpaceOn_iff] at hf

    let Oz : Subalgebra k C.functionField :=
      { φ.range with
        algebraMap_mem' := fun a => by
          obtain ⟨t, ht⟩ := hconst a
          exact ⟨t, ht.symm⟩ }

    have hdomOf : ∀ v : Place k C.functionField, (∀ t, φ t ∈ v.toValuationSubring) →
        ∀ s : C.presheaf.stalk z, v.adicValuation (φ s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) → v.adicValuation (φ s) < 1) := by
      intro v hφv
      have hAv : ∀ s : Γ(C, U), (C.presheaf.germ U (genericPoint C) hη).hom s ∈ v.toValuationSubring :=
        fun s => hA s ▸ hφA s ▸ hφv _
      let ψ : Γ(C, U) →+* v.toValuationSubring := A.codRestrict v.toValuationSubring (fun s => hA s ▸ hAv s)
      let 𝔮 : Ideal Γ(C, U) := Ideal.comap ψ (IsLocalRing.maximalIdeal v.toValuationSubring)
      haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
      let y : PrimeSpectrum Γ(C, U) := ⟨𝔮, inferInstance⟩
      have hy : ∀ s : Γ(C, U), s ∈ y.asIdeal ↔ v.adicValuation ((C.presheaf.germ U (genericPoint C) hη).hom s) < 1 := by
        intro s
        rw [← hA, show A s = ((ψ s : v.toValuationSubring) : C.functionField) from rfl, v.adicValuation_coe,
          IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem, Place.heightOneSpectrum_asIdeal]
        rfl
      have hdom' := LocICAux.centred_fromSpec c hUaff hη v hAv y hy

      have hle : y ≤ hUaff.primeIdealOf ⟨z, hzU⟩ := by
        intro s hs
        by_contra hs𝔭
        have hu : IsUnit (algebraMap Γ(C, U) (C.presheaf.stalk z) s) :=
          IsLocalization.map_units (C.presheaf.stalk z) (⟨s, hs𝔭⟩ : 𝔭.primeCompl)
        have h1 : φ (↑(hu.unit⁻¹) : C.presheaf.stalk z) * A s = 1 := by
          rw [← hφA, ← map_mul, IsUnit.val_inv_mul, map_one]
        have hAs0 : A s ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
        have hinv : (A s)⁻¹ ∈ v.toValuationSubring := by
          rw [inv_eq_of_mul_eq_one_left h1]
          exact hφv _
        have hone : v.adicValuation (A s) = 1 := by
          have hm : A s ∈ v.toValuationSubring := hA s ▸ hAv s
          rw [show A s = ((⟨A s, hm⟩ : v.toValuationSubring) : C.functionField) from rfl, v.adicValuation_coe_eq_one_iff]
          exact isUnit_iff_exists_inv.mpr ⟨⟨(A s)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hAs0)⟩
        have hlt := (hy s).mp hs
        rw [← hA, hone] at hlt
        exact lt_irrefl _ hlt
      have hspec : hUaff.fromSpec y ⤳ z := by
        have h1 : y ⤳ hUaff.primeIdealOf ⟨z, hzU⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hle
        have h2 := h1.map hUaff.fromSpec.base.hom.continuous
        rwa [show hUaff.fromSpec.base.hom (hUaff.primeIdealOf ⟨z, hzU⟩) = z from hUaff.fromSpec_primeIdealOf ⟨z, hzU⟩] at h2
      rcases hpts (hUaff.fromSpec y) with h | h
      ·
        exfalso
        apply v.ne_top'
        refine eq_top_iff.mpr fun g _ => (HoloICAux.mem_iff_adicValuation_le_one v g).mpr ?_
        have hsurj : Function.Surjective (algebraMap (C.presheaf.stalk (hUaff.fromSpec y)) C.functionField) := by
          change Function.Surjective (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom
          haveI := LocICAux.isIso_stalkSpecializes_of_eq C.presheaf h.symm
            ((genericPoint_spec C).specializes (trivial : hUaff.fromSpec y ∈ (⊤ : Set C)))
          exact (asIso (C.presheaf.stalkSpecializes
            ((genericPoint_spec C).specializes (trivial : hUaff.fromSpec y ∈ (⊤ : Set C))))).commRingCatIsoToRingEquiv.surjective
        obtain ⟨t, rfl⟩ := hsurj g
        exact (hdom' t).1
      ·
        have hzz : z = hUaff.fromSpec y := by
          have : z ∈ closure ({hUaff.fromSpec y} : Set C) := specializes_iff_mem_closure.mp hspec
          rwa [h.closure_eq, Set.mem_singleton_iff] at this
        clear_value φ
        subst hzz
        simpa only [hφdef] using hdom'

    have hint : f ∈ integralClosure Oz C.functionField := by
      rw [AlgebraicCurve.mem_integralClosure_iff_forall_place Oz f]
      intro v hOzv
      have hφv : ∀ t, φ t ∈ v.toValuationSubring := fun t => hOzv ⟨t, rfl⟩
      have := hf v (hdomOf v hφv)
      simp only [Finsupp.zero_apply, WithZero.exp_zero] at this
      exact (HoloICAux.mem_iff_adicValuation_le_one v f).mpr this
    have hint' : IsIntegral (C.presheaf.stalk z) f := by
      have h1 := (HoloICAux.isIntegral_iff_isIntegral_range φ f).mpr hint
      exact h1

    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization 𝔭.primeCompl f hint'
    have hsm : m • f = A m * f := by rw [Submonoid.smul_def, Algebra.smul_def]
    rw [hsm] at hm
    have hu : IsUnit (algebraMap Γ(C, U) (C.presheaf.stalk z) m) := IsLocalization.map_units (C.presheaf.stalk z) m
    have h1 : φ (↑(hu.unit⁻¹) : C.presheaf.stalk z) * A m = 1 := by
      rw [← hφA, ← map_mul, IsUnit.val_inv_mul, map_one]
    have hf' : f = (A m * f) * φ (↑(hu.unit⁻¹) : C.presheaf.stalk z) := by
      rw [mul_comm (A m) f, mul_assoc, mul_comm (A m), h1, mul_one]
    rw [hf']
    exact Submodule.subset_span (Set.mul_mem_mul hm ⟨_, rfl⟩)
  ·
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, _, ⟨t, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, AlgebraicCurve.mem_lSpaceOn_iff]
    intro v hv
    simp only [Finsupp.zero_apply, WithZero.exp_zero]
    obtain ⟨hφv, hAv⟩ := hOv v hv
    rw [← HoloICAux.mem_iff_adicValuation_le_one]
    refine mul_mem ?_ (hφv t)
    exact LocICAux.mem_of_isIntegral v A hAv b hb

end S_AlgebraicCurve_lSpaceOn_setOf_centre_eq_span_integralClosure_mul
end P2MW
export P2MW.S_AlgebraicCurve_lSpaceOn_setOf_centre_eq_span_integralClosure_mul (solution)
