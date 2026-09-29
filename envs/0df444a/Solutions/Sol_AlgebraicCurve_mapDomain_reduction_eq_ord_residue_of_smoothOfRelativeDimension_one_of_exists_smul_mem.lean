-- Prove2me | solution 1 for AlgebraicCurve.mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/108c97a7-dbbd-5c5f-804d-dc8706d285b2

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicCurve_exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.SemistableModel.Descent.commRing AlgebraicCurve.SemistableModel.Descent.isNoetherianRing AlgebraicCurve.SemistableModel.Descent.isProper₀ AlgebraicCurve.SemistableModel.Descent.isIntegral₀ AlgebraicCurve.SemistableModel.isProper AlgebraicCurve.SemistableModel.flat AlgebraicCurve.SemistableModel.Descent.henselianLocalRing AlgebraicCurve.SemistableModel.locallyOfFinitePresentation AlgebraicCurve.SemistableModel.Descent.isLocalHom AlgebraicCurve.SemistableModel.Descent.isAlgebraic AlgebraicCurve.SemistableModel.Descent.isAlgebraic_F₀ AlgebraicCurve.SemistableModel.Descent.locallyOfFinitePresentation₀ AlgebraicCurve.SemistableModel.isIntegral AlgebraicCurve.SemistableModel.Descent.flat₀ AlgebraicCurve.SemistableModel.isClosedImmersion_specMap_residue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.SemistableModel.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.SemistableModel.mk.sizeOf_spec AlgebraicCurve.SemistableModel.Descent.mk.injEq AlgebraicCurve.SemistableModel.Descent.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve TopologicalSpace

universe v w

namespace GC3Assembly

open AlgebraicCurve

theorem map_units_zpow {A L : Type*} [CommRing A] [Field L] (φ : A →+* L) (x : Aˣ) (n : ℤ) :
    φ ((x ^ n : Aˣ) : A) = (φ (x : A)) ^ n := by
  have h := congrArg Units.val (map_zpow (Units.map (φ : A →* L)) x n)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at h
  simpa using h

theorem ord_prod {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] (v : Place K₁ F₁)
    {ι : Type*} (s : Finset ι) (f : ι → F₁) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (r : α → β) (D : α →₀ ℤ) (Q : β) :
    Finsupp.mapDomain r D Q = ∑ P ∈ D.support.filter (fun P => r P = Q), D P := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.single_apply]

end GC3Assembly

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
    ∀ f : ↥𝒪F, res f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain red D Q = Q.ord (res f) := by
  classical
  intro f hf D hD Q

  have hpar := AlgebraicCurve.exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one O p hp hO X π F 𝔐 e he K 𝔐k ek hek 𝒪F res h𝒪F hres hsurj hker red hred
  choose u hu huinv hord1 hord0 hordres using hpar
  have hu0 : ∀ P, u P ≠ 0 := fun P h0 => by have := hord1 P; rw [h0, Place.ord_zero] at this; exact zero_ne_one this
  have hf0 : (f : F) ≠ 0 := fun h0 => hf (by rw [show f = 0 from Subtype.ext h0, map_zero])

  let U : Place (AlgebraicClosure ℚ) F → (↥𝒪F)ˣ := fun P =>
    ⟨⟨u P, hu P⟩, ⟨(u P)⁻¹, huinv P⟩, Subtype.ext (mul_inv_cancel₀ (hu0 P)), Subtype.ext (inv_mul_cancel₀ (hu0 P))⟩
  have hUval : ∀ P, ((U P : ↥𝒪F) : F) = u P := fun P => rfl

  set S : Finset (Place (AlgebraicClosure ℚ) F) := D.support.filter (fun P => red P = Q) with hS
  have hSred : ∀ P ∈ S, red P = Q := fun P hP => (Finset.mem_filter.1 hP).2

  let g : ↥𝒪F := f * ∏ P ∈ S, ((U P ^ (-(D P)) : (↥𝒪F)ˣ) : ↥𝒪F)
  have hgval : ((g : ↥𝒪F) : F) = (f : F) * ∏ P ∈ S, (u P) ^ (-(D P)) := by
    show 𝒪F.subtype g = _
    rw [map_mul, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun P _ => by rw [GC3Assembly.map_units_zpow]; rfl
  have hresg : res g = res f * ∏ P ∈ S, (res ⟨u P, hu P⟩) ^ (-(D P)) := by
    rw [map_mul, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun P _ => by rw [GC3Assembly.map_units_zpow]
  have hresu : ∀ P ∈ S, res ⟨u P, hu P⟩ ≠ 0 := fun P hP h0 => by
    have := hordres P; rw [hSred P hP, h0, Place.ord_zero] at this; exact zero_ne_one this
  have hresg0 : res g ≠ 0 := by
    rw [hresg]
    exact mul_ne_zero hf (Finset.prod_ne_zero_iff.2 fun P hP => zpow_ne_zero _ (hresu P hP))

  have hordg : ∀ P' : Place (AlgebraicClosure ℚ) F, red P' = Q → P'.ord ((g : ↥𝒪F) : F) = 0 := by
    intro P' hP'
    rw [hgval, P'.ord_mul hf0 (Finset.prod_ne_zero_iff.2 fun P _ => zpow_ne_zero _ (hu0 P)),
      GC3Assembly.ord_prod P' S _ (fun P _ => zpow_ne_zero _ (hu0 P)), ← hD P']
    simp_rw [Place.ord_zpow]
    have hterm : ∀ P ∈ S, -(D P) * P'.ord (u P) = if P = P' then -(D P') else 0 := by
      intro P hP
      by_cases hPP : P = P'
      · subst hPP; rw [if_pos rfl, hord1, mul_one]
      · rw [if_neg hPP, hord0 P P' (by rw [hSred P hP, hP']) (Ne.symm hPP), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    by_cases hP'S : P' ∈ S
    · rw [if_pos hP'S]; ring
    · rw [if_neg hP'S, add_zero]
      have : P' ∉ D.support := fun h => hP'S (Finset.mem_filter.2 ⟨h, hP'⟩)
      simpa using this

  have hloc := AlgebraicCurve.ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem O p hp hO X π O₀ j hj hju π₀ ε₀ e₀ he₀ F 𝔐 e he K 𝔐k ek hek 𝒪F res h𝒪F hres hsurj hker he1 red hred
    ((g : ↥𝒪F) : F) g.2 (by simpa using hresg0) Q hordg

  have hordQ : Q.ord (res g) = Q.ord (res f) - ∑ P ∈ S, D P := by
    rw [hresg, Q.ord_mul hf (Finset.prod_ne_zero_iff.2 fun P hP => zpow_ne_zero _ (hresu P hP)),
      GC3Assembly.ord_prod Q S _ (fun P hP => zpow_ne_zero _ (hresu P hP))]
    simp_rw [Place.ord_zpow]
    rw [Finset.sum_congr rfl fun P hP => by rw [← hSred P hP, hordres P, mul_one], Finset.sum_neg_distrib]
    ring
  have hloc' : Q.ord (res g) = 0 := by simpa using hloc
  rw [GC3Assembly.mapDomain_apply_eq_sum]
  linarith

end S_AlgebraicCurve_mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem
end P2MW
export P2MW.S_AlgebraicCurve_mapDomain_reduction_eq_ord_residue_of_smoothOfRelativeDimension_one_of_exists_smul_mem (solution)
