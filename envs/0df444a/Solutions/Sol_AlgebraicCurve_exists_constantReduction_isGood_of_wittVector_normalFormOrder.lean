-- Prove2me | solution 1 for AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/43f4479a-d736-59c4-b705-2e1e7fd849cc

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ValuationSubring_ResidueValuationSubring
import Theorems.Thm_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic
import Theorems.Thm_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg
import Theorems.Thm_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add
import Theorems.Thm_AlgebraicCurve_exists_regularProlongation_of_transcendental
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
import Theorems.Thm_AlgebraicCurve_genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
import Theorems.Thm_AlgebraicCurve_finrank_adjoin_eq_card_of_mul_mem_span_of_fractions
import Theorems.Thm_AlgebraicCurve_genusFF_le_of_normalForm
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_algEquiv_apply_eq_residue_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_constantReduction_isGood_of_wittVector_normalFormOrder
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_constantReduction_isGood_of_wittVector_normalFormOrder.AlgebraicCurve IsLocalRing Polynomial"
open scoped TensorProduct

universe u v

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ConstantReduction genusFF RegularProlongation IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed exists_regularProlongation_of_transcendental RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp isCurveOver_of_isAlgClosed_of_transcendental exists_placeMap_mapDomain_eq_ord_of_good_constantReduction finrank_adjoin_eq_card_of_mul_mem_span_of_fractions genusFF_le_of_normalForm RegularProlongation.exists_algEquiv_apply_eq_residue_of_transcendental"
namespace WittNormalFormReduction
p2m_open "AlgebraicCurve"

theorem charZero_wittVector (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨q, hq⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) q with hqp | rfl
  · exfalso
    have hq0 : (q : WittVector p K) = 0 := CharP.cast_eq_zero (WittVector p K) q
    have hqK : (q : K) = 0 := by
      have h := congrArg (WittVector.constantCoeff : WittVector p K →+* K) hq0
      rwa [map_natCast, map_zero] at h
    have hpq : p ∣ q := (CharP.cast_eq_zero_iff K p q).mp hqK
    have hqe : q = p := ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hqp).mp hpq).symm
    subst hqe
    have h1 := congrArg (fun w : WittVector q K => w.coeff 1) hq0
    simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at h1
    exact one_ne_zero h1
  · exact CharP.charP_to_charZero (WittVector p K)

theorem exists_scale {L : Type u} [Field L] (V : ValuationSubring L) {ι : Type*} (T : Finset ι)
    (t : ι → L) (h : ∃ i ∈ T, t i ≠ 0) :
    ∃ α : L, (∀ i ∈ T, α * t i ∈ V) ∧ ∃ i ∈ T, α * t i = 1 := by
  classical
  obtain ⟨i₀, hi₀T, hi₀⟩ := h
  obtain ⟨j, hjT, hj⟩ := Finset.exists_max_image T (fun i => V.valuation (t i)) ⟨i₀, hi₀T⟩
  have hj0 : t j ≠ 0 := by
    intro h0
    have := hj i₀ hi₀T
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi₀ this
  refine ⟨(t j)⁻¹, fun i hi => ?_, j, hjT, inv_mul_cancel₀ hj0⟩
  apply V.mem_of_valuation_le_one
  rw [map_mul, map_inv₀]
  have hle := hj i hi
  have hne : V.valuation (t j) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  calc (V.valuation (t j))⁻¹ * V.valuation (t i)
      ≤ (V.valuation (t j))⁻¹ * V.valuation (t j) := by gcongr
    _ = 1 := inv_mul_cancel₀ hne

section Rank

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]

theorem krullDimLE_one_of_wittVector
    (V : ValuationSubring (AlgebraicClosure (FractionRing (WittVector p K))))
    (hV : ∀ a : WittVector p K,
      algebraMap (WittVector p K) (AlgebraicClosure (FractionRing (WittVector p K))) a ∈ V) :
    Ring.KrullDimLE 1 V := by
  set R₀ := WittVector p K
  set K₀ := FractionRing R₀
  set L := AlgebraicClosure K₀

  let W₀ : ValuationSubring K₀ :=
    { toSubring := (algebraMap R₀ K₀).range
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger R₀ x with h | h
        · exact Or.inl h
        · exact Or.inr h }
  have hW₀ : ∀ x : K₀, x ∈ W₀ ↔ x ∈ (algebraMap R₀ K₀).range := fun _ => Iff.rfl

  have hinj : Function.Injective (algebraMap R₀ K₀) := IsFractionRing.injective R₀ K₀
  let eW : R₀ ≃+* W₀ :=
    (RingEquiv.ofBijective (algebraMap R₀ K₀).rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap R₀ K₀).rangeRestrict_surjective⟩).trans
      (RingEquiv.refl _)
  have hdimW₀ : ringKrullDim W₀ = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv eW]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one R₀

  set V₀ : ValuationSubring K₀ := V.comap (algebraMap K₀ L) with hV₀
  have hle : W₀ ≤ V₀ := by
    intro x hx
    obtain ⟨a, rfl⟩ := (hW₀ x).mp hx
    show algebraMap K₀ L (algebraMap R₀ K₀ a) ∈ V
    rw [← IsScalarTower.algebraMap_apply]
    exact hV a

  have hV₀dim : ringKrullDim V₀ ≤ 1 := by
    have h := ValuationSubring.ringKrullDim_eq_ringKrullDim_residueValuationSubring_add W₀ V₀ hle
    rw [hdimW₀] at h
    have hnn : 0 ≤ ringKrullDim (W₀.residueValuationSubring V₀ hle) := ringKrullDim_nonneg_of_nontrivial

    rcases (WithBot.ne_bot_iff_exists).mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot hnn) with ⟨a, ha⟩
    rcases eq_or_ne (ringKrullDim V₀) ⊥ with hb | hb
    · rw [hb]; exact bot_le
    obtain ⟨b, hb'⟩ := (WithBot.ne_bot_iff_exists).mp hb
    rw [← ha, ← hb'] at h
    rw [← hb']
    have h' : (1 : WithBot ℕ∞) = ((a + b : ℕ∞) : WithBot ℕ∞) := by rw [h]; rfl
    have h'' : (a + b : ℕ∞) = 1 := by exact_mod_cast h'.symm
    have : b ≤ 1 := by rw [← h'']; exact le_add_self
    exact_mod_cast this

  rw [Ring.krullDimLE_iff]
  have h := ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg (K := K₀) (L := L) V
  rw [trdeg_eq_zero, map_zero] at h
  simpa using h.trans (by simpa using hV₀dim)

end Rank

end AlgebraicCurve.WittNormalFormReduction

set_option maxHeartbeats 4000000 in
open AlgebraicCurve.WittNormalFormReduction in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (Bt : Type u) [CommRing Bt] [Algebra (WittVector p K)[X] Bt]
    (bt : Module.Basis (Fin (n + 1)) (WittVector p K)[X] Bt) (d : Fin (n + 1) → ℕ)
    (hbt0 : bt 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((bt.repr (bt i * bt j)) k).natDegree ≤ d i + d j - d k)
    (F : Type v) [Field F] [Algebra K F] (ψ : Bt →+* F)
    (hψC : ∀ a : WittVector p K,
      ψ (algebraMap (WittVector p K)[X] Bt (Polynomial.C a)) = algebraMap K F (a.coeff 0))
    (hψind : ∀ c : Fin (n + 1) → K[X],
      ∑ i, Polynomial.aeval (ψ (algebraMap (WittVector p K)[X] Bt Polynomial.X)) (c i) *
        ψ (bt i) = 0 → c = 0)
    (hψfrac : ∀ z : F, ∃ f h : Bt, ψ h ≠ 0 ∧ z * ψ h = ψ f)
    (hgen : genusFF K F + n = ∑ i, d i) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L) (A : ValuationSubring L)
      (e : IsLocalRing.ResidueField A ≃+* K)
      (F' : Type u) (_ : Field F') (_ : Algebra L F') (_ : Algebra (IsLocalRing.ResidueField A) F),
      algebraMap (IsLocalRing.ResidueField A) F = (algebraMap K F).comp e.toRingHom ∧
        (∃ x : F', Transcendental L x ∧
          FiniteDimensional (IntermediateField.adjoin L ({x} : Set F')) F') ∧
        ∃ R : ConstantReduction A F' F, R.IsGood := by
  classical

  set R₀ := WittVector p K with hR₀
  haveI : CharZero R₀ := charZero_wittVector p K
  set K₀ := FractionRing R₀ with hK₀
  set L : Type u := AlgebraicClosure K₀ with hL
  have hinjR₀L : Function.Injective (algebraMap R₀ L) := by
    rw [IsScalarTower.algebraMap_eq R₀ K₀ L]
    exact (algebraMap K₀ L).injective.comp (IsFractionRing.injective R₀ K₀)
  haveI : FaithfulSMul R₀ L := (faithfulSMul_iff_algebraMap_injective _ L).mpr hinjR₀L
  haveI : Algebra.IsAlgebraic R₀ L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R₀) (K := K₀) (C := L)).mpr inferInstance
  haveI : CharZero L := charZero_of_injective_algebraMap hinjR₀L
  obtain ⟨V, hV, φ, hVmax, hφ⟩ :=
    WittVector.exists_valuationSubring_residueField_equiv_of_isAlgebraic p K L
  set k := IsLocalRing.ResidueField V with hk
  let e : k ≃+* K := φ.symm
  have he : ∀ a : R₀, e (IsLocalRing.residue V ⟨algebraMap R₀ L a, hV a⟩) = a.coeff 0 := fun a => by
    rw [← hφ a]; exact φ.symm_apply_apply _
  haveI : Ring.KrullDimLE 1 V := krullDimLE_one_of_wittVector p K V hV

  letI algkF : Algebra k F := ((algebraMap K F).comp e.toRingHom).toAlgebra
  have halgkF : algebraMap k F = (algebraMap K F).comp e.toRingHom := rfl
  have halgkF' : ∀ c : k, algebraMap k F c = algebraMap K F (e c) := fun _ => rfl

  set P₀ := (WittVector p K)[X] with hP₀
  let iV : R₀ →+* V := (algebraMap R₀ L).codRestrict V hV
  have hiV : ∀ a, ((iV a : V) : L) = algebraMap R₀ L a := fun _ => rfl
  letI algPV : Algebra P₀ V[X] := (Polynomial.mapRingHom iV).toAlgebra
  letI algPL : Algebra P₀ L[X] := (Polynomial.mapRingHom (algebraMap R₀ L)).toAlgebra
  have halgPV : ∀ q : P₀, algebraMap P₀ V[X] q = q.map iV := fun _ => rfl
  have halgPL : ∀ q : P₀, algebraMap P₀ L[X] q = q.map (algebraMap R₀ L) := fun _ => rfl

  let BA := V[X] ⊗[P₀] Bt
  let BL := L[X] ⊗[P₀] Bt
  let bA : Module.Basis (Fin (n + 1)) V[X] BA := Algebra.TensorProduct.basis V[X] bt
  let bL : Module.Basis (Fin (n + 1)) L[X] BL := Algebra.TensorProduct.basis L[X] bt
  have hbA : ∀ i, bA i = 1 ⊗ₜ bt i := fun i => Algebra.TensorProduct.basis_apply bt i
  have hbL : ∀ i, bL i = 1 ⊗ₜ bt i := fun i => Algebra.TensorProduct.basis_apply bt i

  let inclVL : V[X] →ₐ[P₀] L[X] :=
    { Polynomial.mapRingHom V.subtype with
      commutes' := fun q => by
        show (q.map iV).map V.subtype = q.map (algebraMap R₀ L)
        rw [Polynomial.map_map]
        rfl }
  have hinclVL : ∀ q : V[X], inclVL q = q.map V.subtype := fun _ => rfl
  let ι : BA →ₐ[P₀] BL := Algebra.TensorProduct.map inclVL (AlgHom.id P₀ Bt)
  have hιtmul : ∀ (q : V[X]) (b : Bt), ι (q ⊗ₜ b) = (q.map V.subtype) ⊗ₜ b := fun q b => by
    show Algebra.TensorProduct.map inclVL (AlgHom.id P₀ Bt) (q ⊗ₜ b) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hιsmul : ∀ (q : V[X]) (u : BA), ι (q • u) = (q.map V.subtype) • ι u := by
    intro q u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', hιtmul, smul_eq_mul, hιtmul, Polynomial.map_mul,
        TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  have hιbA : ∀ i, ι (bA i) = bL i := fun i => by
    rw [hbA, hbL, hιtmul, Polynomial.map_one]
  have hιsum : ∀ c : Fin (n + 1) → V[X], ι (∑ i, c i • bA i) = ∑ i, (c i).map V.subtype • bL i := by
    intro c
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hιsmul, hιbA]
  have hιinj : Function.Injective ι := by
    intro u w huw
    rw [← sub_eq_zero] at huw ⊢
    rw [← map_sub] at huw
    set d := u - w
    have hd : d = ∑ i, (bA.repr d i) • bA i := (bA.sum_repr d).symm
    rw [hd, hιsum] at huw
    have hzero : ∀ i, (bA.repr d i).map V.subtype = 0 := by
      have := bL.repr_sum_self fun i => (bA.repr d i).map V.subtype
      rw [huw, map_zero] at this
      exact fun i => by simpa using (congrFun this i).symm
    rw [hd]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : bA.repr d i = 0 :=
      Polynomial.map_injective V.subtype V.subtype_injective (by rw [hzero i, Polynomial.map_zero])
    rw [this, zero_smul]

  let cL : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → L[X] := fun i j k => bL.repr (bL i * bL j) k
  have hcL : ∀ i j k, cL i j k = (bt.repr (bt i * bt j) k).map (algebraMap R₀ L) := by
    intro i j k
    show bL.repr (bL i * bL j) k = _
    rw [hbL, hbL, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul,
      one_smul, Finsupp.mapRange_apply]
    rfl
  have hdegL : ∀ i j k, i ≠ 0 → j ≠ 0 → (cL i j k).natDegree ≤ d i + d j - d k := by
    intro i j k hi hj
    rw [hcL]; exact (Polynomial.natDegree_map_le).trans (hdeg i j k hi hj)
  have hprodL : ∀ i j, bL i * bL j = ∑ k, cL i j k • bL k := fun i j => (bL.sum_repr (bL i * bL j)).symm
  have hbL0 : bL 0 = 1 := by rw [hbL, hbt0]; rfl
  have hbA0 : bA 0 = 1 := by rw [hbA, hbt0]; rfl

  set xb : F := ψ (algebraMap P₀ Bt X) with hxb
  letI algPF : Algebra P₀ F := (ψ.comp (algebraMap P₀ Bt)).toAlgebra
  have halgPF : ∀ q : P₀, algebraMap P₀ F q = ψ (algebraMap P₀ Bt q) := fun _ => rfl
  let ψa : Bt →ₐ[P₀] F := { ψ with commutes' := fun _ => rfl }
  have hψa : ∀ b, ψa b = ψ b := fun _ => rfl
  let cVF : V →+* F := (algebraMap K F).comp (e.toRingHom.comp (IsLocalRing.residue V))
  have hcVF : ∀ a : V, cVF a = algebraMap K F (e (IsLocalRing.residue V a)) := fun _ => rfl
  let fA₀ : V[X] →+* F := Polynomial.eval₂RingHom cVF xb
  have hψalg : ∀ q : P₀, ψ (algebraMap P₀ Bt q) =
      Polynomial.aeval xb (q.map (WittVector.constantCoeff : R₀ →+* K)) := by
    intro q
    have h1 : (ψ.comp (algebraMap P₀ Bt)) =
        (Polynomial.aeval xb : K[X] →ₐ[K] F).toRingHom.comp
          (Polynomial.mapRingHom (WittVector.constantCoeff : R₀ →+* K)) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]
        rw [hψC, WittVector.constantCoeff_apply]
      · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
        rfl
    exact congrArg (fun φ : P₀ →+* F => φ q) h1
  have hfA₀ : ∀ q : V[X], fA₀ q =
      Polynomial.aeval xb (q.map (e.toRingHom.comp (IsLocalRing.residue V))) := by
    intro q
    show Polynomial.eval₂ cVF xb q = _
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  let fA : V[X] →ₐ[P₀] F :=
    { fA₀ with
      commutes' := fun q => by
        show fA₀ (q.map iV) = ψ (algebraMap P₀ Bt q)
        rw [hfA₀, hψalg, Polynomial.map_map]
        congr 2
        ext a
        exact he a }
  have hfA : ∀ q, fA q = fA₀ q := fun _ => rfl
  let ρ : BA →ₐ[P₀] F := Algebra.TensorProduct.lift fA ψa fun _ _ => Commute.all _ _
  have hρtmul : ∀ (q : V[X]) (b : Bt), ρ (q ⊗ₜ b) = fA₀ q * ψ b := fun q b =>
    Algebra.TensorProduct.lift_tmul fA ψa (fun _ _ => Commute.all _ _) q b
  have hρone : fA₀ 1 = 1 := map_one fA₀
  have hρbA : ∀ i, ρ (bA i) = ψ (bt i) := fun i => by
    have h := hρtmul (1 : V[X]) (bt i)
    rw [hρone, one_mul] at h
    rw [hbA]
    exact h
  have hρsmul : ∀ (q : V[X]) (u : BA), ρ (q • u) = fA₀ q * ρ u := by
    intro q u
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hρtmul, map_one,
      mul_one]
  have hρsum : ∀ c : Fin (n + 1) → V[X], ρ (∑ i, c i • bA i) = ∑ i, fA₀ (c i) * ψ (bt i) := by
    intro c
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hρsmul, hρbA]

  have hkerρ : ∀ u : BA, ρ u = 0 → ∀ i n, ((bA.repr u i).coeff n) ∈ IsLocalRing.maximalIdeal V := by
    intro u hu i n
    have hu' : ρ (∑ i, (bA.repr u i) • bA i) = 0 := by rwa [bA.sum_repr u]
    rw [hρsum] at hu'
    simp only [hfA₀] at hu'
    have := hψind (fun i => (bA.repr u i).map (e.toRingHom.comp (IsLocalRing.residue V))) hu'
    have hi := congrFun this i
    simp only [Pi.zero_apply] at hi
    have hn := congrArg (fun q : K[X] => q.coeff n) hi
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.coe_comp, Function.comp_apply] at hn
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact e.injective (by rw [map_zero]; exact hn)

  have hgauss : ∀ u : BL, u ≠ 0 → ∃ (α : L) (f : BA), ι f = α • u ∧ ρ f ≠ 0 := by
    intro u hu

    let uc : Fin (n + 1) → L[X] := fun i => bL.repr u i
    have hu' : u = ∑ i, uc i • bL i := (bL.sum_repr u).symm
    obtain ⟨i₀, hi₀⟩ : ∃ i, uc i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hu
      rw [hu']
      exact Finset.sum_eq_zero fun i _ => by rw [hall i, zero_smul]
    obtain ⟨n₀, hn₀⟩ : ∃ n, (uc i₀).coeff n ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hi₀ (Polynomial.ext fun n => by rw [hall n, Polynomial.coeff_zero])
    let N : ℕ := Finset.univ.sup fun i => (uc i).natDegree
    have hN : ∀ i, (uc i).natDegree ≤ N := fun i => Finset.le_sup (f := fun i => (uc i).natDegree) (Finset.mem_univ i)
    let T : Finset (Fin (n + 1) × ℕ) := Finset.univ ×ˢ Finset.range (N + 1)
    have hn₀N : n₀ ≤ N := by
      by_contra h
      exact hn₀ (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hN i₀) (not_le.mp h)))
    obtain ⟨α, hαV, ⟨i₁, n₁⟩, hi₁T, hα1⟩ :=
      exists_scale V T (fun q => (uc q.1).coeff q.2)
        ⟨(i₀, n₀), Finset.mk_mem_product (Finset.mem_univ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn₀N)), hn₀⟩

    have hcoeffV : ∀ i n, (α • uc i).coeff n ∈ V := by
      intro i n
      rw [Polynomial.coeff_smul, smul_eq_mul]
      by_cases hn : n ≤ N
      · exact hαV (i, n) (Finset.mk_mem_product (Finset.mem_univ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hN i) (not_le.mp hn)), mul_zero]
        exact V.zero_mem
    have hsub : ∀ i, (↑(α • uc i).coeffs : Set L) ⊆ (V.toSubring : Set L) := by
      intro i x hx
      obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hcoeffV i n
    let c : Fin (n + 1) → V[X] := fun i => (α • uc i).toSubring V.toSubring (hsub i)
    have hc : ∀ i, (c i).map V.subtype = α • uc i := fun i => Polynomial.map_toSubring _ _ (hsub i)
    refine ⟨α, ∑ i, c i • bA i, ?_, ?_⟩
    · rw [hιsum, hu', Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hc, smul_assoc]
    · rw [hρsum]
      simp only [hfA₀]
      intro h0
      have := congrFun (hψind _ h0) i₁
      simp only [Pi.zero_apply] at this
      have hcoef := congrArg (fun q : K[X] => q.coeff n₁) this
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.coe_comp, Function.comp_apply] at hcoef
      have h1 : ((c i₁).coeff n₁ : L) = 1 := by
        have := congrArg (fun q : L[X] => q.coeff n₁) (hc i₁)
        simp only [Polynomial.coeff_map, Polynomial.coeff_smul, smul_eq_mul] at this
        exact this.trans hα1
      have h1' : (c i₁).coeff n₁ = 1 := Subtype.ext h1
      rw [h1', map_one] at hcoef
      simp at hcoef

  haveI : Nontrivial BL := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : bL.repr (bL 0) 0 = 1 := by rw [bL.repr_self]; simp
    rw [hbL0, ← h, LinearEquiv.map_zero, Finsupp.zero_apply] at h1
    exact zero_ne_one h1
  haveI : NoZeroDivisors BL := by
    refine ⟨fun {u w} huw => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨α, f, hf, hρf⟩ := hgauss u hne.1
    obtain ⟨β, h, hh, hρh⟩ := hgauss w hne.2
    have : ι (f * h) = 0 := by
      rw [map_mul, hf, hh, smul_mul_smul_comm, huw, smul_zero]
    have hfh : f * h = 0 := hιinj (by rw [this, map_zero])
    have := congrArg ρ hfh
    rw [map_mul, map_zero] at this
    exact (mul_ne_zero hρf hρh) this
  haveI : IsDomain BL := NoZeroDivisors.to_isDomain BL

  let F' : Type u := FractionRing BL
  have hinjF' : Function.Injective (algebraMap BL F') := IsFractionRing.injective BL F'
  let jL : L →+* F' := (algebraMap BL F').comp ((algebraMap L[X] BL).comp Polynomial.C)
  letI algLF' : Algebra L F' := jL.toAlgebra
  have halgLF' : ∀ a : L, algebraMap L F' a = algebraMap BL F' (algebraMap L[X] BL (Polynomial.C a)) :=
    fun _ => rfl
  let evL : L[X] →+* F' := (algebraMap BL F').comp (algebraMap L[X] BL)
  set y' : F' := algebraMap BL F' (algebraMap L[X] BL X) with hy'
  have hevL : ∀ q : L[X], evL q = Polynomial.aeval y' q := by
    intro q
    have : evL = (Polynomial.aeval y' : L[X] →ₐ[L] F').toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]
        rfl
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
        rfl
    exact congrArg (fun φ : L[X] →+* F' => φ q) this
  have hevL' : ∀ q : L[X], algebraMap BL F' (algebraMap L[X] BL q) = Polynomial.aeval y' q := hevL
  let s : Fin (n + 1) → F' := fun i => algebraMap BL F' (bL i)
  have hs0 : s 0 = 1 := by simp only [s, hbL0, map_one]
  have hsmulF' : ∀ (q : L[X]) (u : BL), algebraMap BL F' (q • u) = Polynomial.aeval y' q * algebraMap BL F' u := by
    intro q u
    rw [Algebra.smul_def, map_mul, hevL']
  have hsumF' : ∀ d : Fin (n + 1) → L[X],
      algebraMap BL F' (∑ i, d i • bL i) = ∑ i, Polynomial.aeval y' (d i) * s i := by
    intro d
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hsmulF' _ _
  have hmulF' : ∀ i j, s i * s j = ∑ k, Polynomial.aeval y' (cL i j k) * s k := by
    intro i j
    show algebraMap BL F' (bL i) * algebraMap BL F' (bL j) = _
    rw [← map_mul, hprodL, hsumF']
  have hindF' : ∀ d : Fin (n + 1) → L[X], ∑ i, Polynomial.aeval y' (d i) * s i = 0 → d = 0 := by
    intro d hd
    rw [← hsumF'] at hd
    have hd' : ∑ i, d i • bL i = 0 := hinjF' (by rw [hd, map_zero])
    have := bL.repr_sum_self d
    rw [hd', LinearEquiv.map_zero] at this
    funext i
    simpa using (congrFun this i).symm
  have hy'tr : Transcendental L y' := by
    rw [transcendental_iff]
    intro q hq
    have h := hindF' (Pi.single 0 q) (by
      rw [Fin.sum_univ_succ, hs0]
      simp [hq])
    simpa using congrFun h 0
  have hfracF' : ∀ z : F', ∃ cu cv : Fin (n + 1) → L[X],
      ∑ i, Polynomial.aeval y' (cv i) * s i ≠ 0 ∧
        z * ∑ i, Polynomial.aeval y' (cv i) * s i = ∑ i, Polynomial.aeval y' (cu i) * s i := by
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := BL) z
    have hb0 : algebraMap BL F' b ≠ 0 :=
      fun h => nonZeroDivisors.ne_zero hb (hinjF' (by rw [h, map_zero]))
    refine ⟨fun i => bL.repr a i, fun i => bL.repr b i, ?_, ?_⟩
    · rw [← hsumF', bL.sum_repr]; exact hb0
    · rw [← hsumF', ← hsumF', bL.sum_repr, bL.sum_repr]
      exact div_mul_cancel₀ _ hb0
  obtain ⟨hfdF', hdegF'⟩ :=
    AlgebraicCurve.finrank_adjoin_eq_card_of_mul_mem_span_of_fractions y' s
      (fun i j => ⟨cL i j, hmulF' i j⟩) hindF' hfracF'
  haveI := hfdF'
  have hgenF' : genusFF L F' + n ≤ ∑ i, d i :=
    AlgebraicCurve.genusFF_le_of_normalForm n y' hy'tr hfdF' hdegF' s d hs0 hd0 hd cL hmulF' hdegL hindF'

  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin L ({y'} : Set F')) F' :=
    Algebra.IsAlgebraic.of_finite _ F'
  obtain ⟨W, algInst, Rg, hRgW, hyW, htrW⟩ :=
    AlgebraicCurve.exists_regularProlongation_of_transcendental V y' hy'tr
  letI := algInst

  letI : NonAssocSemiring BA := NonAssocRing.toNonAssocSemiring
  let jΛ : BA →+* F' := (algebraMap BL F').comp ι.toRingHom
  have hjΛ : ∀ u, jΛ u = algebraMap BL F' (ι u) := fun _ => rfl
  have hjΛinj : Function.Injective jΛ := hinjF'.comp hιinj
  let Λ : Subring F' := jΛ.range
  let eΛ : BA ≃+* Λ := RingEquiv.ofBijective jΛ.rangeRestrict
    ⟨fun a b h => hjΛinj (congrArg Subtype.val h), jΛ.rangeRestrict_surjective⟩
  have heΛ : ∀ u, ((eΛ u : Λ) : F') = jΛ u := fun _ => rfl
  have heΛsymm : ∀ f : Λ, jΛ (eΛ.symm f) = f := fun f => by
    rw [← heΛ, RingEquiv.apply_symm_apply]

  let evV : V[X] →+* F' := Polynomial.eval₂RingHom ((algebraMap L F').comp (algebraMap V L)) y'
  have hevV : ∀ q : V[X], evV q = Polynomial.aeval y' (q.map V.subtype) := by
    intro q
    show Polynomial.eval₂ ((algebraMap L F').comp (algebraMap V L)) y' q = _
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have halgVBA : ∀ q : V[X], algebraMap V[X] BA q = q ⊗ₜ (1 : Bt) := fun q => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have halgLBL : ∀ q : L[X], algebraMap L[X] BL q = q ⊗ₜ (1 : Bt) := fun q => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hjΛalg : ∀ q : V[X], jΛ (algebraMap V[X] BA q) = evV q := by
    intro q
    rw [hjΛ, halgVBA, hevV, ← hevL', halgLBL]
    show algebraMap BL F' (ι (q ⊗ₜ 1)) = _
    rw [hιtmul]
  have hjΛsum : ∀ c : Fin (n + 1) → V[X], jΛ (∑ i, c i • bA i) = ∑ i, evV (c i) * s i := by
    intro c
    rw [hjΛ]
    show algebraMap BL F' (ι (∑ i, c i • bA i)) = _
    rw [hιsum, hsumF']
    exact Finset.sum_congr rfl fun i _ => by rw [hevV]
  have hρalg : ∀ q : V[X], ρ (algebraMap V[X] BA q) = fA₀ q := fun q => by
    rw [halgVBA, hρtmul, map_one, mul_one]

  haveI : Module.Finite V[X] BA := Module.Finite.of_basis bA
  haveI hBAint : Algebra.IsIntegral V[X] BA := Algebra.IsIntegral.of_finite V[X] BA
  have hint : ∀ f : Λ, ∃ P : (V[X])[X], P.Monic ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F').comp (algebraMap V L)) y')
        (f : F') P = 0 := by
    intro f
    set u := eΛ.symm f with hu
    obtain ⟨P, hPm, hP⟩ := hBAint.isIntegral u
    refine ⟨P, hPm, ?_⟩
    have h1 : (f : F') = jΛ u := (heΛsymm f).symm
    have h2 : (Polynomial.eval₂RingHom ((algebraMap L F').comp (algebraMap V L)) y' : V[X] →+* F') =
        jΛ.comp (algebraMap V[X] BA) := by
      apply RingHom.ext
      intro q
      exact (hjΛalg q).symm
    rw [h1, h2, ← Polynomial.hom_eval₂, hP, map_zero]

  let cVW : V →+* Rg.integers :=
    { toFun := fun a => ⟨algebraMap L F' a, (Rg.algebraMap_mem_iff a).mpr a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let hAW : V[X] →+* Rg.integers := Polynomial.eval₂RingHom cVW ⟨y', hyW⟩
  have hAWcoe : (Rg.integers.subtype).comp hAW = evV := by
    apply Polynomial.ringHom_ext
    · intro a
      show ((Polynomial.eval₂ cVW ⟨y', hyW⟩ (C a) : Rg.integers) : F') = evV (C a)
      simp only [Polynomial.eval₂_C]
      show algebraMap L F' a = Polynomial.eval₂ _ y' (C a)
      rw [Polynomial.eval₂_C]
      rfl
    · show ((Polynomial.eval₂ cVW ⟨y', hyW⟩ X : Rg.integers) : F') = evV X
      simp only [Polynomial.eval₂_X]
      show y' = Polynomial.eval₂ _ y' X
      rw [Polynomial.eval₂_X]
  have hAWcoe' : ∀ q, ((hAW q : Rg.integers) : F') = evV q := fun q =>
    congrArg (fun φ : V[X] →+* F' => φ q) hAWcoe
  have hΛW : ∀ f : F', f ∈ Λ → f ∈ Rg.integers := by
    intro f hf
    obtain ⟨P, hPm, hP⟩ := hint ⟨f, hf⟩
    have hint' : IsIntegral Rg.integers f := by
      refine ⟨P.map hAW, hPm.map hAW, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap Rg.integers F').comp hAW = evV := hAWcoe
      rw [this]
      exact hP
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Rg.integers) (K := F')).mp hint'
    rw [← hz]
    exact z.2
  have hsW : ∀ i, s i ∈ Rg.integers := fun i => hΛW _ ⟨bA i, by rw [hjΛ, hιbA]⟩

  let ρΛ : Λ →+* F := ρ.toRingHom.comp eΛ.symm.toRingHom
  have hρΛ : ∀ u : BA, ρΛ (eΛ u) = ρ u := fun u => by
    show ρ (eΛ.symm (eΛ u)) = ρ u
    rw [RingEquiv.symm_apply_apply]
  have hyΛ' : (y' : F') = jΛ (algebraMap V[X] BA X) := by rw [hjΛalg, hevV, Polynomial.map_X, Polynomial.aeval_X]
  have hyΛ : y' ∈ Λ := ⟨_, hyΛ'.symm⟩
  have hVΛ' : ∀ a : V, algebraMap L F' a = jΛ (algebraMap V[X] BA (C a)) := fun a => by
    rw [hjΛalg, hevV, Polynomial.map_C, Polynomial.aeval_C]; rfl
  have hVΛ : ∀ a : V, algebraMap L F' a ∈ Λ := fun a => ⟨_, (hVΛ' a).symm⟩
  have heΛX : eΛ (algebraMap V[X] BA X) = ⟨y', hyΛ⟩ := Subtype.ext hyΛ'.symm
  have heΛC : ∀ a : V, eΛ (algebraMap V[X] BA (C a)) = ⟨algebraMap L F' a, hVΛ a⟩ := fun a =>
    Subtype.ext (hVΛ' a).symm
  have hρV : ∀ a : V, ρΛ ⟨algebraMap L F' a, hVΛ a⟩ = algebraMap k F (IsLocalRing.residue V a) := by
    intro a
    rw [← heΛC, hρΛ, hρalg]
    show Polynomial.eval₂ cVF xb (C a) = _
    rw [Polynomial.eval₂_C]
    rfl
  have hρΛy : ρΛ ⟨y', hyΛ⟩ = xb := by
    rw [← heΛX, hρΛ, hρalg]
    show Polynomial.eval₂ cVF xb X = xb
    rw [Polynomial.eval₂_X]

  have hψbt0 : ψ (bt 0) = 1 := by rw [hbt0, map_one]
  have hxbtrK : Transcendental K xb := by
    rw [transcendental_iff]
    intro q hq
    have h := hψind (Pi.single 0 q) (by
      rw [Fin.sum_univ_succ, hψbt0]
      simp [hq])
    simpa using congrFun h 0
  have haevalk : ∀ r : k[X], Polynomial.aeval xb r = Polynomial.aeval xb (r.map e.toRingHom) := by
    intro r
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, ← halgkF]
  have haevalK : ∀ r : K[X], Polynomial.aeval xb r = Polynomial.aeval xb (r.map e.symm.toRingHom) := by
    intro r
    rw [haevalk, Polynomial.map_map]
    have : e.toRingHom.comp e.symm.toRingHom = RingHom.id K := by ext x; simp
    rw [this, Polynomial.map_id]
  have hxbtrk : Transcendental k xb := by
    rw [transcendental_iff]
    intro q hq
    rw [haevalk] at hq
    have := transcendental_iff.mp hxbtrK _ hq
    exact Polynomial.map_injective e.toRingHom e.injective (by rw [this, Polynomial.map_zero])

  have hker : ∀ f : Λ, ρΛ f = 0 → Rg.residue ⟨f, hΛW f f.2⟩ = 0 := by
    intro f hf
    set u := eΛ.symm f with hu
    have hρu : ρ u = 0 := by rw [← hρΛ, hu, RingEquiv.apply_symm_apply]; exact hf
    have hcoef := hkerρ u hρu
    set c : Fin (n + 1) → V[X] := fun i => bA.repr u i with hc
    have huc : u = ∑ i, c i • bA i := (bA.sum_repr u).symm
    have hfsum : (f : F') = ∑ i, evV (c i) * s i := by
      rw [← heΛsymm f, ← hu, huc, hjΛsum]

    have hfO : (⟨f, hΛW f f.2⟩ : Rg.integers) = ∑ i, hAW (c i) * ⟨s i, hsW i⟩ := by
      apply Subtype.ext
      show (f : F') = Rg.integers.subtype (∑ i, hAW (c i) * ⟨s i, hsW i⟩)
      rw [hfsum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, ← hAWcoe']; rfl
    have hrescVW : Rg.residue.comp cVW = (algebraMap k _).comp (IsLocalRing.residue V) := by
      ext a
      exact Rg.residue_algebraMap a
    have hresAW : ∀ q : V[X], (∀ n, q.coeff n ∈ IsLocalRing.maximalIdeal V) → Rg.residue (hAW q) = 0 := by
      intro q hq
      have hq0 : q.map (IsLocalRing.residue V) = 0 := by
        ext n
        rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
        exact hq n
      show Rg.residue (Polynomial.eval₂ cVW ⟨y', hyW⟩ q) = 0
      rw [Polynomial.hom_eval₂, hrescVW, ← Polynomial.eval₂_map, hq0, Polynomial.eval₂_zero]
    rw [hfO, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, hresAW (c i) (hcoef i), zero_mul]

  have hfrac : ∀ z : F, ∃ f h : Λ, ρΛ h ≠ 0 ∧ z * ρΛ h = ρΛ f := by
    intro z
    obtain ⟨f₀, h₀, hh₀, hz⟩ := hψfrac z
    have hρ1 : ∀ b : Bt, ρΛ (eΛ ((1 : V[X]) ⊗ₜ b)) = ψ b := fun b => by
      rw [hρΛ, hρtmul, map_one, one_mul]
    refine ⟨eΛ ((1 : V[X]) ⊗ₜ f₀), eΛ ((1 : V[X]) ⊗ₜ h₀), ?_, ?_⟩
    · rw [hρ1]; exact hh₀
    · rw [hρ1, hρ1]; exact hz

  have hψsum : ∀ f₀ : Bt, ψ f₀ = ∑ i, Polynomial.aeval xb
      (((bt.repr f₀ i).map (WittVector.constantCoeff : R₀ →+* K)).map e.symm.toRingHom) * ψ (bt i) := by
    intro f₀
    conv_lhs => rw [← bt.sum_repr f₀]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, map_mul, hψalg, haevalK]
  have hmulK : ∀ i j, ∃ c : Fin (n + 1) → k[X], ψ (bt i) * ψ (bt j) = ∑ l, Polynomial.aeval xb (c l) * ψ (bt l) :=
    fun i j => ⟨_, by rw [← map_mul]; exact hψsum (bt i * bt j)⟩
  have hindK : ∀ d : Fin (n + 1) → k[X], ∑ i, Polynomial.aeval xb (d i) * ψ (bt i) = 0 → d = 0 := by
    intro d hd
    have hd' : ∑ i, Polynomial.aeval xb ((d i).map e.toRingHom) * ψ (bt i) = 0 := by
      rw [← hd]
      exact Finset.sum_congr rfl fun i _ => by rw [← haevalk]
    have := hψind _ hd'
    funext i
    have hi := congrFun this i
    simp only [Pi.zero_apply] at hi
    exact Polynomial.map_injective e.toRingHom e.injective (by rw [hi, Pi.zero_apply, Polynomial.map_zero])
  have hfracK : ∀ z : F, ∃ cu cv : Fin (n + 1) → k[X],
      ∑ i, Polynomial.aeval xb (cv i) * ψ (bt i) ≠ 0 ∧
        z * ∑ i, Polynomial.aeval xb (cv i) * ψ (bt i) = ∑ i, Polynomial.aeval xb (cu i) * ψ (bt i) := by
    intro z
    obtain ⟨f₀, h₀, hh₀, hz⟩ := hψfrac z
    refine ⟨fun i => ((bt.repr f₀ i).map (WittVector.constantCoeff : R₀ →+* K)).map e.symm.toRingHom,
      fun i => ((bt.repr h₀ i).map (WittVector.constantCoeff : R₀ →+* K)).map e.symm.toRingHom, ?_, ?_⟩
    · rw [← hψsum h₀]; exact hh₀
    · rw [← hψsum h₀, ← hψsum f₀]; exact hz
  obtain ⟨hfdK, hdegK⟩ :=
    AlgebraicCurve.finrank_adjoin_eq_card_of_mul_mem_span_of_fractions (k := k) xb
      (fun i => ψ (bt i)) hmulK hindK hfracK
  haveI := hfdK
  haveI hfdK' : FiniteDimensional (IntermediateField.adjoin k ({ρΛ ⟨y', hyΛ⟩} : Set F)) F := by
    rw [hρΛy]; exact hfdK
  have hdegLr : Module.finrank (IntermediateField.adjoin L ({y'} : Set F')) F' ≤
      Module.finrank (IntermediateField.adjoin k ({ρΛ ⟨y', hyΛ⟩} : Set F)) F := by
    rw [hdegF', hρΛy, hdegK]

  obtain ⟨θ, hθ⟩ :=
    AlgebraicCurve.RegularProlongation.exists_algEquiv_apply_eq_residue_of_transcendental V Rg y' hyW
      htrW Λ hΛW hyΛ hVΛ hint ρΛ hρV hker hfrac hdegLr

  let resF : Rg.integers →+* F := (θ.symm : _ →ₐ[k] F).toRingHom.comp Rg.residue
  have hresF : ∀ z, resF z = θ.symm (Rg.residue z) := fun _ => rfl
  let RF : RegularProlongation V F' F :=
    { integers := Rg.integers
      residue := resF
      algebraMap_mem_iff := Rg.algebraMap_mem_iff
      residue_surjective := θ.symm.surjective.comp Rg.residue_surjective
      ker_residue := by
        rw [← Rg.ker_residue]
        ext z
        simp only [RingHom.mem_ker, hresF, map_eq_zero_iff _ θ.symm.injective]
      residue_algebraMap := fun a => by
        rw [hresF, Rg.residue_algebraMap, AlgEquiv.commutes]
      exists_smul_mem := fun f hf => by
        obtain ⟨c, hc, hres⟩ := Rg.exists_smul_mem f hf
        exact ⟨c, hc, by rw [hresF]; exact (map_ne_zero_iff _ θ.symm.injective).mpr hres⟩ }
  have hRFres : ∀ z, RF.residue z = θ.symm (Rg.residue z) := fun _ => rfl
  have hresy : RF.residue ⟨y', hyW⟩ = xb := by
    rw [hRFres, ← hρΛy, ← hθ ⟨y', hyΛ⟩, AlgEquiv.symm_apply_apply]

  have hgk : genusFF k F = genusFF K F :=
    (genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp k K F e halgkF).1

  have hDeu := RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one V
    (fun _ : Fin 1 => F) (fun _ => RF) (Function.injective_of_subsingleton _) y' (fun _ => hyW) hy'tr hfdF'
    (fun _ => by rw [hresy]; exact hxbtrk)
    (by rw [Fin.sum_univ_one, hresy, hdegK, hdegF'])
  rw [Fin.sum_univ_one] at hDeu
  have hgood : genusFF k F = genusFF L F' := by
    refine le_antisymm hDeu ?_
    rw [hgk]
    omega

  haveI : IsCurveOver L F' := isCurveOver_of_isAlgClosed_of_transcendental y' hy'tr
  haveI : IsAlgClosed k := IsAlgClosed.of_ringEquiv K k e.symm
  haveI : IsCurveOver k F := isCurveOver_of_isAlgClosed_of_transcendental xb hxbtrk
  obtain ⟨r, hr⟩ := exists_placeMap_mapDomain_eq_ord_of_good_constantReduction V (F := F') (Fbar := F)
    Rg.integers RF.residue RF.algebraMap_mem_iff RF.residue_surjective RF.ker_residue RF.residue_algebraMap
    RF.exists_smul_mem
    ⟨⟨y', hyW⟩, by rw [hresy]; exact hxbtrk, by rw [hresy, hdegK]; exact Nat.succ_pos n,
      by rw [hresy, hdegK, hdegF']⟩ hgood
  let Rcr : ConstantReduction V F' F :=
    { integers := Rg.integers
      residue := RF.residue
      placeMap := r
      algebraMap_mem_iff := RF.algebraMap_mem_iff
      residue_surjective := RF.residue_surjective
      ker_residue := RF.ker_residue
      residue_algebraMap := RF.residue_algebraMap
      exists_smul_mem := RF.exists_smul_mem
      deg_placeMap := fun P => by
        rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed]
      mapDomain_placeMap := hr }
  exact ⟨L, inferInstance, inferInstance, inferInstance, V, e, F', inferInstance, algLF', algkF, halgkF,
    ⟨y', hy'tr, hfdF'⟩, Rcr, hgood⟩

end
end S_AlgebraicCurve_exists_constantReduction_isGood_of_wittVector_normalFormOrder
end P2MW
export P2MW.S_AlgebraicCurve_exists_constantReduction_isGood_of_wittVector_normalFormOrder (solution)
