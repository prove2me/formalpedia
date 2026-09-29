-- Prove2me | solution 1 for AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e419213d-c42c-50dd-aebf-593be4ac6610

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open AlgebraicCurve

namespace X2Glue

theorem algebra_adjoin_eq_top_of_intermediateField {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] [FiniteDimensional F E]
    {S : Set E} (hS : IntermediateField.adjoin K S = ⊤) : Algebra.adjoin F S = ⊤ := by
  have hS' : IntermediateField.adjoin F S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin K S := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K S ≤ (IntermediateField.adjoin F S).restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr fun y hy => IntermediateField.subset_adjoin F S hy
    exact hle hx
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hS', IntermediateField.top_toSubalgebra]

end X2Glue

theorem solution
    {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z'] [CharZero K]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K Z] [HasPrincipalDivisors K Z']
    (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
    (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (s : F₁ →ₐ[K] Z') (s' : F₂ →ₐ[K] Z')
    (hsq : u.comp φ = u'.comp ψ') (hsq' : s.comp φ = s'.comp ψ')
    (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
    (hs : s.toRingHom.IsIntegral) (hs' : s'.toRingHom.IsIntegral)
    (hφfin : FiniteAlong K φ) (hψ'fin : FiniteAlong K ψ')
    (hufin : FiniteAlong K u) (hu'fin : FiniteAlong K u')
    (hsfin : FiniteAlong K s) (hs'fin : FiniteAlong K s')
    (hgen : IntermediateField.adjoin K (Set.range u ∪ Set.range u') = ⊤)
    (hgen' : IntermediateField.adjoin K (Set.range s ∪ Set.range s') = ⊤)
    (hdeg : finrankAlong K u' + finrankAlong K s' = finrankAlong K φ)
    (hne : ∃ (a : F₁) (b : F₂), s a = s' b ∧ u a ≠ u' b)
    (D : Divisor K F₂) :
    Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D)
      = Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D)
        + Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D) := by
  classical

  letI : Algebra F F₁ := algebraAlong φ
  letI : Algebra F F₂ := algebraAlong ψ'
  letI : Algebra F₁ Z := algebraAlong u
  letI : Algebra F₂ Z := algebraAlong u'
  letI : Algebra F₁ Z' := algebraAlong s
  letI : Algebra F₂ Z' := algebraAlong s'
  letI : Algebra F Z := algebraAlong (u.comp φ)
  letI : Algebra F Z' := algebraAlong (s.comp φ)
  haveI : IsScalarTower K F F₁ := isScalarTower_along φ
  haveI : IsScalarTower K F F₂ := isScalarTower_along ψ'
  haveI : IsScalarTower K F₁ Z := isScalarTower_along u
  haveI : IsScalarTower K F₂ Z := isScalarTower_along u'
  haveI : IsScalarTower K F₁ Z' := isScalarTower_along s
  haveI : IsScalarTower K F₂ Z' := isScalarTower_along s'
  haveI : IsScalarTower K F Z := isScalarTower_along (u.comp φ)
  haveI : IsScalarTower K F Z' := isScalarTower_along (s.comp φ)
  haveI : IsScalarTower F F₁ Z := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F F₂ Z := IsScalarTower.of_algebraMap_eq fun x => AlgHom.congr_fun hsq x
  haveI : IsScalarTower F F₁ Z' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F F₂ Z' := IsScalarTower.of_algebraMap_eq fun x => AlgHom.congr_fun hsq' x
  haveI : Algebra.IsIntegral F F₁ := isIntegral_along φ hφ
  haveI : Algebra.IsIntegral F F₂ := isIntegral_along ψ' hψ'
  haveI : Algebra.IsIntegral F₁ Z := isIntegral_along u hu
  haveI : Algebra.IsIntegral F₂ Z := isIntegral_along u' hu'
  haveI : Algebra.IsIntegral F₁ Z' := isIntegral_along s hs
  haveI : Algebra.IsIntegral F₂ Z' := isIntegral_along s' hs'
  haveI : FiniteDimensional F F₁ := hφfin
  haveI : FiniteDimensional F F₂ := hψ'fin
  haveI : FiniteDimensional F₁ Z := hufin
  haveI : FiniteDimensional F₂ Z := hu'fin
  haveI : FiniteDimensional F₁ Z' := hsfin
  haveI : FiniteDimensional F₂ Z' := hs'fin
  haveI : FiniteDimensional F Z := Module.Finite.trans F₁ Z
  haveI : FiniteDimensional F Z' := Module.Finite.trans F₁ Z'
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

  have hgenZ : Algebra.adjoin F (Set.range (algebraMap F₂ Z) ∪ Set.range (algebraMap F₁ Z)) = ⊤ := by
    rw [Set.union_comm]; exact X2Glue.algebra_adjoin_eq_top_of_intermediateField (K := K) hgen
  have hgenZ' : Algebra.adjoin F (Set.range (algebraMap F₂ Z') ∪ Set.range (algebraMap F₁ Z')) = ⊤ := by
    rw [Set.union_comm]; exact X2Glue.algebra_adjoin_eq_top_of_intermediateField (K := K) hgen'
  have hdeg' : Module.finrank F₂ Z + Module.finrank F₂ Z' = Module.finrank F F₁ := hdeg
  have hne' : ∃ (a : F₁) (b : F₂), algebraMap F₁ Z' a = algebraMap F₂ Z' b ∧
      algebraMap F₁ Z a ≠ algebraMap F₂ Z b := hne

  have eZ : ∀ W : Place K Z, Place.ramificationIndexAlong u' W = W.ramificationIndex F₂ := fun _ => rfl
  have fZ : ∀ W : Place K Z, W.inertiaDegAlong u hu = W.inertiaDeg F₁ := fun _ => rfl
  have eZ' : ∀ W : Place K Z', Place.ramificationIndexAlong s' W = W.ramificationIndex F₂ := fun _ => rfl
  have fZ' : ∀ W : Place K Z', W.inertiaDegAlong s hs = W.inertiaDeg F₁ := fun _ => rfl
  have fF : ∀ w : Place K F₂, w.inertiaDegAlong ψ' hψ' = w.inertiaDeg F := fun _ => rfl
  have eF : ∀ w : Place K F₁, Place.ramificationIndexAlong φ w = w.ramificationIndex F := fun _ => rfl

  have hrr : ∀ W : Place K Z, (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  have hrr' : ∀ W : Place K Z', (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

  suffices h : (Divisor.pullbackAlong φ hφ).comp (Divisor.pushforwardAlong ψ' hψ') =
      (Divisor.pushforwardAlong u hu).comp (Divisor.pullbackAlong u' hu')
        + (Divisor.pushforwardAlong s hs).comp (Divisor.pullbackAlong s' hs') from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun wA n => ?_
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.add_apply, Function.comp_apply]
  rw [Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single, Divisor.pullbackAlong_single,
    Divisor.pullbackAlong_single, map_sum, map_sum]
  simp only [Divisor.pushforwardAlong_single]

  ext wB
  rw [Finsupp.add_apply, Finset.sum_apply', Finset.sum_apply', Finset.sum_apply']
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', eZ, fZ, eZ', fZ', fF, eF]
  by_cases hv : wB.restrictAlong φ hφ = wA.restrictAlong ψ' hψ'
  · rw [if_pos (Place.mem_fiberAlong.mpr hv), ← Finset.sum_filter, ← Finset.sum_filter]
    have hT : ∀ W, W ∈ (Place.fiberAlong u' hu' wA).filter (fun W => W.restrictAlong u hu = wB)
        ↔ W.restrict F₂ = wA ∧ W.restrict F₁ = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have hT' : ∀ W, W ∈ (Place.fiberAlong s' hs' wA).filter (fun W => W.restrictAlong s hs = wB)
        ↔ W.restrict F₂ = wA ∧ W.restrict F₁ = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have key := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange_add
      (K := K) (F := F) (F₁ := F₂) (F₂ := F₁) (Z := Z) (Z' := Z')
      hgenZ hgenZ' hdeg' hne' wA wB (Eq.symm hv) _ hT _ hT'
    rw [Finset.sum_congr rfl fun W _ => mul_assoc n _ _,
      Finset.sum_congr rfl fun W _ => mul_assoc n _ _, ← Finset.mul_sum, ← Finset.mul_sum,
      ← mul_add, mul_assoc]
    congr 1
    exact_mod_cast key.symm
  ·
    rw [if_neg (fun h => hv (Place.mem_fiberAlong.mp h))]
    have h0 : ∑ W ∈ Place.fiberAlong u' hu' wA,
        (if Place.restrictAlong u hu W = wB then n * (W.ramificationIndex F₂ : ℤ) * (W.inertiaDeg F₁ : ℤ)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun W hW => ?_
      rw [if_neg]
      intro hWB
      apply hv
      have h₁ : W.restrict F₂ = wA := Place.mem_fiberAlong.mp hW
      have h₂ : W.restrict F₁ = wB := hWB
      show wB.restrict F = wA.restrict F
      rw [← h₁, ← h₂, hrr]
    have h0' : ∑ W ∈ Place.fiberAlong s' hs' wA,
        (if Place.restrictAlong s hs W = wB then n * (W.ramificationIndex F₂ : ℤ) * (W.inertiaDeg F₁ : ℤ)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun W hW => ?_
      rw [if_neg]
      intro hWB
      apply hv
      have h₁ : W.restrict F₂ = wA := Place.mem_fiberAlong.mp hW
      have h₂ : W.restrict F₁ = wB := hWB
      show wB.restrict F = wA.restrict F
      rw [← h₁, ← h₂, hrr']
    rw [h0, h0', add_zero]

end S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top (solution)
