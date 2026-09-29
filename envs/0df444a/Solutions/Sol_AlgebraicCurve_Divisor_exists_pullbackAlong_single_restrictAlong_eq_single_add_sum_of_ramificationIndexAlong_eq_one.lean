-- Prove2me | solution 1 for AlgebraicCurve.Divisor.exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/eaa7130d-50bb-58f9-ad28-937bd11f90ef

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (n : ℕ) (hn : finrankAlong K φ = n + 1)
    (hinert : ∀ W : Place K F', W.inertiaDegAlong φ hφ = 1)
    (W₀ : Place K F') (he : W₀.ramificationIndexAlong φ = 1) :
    ∃ (k : ℕ) (W : Fin k → Place K F') (e : Fin k → ℕ),
      (∀ j, 0 < e j) ∧ ∑ j, e j = n ∧ Function.Injective W ∧
      (∀ j, W j ≠ W₀) ∧ (∀ j, (W j).restrictAlong φ hφ = W₀.restrictAlong φ hφ) ∧
      (∀ W' : Place K F', W'.restrictAlong φ hφ = W₀.restrictAlong φ hφ → W' = W₀ ∨ ∃ j, W' = W j) ∧
      (∀ j, (W j).ramificationIndexAlong φ = e j) ∧
      Divisor.pullbackAlong φ hφ (Finsupp.single (W₀.restrictAlong φ hφ) 1) =
        Finsupp.single W₀ 1 + ∑ j, (e j : ℤ) • Finsupp.single (W j) 1 := by
  classical
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  set w₀ := W₀.restrictAlong φ hφ with hw₀

  set S : Finset (Place K F') := (Place.fiberAlong φ hφ w₀).erase W₀ with hS
  have hW₀mem : W₀ ∈ Place.fiberAlong φ hφ w₀ := Place.mem_fiberAlong.mpr rfl

  let k := S.card
  let eq := S.equivFin
  let W : Fin k → Place K F' := fun j => (eq.symm j : Place K F')
  let e : Fin k → ℕ := fun j => (W j).ramificationIndexAlong φ
  have hWmem : ∀ j, W j ∈ S := fun j => (eq.symm j).2
  have hWinj : Function.Injective W := fun a b h => eq.symm.injective (Subtype.ext h)
  refine ⟨k, W, e, ?_, ?_, hWinj, ?_, ?_, ?_, fun j => rfl, ?_⟩
  · intro j
    show 0 < (W j).ramificationIndex F
    exact (W j).ramificationIndex_pos (F := F)
  ·
    have hFI := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep w₀
    simp_rw [hinert, Nat.cast_one, mul_one] at hFI
    rw [hn, ← Finset.add_sum_erase _ _ hW₀mem] at hFI
    have he' : ((W₀.ramificationIndexAlong φ : ℕ) : ℤ) = 1 := by rw [he]; rfl
    rw [he'] at hFI
    have hsumS : ∑ w ∈ S, (w.ramificationIndexAlong φ : ℤ) = n := by
      push_cast at hFI; linarith

    have hre : ∑ j, (e j : ℤ) = ∑ w ∈ S, (w.ramificationIndexAlong φ : ℤ) := by
      rw [← Finset.sum_coe_sort S]
      exact Fintype.sum_equiv eq.symm _ _ (fun j => rfl)
    have : ((∑ j, e j : ℕ) : ℤ) = n := by push_cast; rw [hre, hsumS]
    exact_mod_cast this
  · intro j
    exact Finset.ne_of_mem_erase (hWmem j)
  · intro j
    exact Place.mem_fiberAlong.mp (Finset.mem_of_mem_erase (hWmem j))
  ·
    intro W' hW'
    by_cases h : W' = W₀
    · exact Or.inl h
    · right
      have hmem : W' ∈ S := Finset.mem_erase.mpr ⟨h, Place.mem_fiberAlong.mpr hW'⟩
      exact ⟨eq ⟨W', hmem⟩, by show W' = ((eq.symm (eq ⟨W', hmem⟩)) : Place K F'); rw [Equiv.symm_apply_apply]⟩
  ·
    show Divisor.pullback F' (Finsupp.single w₀ 1) = _
    rw [Divisor.pullback_single]
    change ∑ w ∈ Place.fiberAlong φ hφ w₀, Finsupp.single w (1 * (w.ramificationIndexAlong φ : ℤ)) = _
    rw [← Finset.add_sum_erase _ _ hW₀mem]
    congr 1
    · rw [one_mul, show ((W₀.ramificationIndexAlong φ : ℕ) : ℤ) = 1 by rw [he]; rfl]
    · rw [← Finset.sum_coe_sort ((Place.fiberAlong φ hφ w₀).erase W₀)]
      refine (Fintype.sum_equiv eq.symm _ _ (fun j => ?_)).symm
      show (e j : ℤ) • Finsupp.single (W j) (1 : ℤ) = Finsupp.single _ _
      rw [Finsupp.smul_single, smul_eq_mul, mul_one, one_mul]

end S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one (solution)
