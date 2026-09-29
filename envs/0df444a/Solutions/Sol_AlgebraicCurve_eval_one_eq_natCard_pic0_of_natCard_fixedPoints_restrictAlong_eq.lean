-- Prove2me | solution 1 for AlgebraicCurve.eval_one_eq_natCard_pic0_of_natCard_fixedPoints_restrictAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2c1cdc2e-4dc3-53e4-94c8-3f76ee208298

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_AlgebraicCurve_exists_LPolynomial_of_finite
import Theorems.Thm_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
import Theorems.Thm_AlgebraicCurve_LPolynomial_eval_one_eq_natCard_pic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_eval_one_eq_natCard_pic0_of_natCard_fixedPoints_restrictAlong_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

noncomputable section

namespace P2mFixCNF

section Series

open PowerSeries

def E (f : ℂ⟦X⟧) : ℂ⟦X⟧ := X * (d⁄dX ℂ) f

theorem coeff_E (f : ℂ⟦X⟧) (n : ℕ) : coeff n (E f) = (n : ℂ) * coeff n f := by
  cases n with
  | zero => simp [E, coeff_zero_X_mul]
  | succ m =>
    rw [E, coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem E_mul (f g : ℂ⟦X⟧) : E (f * g) = E f * g + f * E g := by
  simp only [E, Derivation.leibniz, smul_eq_mul]
  ring

theorem E_prod {ι : Type*} (s : Finset ι) (f M : ι → ℂ⟦X⟧)
    (h : ∀ i ∈ s, E (f i) = f i * M i) :
    E (∏ i ∈ s, f i) = (∏ i ∈ s, f i) * ∑ i ∈ s, M i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext n
    simp [coeff_E]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, E_mul,
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), h a (Finset.mem_insert_self a s)]
    ring

def geomTail (a : ℂ) : ℂ⟦X⟧ := PowerSeries.mk fun r => if r = 0 then 0 else a ^ r

theorem coeff_geomTail (a : ℂ) (r : ℕ) :
    coeff r (geomTail a) = if r = 0 then 0 else a ^ r := by
  rw [geomTail, coeff_mk]

theorem E_linear (a : ℂ) : E (1 - C a * X) = (1 - C a * X) * (-geomTail a) := by
  ext n
  rw [coeff_E, mul_neg, map_neg, map_sub, coeff_one, coeff_C_mul, coeff_X, sub_mul, one_mul,
    map_sub, mul_assoc, coeff_C_mul, coeff_geomTail]
  rcases n with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_geomTail]
    rcases m with _ | m
    · simp
    · have e1 : (m + 1 + 1 = 0) = False := eq_false (by omega)
      have e2 : (m + 1 + 1 = 1) = False := eq_false (by omega)
      have e3 : (m + 1 = 0) = False := eq_false (by omega)
      simp only [e1, e2, e3, if_false]
      ring

theorem coeff_mul_range (f M : ℂ⟦X⟧) (n : ℕ) :
    coeff n (f * M) = ∑ r ∈ Finset.range (n + 1), coeff r f * coeff (n - r) M := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem eq_of_E_eq (f g M : ℂ⟦X⟧) (hf : E f = f * M) (hg : E g = g * M)
    (h0 : coeff 0 f = coeff 0 g) (hf0 : coeff 0 f ≠ 0) : f = g := by

  have hM0 : coeff 0 M = 0 := by
    have := congrArg (coeff 0) hf
    rw [coeff_E, Nat.cast_zero, zero_mul, coeff_mul_range, Finset.sum_range_one,
      Nat.sub_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hf0

  have hrec : ∀ (u : ℂ⟦X⟧), E u = u * M → ∀ n : ℕ,
      (n : ℂ) * coeff n u = ∑ r ∈ Finset.range n, coeff r u * coeff (n - r) M := by
    intro u hu n
    have := congrArg (coeff n) hu
    rw [coeff_E, coeff_mul_range, Finset.sum_range_succ, Nat.sub_self, hM0, mul_zero,
      add_zero] at this
    exact this
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h0
    · have h1 := hrec f hf n
      have h2 := hrec g hg n
      have h3 : ∑ r ∈ Finset.range n, coeff r f * coeff (n - r) M =
          ∑ r ∈ Finset.range n, coeff r g * coeff (n - r) M :=
        Finset.sum_congr rfl fun r hr => by rw [ih r (Finset.mem_range.mp hr)]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      apply mul_left_cancel₀ hn0
      rw [h1, h3, ← h2]

theorem series_converse {m : ℕ} (q : ℂ) (α : Fin m → ℂ) (A N : ℕ → ℂ) (hA0 : A 0 = 1)
    (hN0 : N 0 = 0)
    (hB : ∀ n : ℕ, (n : ℂ) * A n = ∑ r ∈ Finset.range (n + 1), N r * A (n - r))
    (hN : ∀ r : ℕ, 1 ≤ r → N r = q ^ r + 1 - ∑ i, α i ^ r) :
    (1 - X) * (1 - C q * X) * PowerSeries.mk A = ∏ i, (1 - C (α i) * X) := by
  classical
  set Z : ℂ⟦X⟧ := PowerSeries.mk A with hZdef
  set Nc : ℂ⟦X⟧ := PowerSeries.mk N with hNdef
  set U : ℂ⟦X⟧ := (1 - X) * (1 - C q * X) with hUdef
  set P : ℂ⟦X⟧ := ∏ i, (1 - C (α i) * X) with hPdef

  have hEZ : E Z = Z * Nc := by
    ext n
    rw [coeff_E, mul_comm Z, coeff_mul_range]
    simp only [hZdef, hNdef, coeff_mk]
    exact hB n

  have hEU : E U = U * (-geomTail 1 + -geomTail q) := by
    have h1 : E (1 - X) = (1 - X) * (-geomTail 1) := by
      simpa using E_linear 1
    rw [hUdef, E_mul, h1, E_linear q]
    ring

  have hEP : E P = P * ∑ i, (-geomTail (α i)) :=
    E_prod Finset.univ (fun i => 1 - C (α i) * X) (fun i => -geomTail (α i))
      (fun i _ => E_linear (α i))

  have hNc : Nc = geomTail 1 + geomTail q - ∑ i, geomTail (α i) := by
    ext r
    rw [hNdef, coeff_mk, map_sub, map_add, map_sum, coeff_geomTail, coeff_geomTail]
    simp only [coeff_geomTail, one_pow]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [hN0]
    · have hr0 : r ≠ 0 := hr.ne'
      simp only [hr0, if_false]
      rw [hN r hr]
      ring

  have hEUZ : E (U * Z) = (U * Z) * ∑ i, (-geomTail (α i)) := by
    rw [E_mul, hEU, hEZ, hNc, Finset.sum_neg_distrib]
    ring

  have hUZ0 : coeff 0 (U * Z) = 1 := by
    rw [hUdef, hZdef, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [hA0]
  have hP0 : coeff 0 P = 1 := by
    rw [hPdef, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
    simp
  exact eq_of_E_eq (U * Z) P _ hEUZ hEP (by rw [hUZ0, hP0]) (by rw [hUZ0]; exact one_ne_zero)

end Series

section Poly

open Polynomial

theorem exists_fin_map_eq {S : Type*} {n : ℕ} (s : Multiset S) (hn : Multiset.card s = n) :
    ∃ ρ : Fin n → S, Finset.univ.val.map ρ = s := by
  have hl : (s.toList : Multiset S) = s := s.coe_toList
  have hlen : s.toList.length = n := by rw [Multiset.length_toList, hn]
  subst hlen
  exact ⟨s.toList.get, by rw [Fin.univ_val_map, List.ofFn_get, hl]⟩

theorem eval_one_eq_eval_one (q : ℕ) (A N : ℕ → ℕ) (hN0 : N 0 = 0) (L : ℤ[X])
    (hL0 : L.coeff 0 = 1)
    (hLZ : (1 - PowerSeries.X) * (1 - PowerSeries.C (q : ℤ) * PowerSeries.X) *
        PowerSeries.mk (fun n : ℕ => (A n : ℤ)) = (L : PowerSeries ℤ))
    (hB : ∀ n, n * A n = ∑ r ∈ Finset.Icc 1 n, N r * A (n - r))
    (P : ℤ[X]) (hP : P.Monic)
    (hfix : ∀ r : ℕ, 1 ≤ r → ((N r : ℕ) : ℂ) = (q : ℂ) ^ r + 1 -
        (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ r)).sum)) :
    P.eval 1 = L.eval 1 := by
  classical

  set Pc : ℂ[X] := P.map (Int.castRingHom ℂ) with hPcdef
  have hPcm : Pc.Monic := hP.map _
  set m : ℕ := Pc.natDegree with hm
  have hcard : Multiset.card Pc.roots = m := IsAlgClosed.card_roots_eq_natDegree
  obtain ⟨ρ, hρ⟩ := exists_fin_map_eq Pc.roots hcard
  have hPcprod : Pc = ∏ i, (X - C (ρ i)) := by
    have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPcm hcard
    rw [← hρ, Multiset.map_map, Function.comp_def, Finset.prod_map_val] at h
    exact h.symm

  have hA0 : ((A 0 : ℕ) : ℂ) = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hLZ
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_mul] at h
    simp only [map_sub, map_one, PowerSeries.constantCoeff_X, sub_zero, map_mul,
      PowerSeries.constantCoeff_C, mul_zero, one_mul, PowerSeries.constantCoeff_mk,
      Polynomial.constantCoeff_coe, hL0] at h
    have h' : (A 0 : ℤ) = 1 := h
    exact_mod_cast h'

  have hBc : ∀ n : ℕ, (n : ℂ) * ((A n : ℕ) : ℂ)
      = ∑ r ∈ Finset.range (n + 1), ((N r : ℕ) : ℂ) * ((A (n - r) : ℕ) : ℂ) := by
    intro n
    have h := congrArg (Nat.cast : ℕ → ℂ) (hB n)
    push_cast at h
    rw [h, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < n + 1 by omega), hN0]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [Finset.Ico_add_one_right_eq_Icc]

  have hNr : ∀ r : ℕ, 1 ≤ r → ((N r : ℕ) : ℂ) = (q : ℂ) ^ r + 1 - ∑ i, ρ i ^ r := by
    intro r hr
    have hsum : ((Pc.roots.map fun z => z ^ r).sum) = ∑ i, ρ i ^ r := by
      rw [← hρ, Multiset.map_map, Function.comp_def, Finset.sum_map_val]
    rw [hfix r hr, hsum]

  have hconv := series_converse (q : ℂ) ρ (fun n => ((A n : ℕ) : ℂ)) (fun r => ((N r : ℕ) : ℂ))
    hA0 (by simp [hN0]) hBc hNr

  set Lc : ℂ[X] := L.map (Int.castRingHom ℂ) with hLcdef
  have hmk : PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.mk fun n : ℕ => (A n : ℤ))
      = PowerSeries.mk fun n : ℕ => ((A n : ℕ) : ℂ) := by
    ext n
    simp [PowerSeries.coeff_map]
  have hZc : (1 - PowerSeries.X) * (1 - PowerSeries.C (q : ℂ) * PowerSeries.X) *
      PowerSeries.mk (fun n : ℕ => ((A n : ℕ) : ℂ)) = (Lc : PowerSeries ℂ) := by
    have h := congrArg (PowerSeries.map (Int.castRingHom ℂ)) hLZ
    rw [← Polynomial.polynomial_map_coe, ← hLcdef, map_mul, map_mul, map_sub,
      map_sub, map_one, map_mul, PowerSeries.map_C, PowerSeries.map_X, hmk, eq_intCast,
      Int.cast_natCast] at h
    exact h
  have hcoe : ((∏ i, (1 - C (ρ i) * X) : ℂ[X]) : PowerSeries ℂ)
      = ∏ i, (1 - PowerSeries.C (ρ i) * PowerSeries.X) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
  have hLc : Lc = ∏ i, (1 - C (ρ i) * X) := by
    apply Polynomial.coe_inj.mp
    rw [hcoe, ← hZc, hconv]

  have hL1 : Lc.eval 1 = ∏ i, (1 - ρ i) := by
    rw [hLc, eval_prod]
    simp
  have hP1 : Pc.eval 1 = ∏ i, (1 - ρ i) := by
    rw [hPcprod, eval_prod]
    simp
  have h1 : ((P.eval 1 : ℤ) : ℂ) = ((L.eval 1 : ℤ) : ℂ) := by
    have e1 : Pc.eval 1 = ((P.eval 1 : ℤ) : ℂ) := by
      rw [hPcdef, eval_map, eval₂_at_one, eq_intCast]
    have e2 : Lc.eval 1 = ((L.eval 1 : ℤ) : ℂ) := by
      rw [hLcdef, eval_map, eval₂_at_one, eq_intCast]
    rw [← e1, ← e2, hP1, hL1]
  exact_mod_cast h1

end Poly

end P2mFixCNF

end

open AlgebraicCurve in

theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hC : AlgebraicCurve.ConstantsAreBase k F₀)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (P : Polynomial ℤ) (hP : P.Monic)
    (hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (Nat.card k : ℂ) ^ n + 1 -
          (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) :
    (P.eval 1 : ℤ) = Nat.card (AlgebraicCurve.Pic0 k F₀) := by
  classical

  have hcount := fun r (hr : 0 < r) =>
    (AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
      k K F₀ F hfg hgen φ hφi hφ r hr).2

  haveI hEss₀ : Algebra.EssFiniteType k F₀ := by
    obtain ⟨s, hs⟩ := hfg
    exact IntermediateField.fg_top_iff.mp ⟨s, hs⟩

  obtain ⟨L, -, hL0, -, hLZ⟩ := AlgebraicCurve.exists_LPolynomial_of_finite k F₀ hC
  have hEuler := fun n => AlgebraicCurve.card_effectiveDivisors_mul_eq_sum k F₀ n

  have hL1 := AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0 k F₀ hC L hLZ

  rw [← hL1]
  refine P2mFixCNF.eval_one_eq_eval_one (Nat.card k)
    (fun n => Nat.card {D : Divisor k F₀ // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)})
    (fun r => ∑ d ∈ Nat.divisors r, d * Nat.card {v : Place k F₀ | v.deg = d})
    (by simp) L hL0 hLZ hEuler P hP fun r hr => ?_
  show ((∑ d ∈ Nat.divisors r, d * Nat.card {v : Place k F₀ | v.deg = d} : ℕ) : ℂ) = _
  rw [← hcount r hr]
  exact hfix r hr

end S_AlgebraicCurve_eval_one_eq_natCard_pic0_of_natCard_fixedPoints_restrictAlong_eq
end P2MW
export P2MW.S_AlgebraicCurve_eval_one_eq_natCard_pic0_of_natCard_fixedPoints_restrictAlong_eq (solution)
