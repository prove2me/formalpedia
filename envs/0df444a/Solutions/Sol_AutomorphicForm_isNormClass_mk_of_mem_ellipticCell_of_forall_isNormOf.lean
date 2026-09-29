-- Prove2me | solution 1 for AutomorphicForm.isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d185911e-ace6-54c6-bb9a-92acb433f54c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Theorems.Thm_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Theorems.Thm_NumberField_unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open Polynomial LT.TwistedNorm NumberField IsDedekindDomain
open scoped TensorProduct NumberField.LiesOver

noncomputable section

namespace R3NormCrit

section Companion

variable {R : Type*} [CommRing R] (t d : R)

private def _root_.R3NormCrit.comp : Matrix (Fin 2) (Fin 2) R := !![0, -d; 1, t]

p2m_export "R3NormCrit" "comp"

def quad : R[X] := X ^ 2 - C t * X + C d

@[scoped simp] theorem comp_apply_00 : comp t d 0 0 = 0 := rfl
@[scoped simp] theorem comp_apply_01 : comp t d 0 1 = -d := rfl
@[scoped simp] theorem comp_apply_10 : comp t d 1 0 = 1 := rfl
@[scoped simp] theorem comp_apply_11 : comp t d 1 1 = t := rfl

theorem quad_monic : (quad t d).Monic := by
  unfold quad
  nontriviality R
  monicity!

theorem quad_natDegree [Nontrivial R] : (quad t d).natDegree = 2 := by
  unfold quad; compute_degree!

theorem quad_degree [Nontrivial R] : (quad t d).degree = 2 := by
  unfold quad; compute_degree!

theorem quad_ne_zero [Nontrivial R] : quad t d ≠ 0 := (quad_monic t d).ne_zero

theorem quad_eval (x : R) : (quad t d).eval x = x ^ 2 - t * x + d := by
  simp [quad]

theorem quad_map {S : Type*} [CommRing S] (φ : R →+* S) :
    (quad t d).map φ = quad (φ t) (φ d) := by
  simp [quad, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

theorem det_comp : (comp t d).det = d := by
  simp [Matrix.det_fin_two, comp]

theorem comp_map {S : Type*} [CommRing S] (φ : R →+* S) :
    (comp t d).map φ = comp (φ t) (φ d) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [comp]

def lin (p q : R) : Matrix (Fin 2) (Fin 2) R := p • (1 : Matrix (Fin 2) (Fin 2) R) + q • comp t d

@[scoped simp] theorem lin_apply_00 (p q : R) : lin t d p q 0 0 = p := by simp [lin]
@[scoped simp] theorem lin_apply_10 (p q : R) : lin t d p q 1 0 = q := by simp [lin]
@[scoped simp] theorem lin_apply_01 (p q : R) : lin t d p q 0 1 = -(q * d) := by simp [lin]
@[scoped simp] theorem lin_apply_11 (p q : R) : lin t d p q 1 1 = p + q * t := by simp [lin]

theorem det_lin (p q : R) : (lin t d p q).det = p ^ 2 + p * q * t + q ^ 2 * d := by
  simp [Matrix.det_fin_two]; ring

theorem eq_lin_of_comm (Y : Matrix (Fin 2) (Fin 2) R) (h : comp t d * Y = Y * comp t d) :
    Y = lin t d (Y 0 0) (Y 1 0) := by
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, comp] at h00 h10
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination -h00
  · linear_combination -h10

def Φ : R[X] →ₐ[R] Matrix (Fin 2) (Fin 2) R := aeval (comp t d)

theorem Φ_X : Φ t d X = comp t d := aeval_X _

theorem Φ_C (p : R) : Φ t d (C p) = p • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [Φ, aeval_C, Algebra.algebraMap_eq_smul_one]

theorem Φ_lin (p q : R) : Φ t d (C p + C q * X) = lin t d p q := by
  rw [map_add, map_mul, Φ_C, Φ_C, Φ_X, lin, smul_mul_assoc, one_mul]

theorem Φ_quad : Φ t d (quad t d) = 0 := by
  rw [quad, map_add, map_sub, map_mul, map_pow, Φ_C, Φ_C, Φ_X]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, comp] <;> ring

theorem quad_dvd_of_Φ_eq_zero (g : R[X]) (h : Φ t d g = 0) : quad t d ∣ g := by
  nontriviality R
  set r := g %ₘ quad t d with hr
  have hdeg : r.degree ≤ 1 := by
    have := degree_modByMonic_lt g (quad_monic t d)
    rw [quad_degree] at this
    exact Order.le_of_lt_succ this
  have hr' : r = C (r.coeff 1) * X + C (r.coeff 0) := eq_X_add_C_of_degree_le_one hdeg
  have hΦr : Φ t d r = 0 := by
    have := modByMonic_add_div g (quad t d)
    rw [← hr] at this
    have h2 : Φ t d r = Φ t d g - Φ t d (quad t d * (g /ₘ quad t d)) := by
      rw [← map_sub]; congr 1; exact eq_sub_of_add_eq this
    rw [h2, h, map_mul, Φ_quad, zero_mul, sub_zero]
  have hlin : Φ t d r = lin t d (r.coeff 0) (r.coeff 1) := by
    conv_lhs => rw [hr']
    rw [← Φ_lin, add_comm]
  rw [hlin] at hΦr
  have h0 : r.coeff 0 = 0 := by simpa using congrFun (congrFun hΦr 0) 0
  have h1 : r.coeff 1 = 0 := by simpa using congrFun (congrFun hΦr 1) 0
  have hr0 : r = 0 := by rw [hr', h0, h1]; simp
  exact (modByMonic_eq_zero_iff_dvd (quad_monic t d)).mp hr0

theorem Φ_eq_of_quad_dvd_sub (g g' : R[X]) (h : quad t d ∣ g - g') : Φ t d g = Φ t d g' := by
  obtain ⟨k, hk⟩ := h
  have : Φ t d (g - g') = 0 := by rw [hk, map_mul, Φ_quad, zero_mul]
  rwa [map_sub, sub_eq_zero] at this

end Companion

section Sigma

variable {R : Type*} [CommRing R] (t d : R) (s : R →+* R) (ht : s t = t) (hd : s d = d)

theorem iterate_map_fixed {x : R} (hx : s x = x) (i : ℕ) : s^[i] x = x :=
  Function.iterate_fixed hx i

include ht hd in
theorem comp_map_iterate (i : ℕ) : (comp t d).map (s^[i]) = comp t d := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [comp, iterate_map_fixed s ht, iterate_map_fixed s hd, iterate_map_zero, iterate_map_one,
      iterate_map_neg]

include ht hd in
theorem lin_map_iterate (p q : R) (i : ℕ) :
    (lin t d p q).map (s^[i]) = lin t d (s^[i] p) (s^[i] q) := by
  have hc := comp_map_iterate t d s ht hd i
  ext a b
  have hcab := congrFun (congrFun hc a) b
  simp only [Matrix.map_apply] at hcab
  fin_cases a <;> fin_cases b <;>
    simp [iterate_map_mul, iterate_map_add, iterate_map_neg, iterate_map_fixed s ht,
      iterate_map_fixed s hd]

theorem coe_iterate_map (i : ℕ) (δ : GL (Fin 2) R) :
    (((Matrix.GeneralLinearGroup.map s)^[i] δ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = (δ : Matrix (Fin 2) (Fin 2) R).map (s^[i]) := by
  ext a b
  rw [LT.TwistedNorm.iterate_generalLinearGroup_map_apply]
  rfl

def twistPoly (n : ℕ) (p q : R) : R[X] :=
  ∏ i ∈ Finset.range n, (C (s^[i] p) + C (s^[i] q) * X)

theorem list_prod_range_eq {M : Type*} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).prod = ∏ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih,
      Finset.prod_range_succ, List.map_singleton, List.prod_singleton]

include ht hd in

theorem coe_sigmaNormPow_of_coe_eq_lin (n : ℕ) (p q : R) (δ : GL (Fin 2) R)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) R) = lin t d p q) :
    ((sigmaNormPow (Matrix.GeneralLinearGroup.map s) n δ : GL (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R) = Φ t d (twistPoly s n p q) := by
  rw [sigmaNormPow_def, sigmaPartialNorm_eq_prod_map_range, twistPoly, ← list_prod_range_eq,
    map_list_prod]
  rw [show ((((List.range n).map fun i => (Matrix.GeneralLinearGroup.map s)^[i] δ).prod :
      GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = (((List.range n).map fun i => (Matrix.GeneralLinearGroup.map s)^[i] δ).map
          (Units.coeHom (Matrix (Fin 2) (Fin 2) R))).prod from map_list_prod (Units.coeHom _) _]
  rw [List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Units.coeHom_apply]
  rw [coe_iterate_map, hδ, lin_map_iterate t d s ht hd, Φ_lin]

end Sigma

section Transfer

variable {R : Type*} [CommRing R] (t d : R) (s : R →+* R) (ht : s t = t) (hd : s d = d)
  (n : ℕ) (hs : ∀ x : R, s^[n] x = x)

include ht hd hs in

theorem exists_twistPoly_sub_X_dvd (Cu δ y : GL (Fin 2) R)
    (hCu : (Cu : Matrix (Fin 2) (Fin 2) R) = comp t d)
    (h : Cu = y⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map s) n δ * y) :
    ∃ p q : R, quad t d ∣ twistPoly s n p q - X := by
  set F := Matrix.GeneralLinearGroup.map (n := Fin 2) s with hF
  have hper : ∀ g : GL (Fin 2) R, F^[n] g = g := fun g =>
    LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self hs g

  set δ' := y⁻¹ * δ * F y with hδ'
  have hN : sigmaNormPow F n δ' = Cu := by
    rw [hδ', sigmaNormPow_sigmaConjElt F n (hper y) δ, ← h]

  have hsC : F Cu = Cu := by
    apply Units.ext
    change ((Cu : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map s = _
    rw [hCu]
    simpa using comp_map_iterate t d s ht hd 1
  have hcomm : δ' * Cu = Cu * δ' := by
    have h1 := map_sigmaNormPow F n (hper δ')
    rw [hN, hsC] at h1
    calc δ' * Cu = δ' * (δ'⁻¹ * Cu * δ') := by rw [← h1]
      _ = Cu * δ' := by group
  have hcomm' : comp t d * (δ' : Matrix (Fin 2) (Fin 2) R) = δ' * comp t d := by
    rw [← hCu, ← Units.val_mul, ← hcomm, Units.val_mul]
  set p := (δ' : Matrix (Fin 2) (Fin 2) R) 0 0
  set q := (δ' : Matrix (Fin 2) (Fin 2) R) 1 0
  have hlin : (δ' : Matrix (Fin 2) (Fin 2) R) = lin t d p q := eq_lin_of_comm t d _ hcomm'
  refine ⟨p, q, quad_dvd_of_Φ_eq_zero t d _ ?_⟩
  rw [map_sub, Φ_X, ← coe_sigmaNormPow_of_coe_eq_lin t d s ht hd n p q δ' hlin, hN, hCu, sub_self]

end Transfer

section Push

variable {R : Type*} [CommRing R] (t d : R) (s : R →+* R) (n : ℕ)

theorem iterate_comp_apply {B : Type*} [CommRing B] (ψ : R →+* B) (τ : B →+* B)
    (hτ : ∀ x, τ (ψ x) = ψ (s x)) (i : ℕ) (x : R) : τ^[i] (ψ x) = ψ (s^[i] x) := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hτ, ih]

theorem prod_iterate_eq_of_dvd {B : Type*} [CommRing B] (ψ : R →+* B) (τ : B →+* B)
    (hτ : ∀ x, τ (ψ x) = ψ (s x)) (β : B) (hβ : τ β = β)
    (hroot : β ^ 2 - ψ t * β + ψ d = 0) (p q : R)
    (hdvd : quad t d ∣ twistPoly s n p q - X) :
    ∏ i ∈ Finset.range n, τ^[i] (ψ p + ψ q * β) = β := by
  obtain ⟨k, hk⟩ := hdvd
  have hev : (twistPoly s n p q).eval₂ ψ β = β := by
    have := congrArg (fun g : R[X] => g.eval₂ ψ β) hk
    simp only [eval₂_sub, eval₂_X, eval₂_mul] at this
    have hq : (quad t d).eval₂ ψ β = 0 := by
      simp [quad, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, hroot]
    rw [hq, zero_mul, sub_eq_zero] at this
    exact this
  have hprod : ∏ i ∈ Finset.range n, τ^[i] (ψ p + ψ q * β) = (twistPoly s n p q).eval₂ ψ β := by
    rw [twistPoly, eval₂_finsetProd]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, iterate_map_add, iterate_map_mul,
      iterate_comp_apply s ψ τ hτ, iterate_comp_apply s ψ τ hτ, Function.iterate_fixed hβ]
  rw [hprod, hev]

theorem prod_range_two_mul {M : Type*} [CommMonoid M] (g : ℕ → M) (m : ℕ) :
    ∏ i ∈ Finset.range (2 * m), g i = ∏ k ∈ Finset.range m, (g (2 * k) * g (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ← ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc]

theorem eval_twistPoly_two_mul (m : ℕ) (p q lam mu : R) (hl : s lam = mu) (hm : s mu = lam) :
    (twistPoly s (2 * m) p q).eval lam
      = ∏ k ∈ Finset.range m, (s^[2])^[k] ((p + q * lam) * s (p + q * mu)) := by
  rw [twistPoly, eval_prod, prod_range_two_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h2 : ∀ j, s^[2 * j] lam = lam := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, hl, hm]
  have h2' : s^[2 * k + 1] mu = lam := by
    rw [Function.iterate_succ_apply, hm, h2]
  rw [← Function.iterate_mul]
  simp only [eval_add, eval_mul, eval_C, eval_X, map_mul s, map_add s, iterate_map_mul,
    iterate_map_add]
  rw [h2 k, ← Function.iterate_succ_apply s (2 * k) p, ← Function.iterate_succ_apply s (2 * k) q,
    ← Function.iterate_succ_apply s (2 * k) mu, h2']

end Push

section Reconstruct

variable {L : Type*} [Field L] (t d : L) (σ : L →+* L) (ht : σ t = t) (hd : σ d = d) (n : ℕ)

include ht hd in

theorem exists_sigmaNormPow_eq_of_dvd (hd0 : d ≠ 0) (p q : L)
    (hdvd : quad t d ∣ twistPoly σ n p q - X) :
    ∃ δ : GL (Fin 2) L, (δ : Matrix (Fin 2) (Fin 2) L) = lin t d p q ∧
      ((sigmaNormPow (Matrix.GeneralLinearGroup.map σ) n δ : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) = comp t d := by
  have hΦ : Φ t d (twistPoly σ n p q) = comp t d := by
    rw [Φ_eq_of_quad_dvd_sub t d _ _ hdvd, Φ_X]

  have hdet : (lin t d p q).det ≠ 0 := by
    intro h0
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero ?_)
      rintro rfl
      rw [twistPoly, Finset.prod_range_zero, map_one] at hΦ
      have := congrFun (congrFun hΦ 1) 0
      simp at this
    have h1 : (Φ t d (twistPoly σ (m + 1) p q)).det = 0 := by
      rw [twistPoly, Finset.prod_range_succ', map_mul, Matrix.det_mul]
      simp only [Function.iterate_zero, id_eq, Φ_lin, h0, mul_zero]
    rw [hΦ, det_comp] at h1
    exact hd0 h1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, ?_⟩
  rw [coe_sigmaNormPow_of_coe_eq_lin t d σ ht hd n p q _ rfl, hΦ]

end Reconstruct

section TensorTwist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sigmaTensor_iterate_tmul (i : ℕ) (l : L) (a : A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[i] (l ⊗ₜ[K] a) = (σ^[i] l) ⊗ₜ[K] a := by
  induction i generalizing l with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sigmaTensor_tmul, ih]

theorem sigmaTensor_algebraMap (k : K) :
    AutomorphicForm.sigmaTensor K L A σ (algebraMap K (L ⊗[K] A) k) = algebraMap K (L ⊗[K] A) k :=
  (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)).commutes k

variable [FiniteDimensional K L] [IsGalois K L]

theorem sigmaTensor_iterate_finrank (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : L ⊗[K] A) : (AutomorphicForm.sigmaTensor K L A σ)^[Module.finrank K L] x = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact iterate_map_zero _ _
  | tmul l a => rw [sigmaTensor_iterate_tmul, iterate_finrank_apply_of_generator hgen]
  | add x y hx hy => rw [iterate_map_add, hx, hy]

end TensorTwist

section LocalPush

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (A : Type) [CommRing A] [Algebra K A] {σ : L ≃ₐ[K] L}
  (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t d : K)

theorem normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ
      = sigmaNormPow (Matrix.GeneralLinearGroup.map (AutomorphicForm.sigmaTensor K L A σ))
          (Module.finrank K L) δ := by
  rw [sigmaNormPow_def, sigmaPartialNorm_eq_prod_map_range]
  rfl

theorem coe_toTensorGL_of_coe_eq_comp (Cu : GL (Fin 2) K)
    (hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d) :
    ((AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.map (algebraMap K A) Cu) :
        GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
      = comp (algebraMap K (L ⊗[K] A) t) (algebraMap K (L ⊗[K] A) d) := by
  have h1 : ((AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.map (algebraMap K A) Cu) :
      GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
        = (Cu : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (L ⊗[K] A)) := by
    ext i j
    change (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
      (algebraMap K A ((Cu : Matrix (Fin 2) (Fin 2) K) i j)) = _
    exact AlgHom.commutes _ _
  rw [h1, hCu, comp_map]

include hgen in

theorem exists_dvd_of_isNormOf (Cu : GL (Fin 2) K) (hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.map (algebraMap K A) Cu) δ) :
    ∃ p q : L ⊗[K] A, quad (algebraMap K (L ⊗[K] A) t) (algebraMap K (L ⊗[K] A) d) ∣
      twistPoly (AutomorphicForm.sigmaTensor K L A σ) (Module.finrank K L) p q - X := by
  obtain ⟨y, hy⟩ := hN
  rw [AutomorphicForm.IsNormConjugator, normString_eq_sigmaNormPow] at hy
  exact exists_twistPoly_sub_X_dvd _ _ (AutomorphicForm.sigmaTensor K L A σ)
    (sigmaTensor_algebraMap K L A σ t) (sigmaTensor_algebraMap K L A σ d) (Module.finrank K L)
    (sigmaTensor_iterate_finrank K L A σ hgen) _ δ y (coe_toTensorGL_of_coe_eq_comp K L A t d Cu hCu) hy

include hgen in

theorem local_push_inert {B : Type*} [CommRing B] [Algebra K B]
    (ψ : L ⊗[K] A →ₐ[K] B) (τB : B →+* B)
    (hτ : ∀ x, τB (ψ x) = ψ (AutomorphicForm.sigmaTensor K L A σ x))
    (β : B) (hβ : τB β = β) (hroot : β ^ 2 - algebraMap K B t * β + algebraMap K B d = 0)
    (Cu : GL (Fin 2) K) (hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.map (algebraMap K A) Cu) δ) :
    ∃ z : B, ∏ i ∈ Finset.range (Module.finrank K L), τB^[i] z = β := by
  obtain ⟨p, q, hdvd⟩ := exists_dvd_of_isNormOf K L A hgen t d Cu hCu δ hN
  refine ⟨ψ p + ψ q * β, ?_⟩
  have hroot' : β ^ 2 - ψ.toRingHom (algebraMap K (L ⊗[K] A) t) * β
      + ψ.toRingHom (algebraMap K (L ⊗[K] A) d) = 0 := by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes] using hroot
  have := prod_iterate_eq_of_dvd _ _ (AutomorphicForm.sigmaTensor K L A σ) (Module.finrank K L)
    ψ.toRingHom τB hτ β hβ hroot' p q hdvd
  simpa using this

include hgen in

theorem local_push_split {B : Type*} [CommRing B] [Algebra K B]
    (ψ : L ⊗[K] A →ₐ[K] B) (τB : B →+* B)
    (hτ : ∀ x, τB (ψ x) = ψ (AutomorphicForm.sigmaTensor K L A σ
      (AutomorphicForm.sigmaTensor K L A σ x)))
    (lam : L) (hlam : lam ^ 2 - algebraMap K L t * lam + algebraMap K L d = 0)
    (hσlam : σ lam = algebraMap K L t - lam) (m : ℕ) (hm : Module.finrank K L = 2 * m)
    (Cu : GL (Fin 2) K) (hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.map (algebraMap K A) Cu) δ) :
    ∃ z : B, ∏ k ∈ Finset.range m, τB^[k] z = ψ (lam ⊗ₜ[K] 1) := by
  obtain ⟨p, q, hdvd⟩ := exists_dvd_of_isNormOf K L A hgen t d Cu hCu δ hN
  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  set lamT : L ⊗[K] A := lam ⊗ₜ[K] 1
  set muT : L ⊗[K] A := (algebraMap K L t - lam) ⊗ₜ[K] 1
  have hsl : s lamT = muT := by rw [hs, sigmaTensor_tmul, hσlam]
  have hsm : s muT = lamT := by
    rw [hs, sigmaTensor_tmul, map_sub, hσlam, AlgEquiv.commutes, sub_sub_cancel]

  have hroot : (quad (algebraMap K (L ⊗[K] A) t) (algebraMap K (L ⊗[K] A) d)).eval lamT = 0 := by
    rw [quad_eval]
    have e1 : algebraMap K (L ⊗[K] A) t = algebraMap K L t ⊗ₜ[K] (1 : A) := rfl
    have e2 : algebraMap K (L ⊗[K] A) d = algebraMap K L d ⊗ₜ[K] (1 : A) := rfl
    rw [e1, e2]
    simp only [lamT, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_pow,
      one_mul, ← TensorProduct.sub_tmul, ← TensorProduct.add_tmul, hlam, TensorProduct.zero_tmul]
  have hev : (twistPoly s (Module.finrank K L) p q).eval lamT = lamT := by
    obtain ⟨k, hk⟩ := hdvd
    have := congrArg (fun g => Polynomial.eval lamT g) hk
    simp only [eval_sub, eval_X, eval_mul, hroot, zero_mul, sub_eq_zero] at this
    exact this
  rw [hm, eval_twistPoly_two_mul s m p q lamT muT hsl hsm] at hev
  set u := (p + q * lamT) * s (p + q * muT) with hu
  refine ⟨ψ u, ?_⟩
  have hτ' : ∀ x, τB (ψ.toRingHom x) = ψ.toRingHom ((s.comp s) x) := fun x => hτ x
  have h2 : (⇑s)^[2] = ⇑(s.comp s) := by ext x; simp [Function.iterate_succ]
  calc ∏ k ∈ Finset.range m, τB^[k] (ψ u)
      = ∏ k ∈ Finset.range m, ψ ((s.comp s)^[k] u) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        have := iterate_comp_apply (s.comp s) ψ.toRingHom τB hτ' k u
        simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this
    _ = ψ (∏ k ∈ Finset.range m, ((⇑s)^[2])^[k] u) := by rw [map_prod, h2]
    _ = ψ lamT := by rw [hev]

end LocalPush

section Global

variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  [FiniteDimensional E M] {τ : M ≃ₐ[E] M} (hgenτ : ∀ τ' : M ≃ₐ[E] M, τ' ∈ Subgroup.zpowers τ)

abbrev tauR (R : Type*) [CommRing R] [Algebra E R] (τ : M ≃ₐ[E] M) : R ⊗[E] M →ₐ[E] R ⊗[E] M :=
  Algebra.TensorProduct.map (AlgHom.id E R) (τ : M →ₐ[E] M)

theorem tauR_pow_apply (R : Type*) [CommRing R] [Algebra E R] (τ : M ≃ₐ[E] M) (i : ℕ) (z : R ⊗[E] M) :
    Algebra.TensorProduct.map (AlgHom.id E R) ((τ ^ i : M ≃ₐ[E] M) : M →ₐ[E] M) z
      = (tauR E M R τ)^[i] z := by
  induction i generalizing z with
  | zero =>
      simp only [pow_zero, Function.iterate_zero, id_eq]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => rw [map_add, hx, hy]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ← ih, pow_succ']
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]

include hgenτ in

theorem norm_eq_of_prod_iterate_eq [IsGalois E M] (R : Type) [CommRing R] [Algebra E R]
    (hinj : Function.Injective (algebraMap R (R ⊗[E] M)))
    (z : R ⊗[E] M) (r : R)
    (hz : ∏ i ∈ Finset.range (Module.finrank E M), (tauR E M R τ)^[i] z = algebraMap R (R ⊗[E] M) r) :
    Algebra.norm R z = r := by
  apply hinj
  rw [Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv E M R z,
    prod_algEquiv_eq_prod_range_of_generator hgenτ, ← hz]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact tauR_pow_apply E M R τ i z

include hgenτ in

theorem exists_prod_pow_eq_of_local [IsGalois E M] (a : Eˣ)
    (hfinE : ∀ w : HeightOneSpectrum (𝓞 E), ∃ z : w.adicCompletion E ⊗[E] M,
      ∏ i ∈ Finset.range (Module.finrank E M), (tauR E M (w.adicCompletion E) τ)^[i] z
        = algebraMap E (w.adicCompletion E ⊗[E] M) (a : E))
    (hinfE : ∃ z : InfiniteAdeleRing E ⊗[E] M,
      ∏ i ∈ Finset.range (Module.finrank E M), (tauR E M (InfiniteAdeleRing E) τ)^[i] z
        = algebraMap E (InfiniteAdeleRing E ⊗[E] M) (a : E)) :
    ∃ b : M, ∏ i ∈ Finset.range (Module.finrank E M), (τ ^ i) b = algebraMap E M a := by
  haveI : IsCyclic (M ≃ₐ[E] M) :=
    ⟨⟨τ, fun τ' => Subgroup.mem_zpowers_iff.mp (hgenτ τ')⟩⟩

  have hinjOf : ∀ (R : Type) [CommRing R] [Algebra E R],
      Function.Injective (algebraMap R (R ⊗[E] M)) := by
    intro R _ _
    have : (algebraMap R (R ⊗[E] M) : R → R ⊗[E] M)
        = (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[E] M) := by
      funext x; rfl
    rw [this]
    exact Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap E M).injective
  have hfin' : ∀ w : HeightOneSpectrum (𝓞 E), ∃ z : w.adicCompletion E ⊗[E] M,
      Algebra.norm (w.adicCompletion E) z = algebraMap E (w.adicCompletion E) (a : E) := by
    intro w
    obtain ⟨z, hz⟩ := hfinE w
    refine ⟨z, norm_eq_of_prod_iterate_eq E M hgenτ _ (hinjOf _) z _ ?_⟩
    rw [hz, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (w.adicCompletion E ⊗[E] M)]
  have hinf' : ∃ z : InfiniteAdeleRing E ⊗[E] M,
      Algebra.norm (InfiniteAdeleRing E) z = algebraMap E (InfiniteAdeleRing E) (a : E) := by
    obtain ⟨z, hz⟩ := hinfE
    refine ⟨z, norm_eq_of_prod_iterate_eq E M hgenτ _ (hinjOf _) z _ ?_⟩
    rw [hz, IsScalarTower.algebraMap_apply E (InfiniteAdeleRing E) (InfiniteAdeleRing E ⊗[E] M)]
  have hmem := NumberField.unitsMap_algebraMap_mem_range_idelicNorm_of_forall_exists_norm_eq
    E M a hfin' hinf'
  obtain ⟨b, hb⟩ := NumberField.exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic E M a hmem
  refine ⟨b, ?_⟩
  rw [← hb, Algebra.norm_eq_prod_automorphisms, prod_algEquiv_eq_prod_range_of_generator hgenτ]

end Global

section Setup

variable {K : Type} [Field K]

theorem quad_ne_zero_of_mem_ellipticCell (γ : GL (Fin 2) K) (hγ : γ ∈ AutomorphicForm.ellipticCell K)
    (a : K) :
    a ^ 2 - (γ : Matrix (Fin 2) (Fin 2) K).trace * a + (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
  intro h
  apply hγ a
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two]
  simp [h]

theorem ne_smul_one_of_mem_ellipticCell (γ : GL (Fin 2) K) (hγ : γ ∈ AutomorphicForm.ellipticCell K)
    (c : K) : (γ : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro h
  apply quad_ne_zero_of_mem_ellipticCell γ hγ c
  rw [h]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

theorem irreducible_quad_of_forall_ne (t d : K) (h : ∀ a : K, a ^ 2 - t * a + d ≠ 0) :
    Irreducible (quad t d) := by
  rw [(quad_monic t d).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [quad_natDegree]) (by rw [quad_natDegree]; norm_num), Multiset.eq_zero_iff_forall_notMem]
  intro a ha
  rw [mem_roots (quad_ne_zero t d), IsRoot, quad_eval] at ha
  exact h a ha

theorem AdjoinRoot_exists_eq {F : Type*} [Field F] (t d : F) (b : AdjoinRoot (quad t d)) :
    ∃ p q : F, b = AdjoinRoot.of (quad t d) p + AdjoinRoot.of (quad t d) q * AdjoinRoot.root (quad t d) := by
  obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective b
  set r := h %ₘ quad t d with hr
  have hdeg : r.degree ≤ 1 := by
    have := degree_modByMonic_lt h (quad_monic t d)
    rw [quad_degree] at this
    exact Order.le_of_lt_succ this
  have hr' : r = C (r.coeff 1) * X + C (r.coeff 0) := eq_X_add_C_of_degree_le_one hdeg
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  have hmk : AdjoinRoot.mk (quad t d) h = AdjoinRoot.mk (quad t d) r := by
    rw [AdjoinRoot.mk_eq_mk]
    refine ⟨h /ₘ quad t d, ?_⟩
    have := modByMonic_add_div h (quad t d)
    rw [← hr] at this
    exact (sub_eq_of_eq_add' this.symm)
  rw [hmk]
  conv_lhs => rw [hr']
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]

variable (t d : K) [Fact (Irreducible (quad t d))]

theorem root_quad_eq :
    AdjoinRoot.root (quad t d) ^ 2 - AdjoinRoot.of (quad t d) t * AdjoinRoot.root (quad t d)
      + AdjoinRoot.of (quad t d) d = 0 := by
  have h := AdjoinRoot.eval₂_root (quad t d)
  rw [quad] at h
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] at h
  exact h

theorem finrank_adjoinRoot_quad : Module.finrank K (AdjoinRoot (quad t d)) = 2 := by
  rw [(AdjoinRoot.powerBasis (quad_monic t d).ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    quad_natDegree]

theorem module_finite_adjoinRoot_quad : Module.Finite K (AdjoinRoot (quad t d)) :=
  (AdjoinRoot.powerBasis (quad_monic t d).ne_zero).finite

theorem numberField_adjoinRoot_quad [NumberField K] : NumberField (AdjoinRoot (quad t d)) := by
  haveI : CharZero (AdjoinRoot (quad t d)) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  haveI : Module.Finite K (AdjoinRoot (quad t d)) := module_finite_adjoinRoot_quad t d
  haveI : FiniteDimensional ℚ (AdjoinRoot (quad t d)) := Module.Finite.trans K (AdjoinRoot (quad t d))
  exact NumberField.mk

theorem root_quad_ne_zero (hd0 : d ≠ 0) : AdjoinRoot.root (quad t d) ≠ 0 := by
  intro h0
  have h := root_quad_eq t d
  rw [h0] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
    zero_add] at h
  exact hd0 ((AdjoinRoot.of (quad t d)).injective (by rw [h, map_zero]))

end Setup

section Generators

theorem forall_mem_zpowers_of_card_le {G : Type*} [Group G] [Fintype G] (τ : G) (n : ℕ)
    (hcard : Fintype.card G ≤ n) (hpow : ∀ i, 0 < i → i < n → τ ^ i ≠ 1) :
    (∀ g, g ∈ Subgroup.zpowers τ) ∧ Fintype.card G = n := by
  classical
  have hle : n ≤ orderOf τ := by
    by_contra hlt
    push Not at hlt
    exact hpow (orderOf τ) (orderOf_pos τ) hlt (pow_orderOf_eq_one τ)
  have hzc : Fintype.card (Subgroup.zpowers τ) = orderOf τ := Fintype.card_zpowers
  have h1 : Nat.card G ≤ Nat.card (Subgroup.zpowers τ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hzc]
    exact hcard.trans hle
  have htop : Subgroup.zpowers τ = ⊤ := Subgroup.eq_top_of_le_card _ h1
  refine ⟨fun g => htop ▸ Subgroup.mem_top g, le_antisymm hcard ?_⟩
  calc n ≤ orderOf τ := hle
    _ = Fintype.card (Subgroup.zpowers τ) := hzc.symm
    _ ≤ Fintype.card G := Fintype.card_subtype_le _

end Generators

section GenericPush

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t d : K)
  (E M : Type) [Field E] [Algebra K E] [Field M] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
  [Algebra L M] [IsScalarTower K L M]
  (A : Type) [CommRing A] [Algebra K A]
  (R : Type) [CommRing R] [Algebra E R] [Algebra K R] [IsScalarTower K E R]

def psiGen (up : A →ₐ[K] R) : L ⊗[K] A →ₐ[K] R ⊗[E] M :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeRight.restrictScalars K).comp (IsScalarTower.toAlgHom K L M))
    (((Algebra.TensorProduct.includeLeft : R →ₐ[E] R ⊗[E] M).restrictScalars K).comp up)
    (fun _ _ => Commute.all _ _)

theorem psiGen_tmul (up : A →ₐ[K] R) (l : L) (a : A) :
    psiGen K L E M A R up (l ⊗ₜ[K] a) = up a ⊗ₜ[E] algebraMap L M l := by
  rw [psiGen, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem tauR_tmul (τ : M ≃ₐ[E] M) (r : R) (m : M) : tauR E M R τ (r ⊗ₜ[E] m) = r ⊗ₜ[E] τ m := rfl

include hgen in

theorem push_inert (up : A →ₐ[K] R) (τ : M ≃ₐ[E] M)
    (hτL : ∀ l : L, τ (algebraMap L M l) = algebraMap L M (σ l))
    (αE : E) (hα : αE ^ 2 - algebraMap K E t * αE + algebraMap K E d = 0)
    (Cu : GL (Fin 2) K) (hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.map (algebraMap K A) Cu) δ) :
    ∃ z : R ⊗[E] M, ∏ i ∈ Finset.range (Module.finrank K L), (tauR E M R τ)^[i] z
      = algebraMap E (R ⊗[E] M) αE := by
  set B := R ⊗[E] M
  set ψ := psiGen K L E M A R up
  set τB : B →+* B := (tauR E M R τ).toRingHom with hτB
  have hτ : ∀ x, τB (ψ x) = ψ (AutomorphicForm.sigmaTensor K L A σ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul l a =>
        rw [sigmaTensor_tmul, psiGen_tmul, psiGen_tmul, ← hτL]
        rfl
  set β : B := algebraMap E B αE
  have hβ : τB β = β := (tauR E M R τ).commutes αE
  have hroot : β ^ 2 - algebraMap K B t * β + algebraMap K B d = 0 := by
    have : β ^ 2 - algebraMap K B t * β + algebraMap K B d
        = algebraMap E B (αE ^ 2 - algebraMap K E t * αE + algebraMap K E d) := by
      simp only [β, map_sub, map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply K E B]
    rw [this, hα, map_zero]
  obtain ⟨z, hz⟩ := local_push_inert K L A hgen t d ψ τB hτ β hβ hroot Cu hCu δ hN
  exact ⟨z, by exact hz⟩

include hgen in

theorem push_split (up : A →ₐ[K] R) (τ : M ≃ₐ[E] M)
    (hτL : ∀ l : L, τ (algebraMap L M l) = algebraMap L M (σ (σ l)))
    (lam : L) (hlam : lam ^ 2 - algebraMap K L t * lam + algebraMap K L d = 0)
    (hσlam : σ lam = algebraMap K L t - lam) (m : ℕ) (hm : Module.finrank K L = 2 * m)
    (αE : E) (hαlam : algebraMap E M αE = algebraMap L M lam)
    (Cu : GL (Fin 2) K) (hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.map (algebraMap K A) Cu) δ) :
    ∃ z : R ⊗[E] M, ∏ k ∈ Finset.range m, (tauR E M R τ)^[k] z = algebraMap E (R ⊗[E] M) αE := by
  set B := R ⊗[E] M
  set ψ := psiGen K L E M A R up
  set τB : B →+* B := (tauR E M R τ).toRingHom with hτB
  have hτ : ∀ x, τB (ψ x) = ψ (AutomorphicForm.sigmaTensor K L A σ
      (AutomorphicForm.sigmaTensor K L A σ x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul l a =>
        rw [sigmaTensor_tmul, sigmaTensor_tmul, psiGen_tmul, psiGen_tmul, ← hτL]
        rfl
  obtain ⟨z, hz⟩ := local_push_split K L A hgen t d ψ τB hτ lam hlam hσlam m hm Cu hCu δ hN
  refine ⟨z, ?_⟩
  have hz' : ∏ k ∈ Finset.range m, (tauR E M R τ)^[k] z = ψ (lam ⊗ₜ[K] 1) := by exact hz
  rw [hz', psiGen_tmul, map_one]
  symm
  calc algebraMap E (R ⊗[E] M) αE = algebraMap E R αE ⊗ₜ[E] (1 : M) :=
        Algebra.TensorProduct.algebraMap_apply αE
    _ = (αE • (1 : R)) ⊗ₜ[E] (1 : M) := by rw [Algebra.algebraMap_eq_smul_one]
    _ = (1 : R) ⊗ₜ[E] (αE • (1 : M)) := TensorProduct.smul_tmul _ _ _
    _ = 1 ⊗ₜ[E] algebraMap E M αE := by rw [Algebra.algebraMap_eq_smul_one]
    _ = 1 ⊗ₜ[E] algebraMap L M lam := by rw [hαlam]

end GenericPush

section UpMaps

variable (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

def vOf (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)

def wExt (w : HeightOneSpectrum (𝓞 E)) : (vOf K E w).Extension (𝓞 E) := ⟨w, rfl⟩

def upFin (w : HeightOneSpectrum (𝓞 E)) : (vOf K E w).adicCompletion K →ₐ[K] w.adicCompletion E where
  toRingHom := (HeightOneSpectrum.Extension.adicCompletionSemialgHom K E (wExt K E w)).toRingHom
  commutes' k := by
    have := (HeightOneSpectrum.Extension.adicCompletionSemialgHom K E (wExt K E w)).commutes k
    simp at this ⊢
    exact this

def nuOf (ν : InfinitePlace E) : InfinitePlace K := ν.comap (algebraMap K E)

scoped instance liesOver_nuOf (ν : InfinitePlace E) : ν.1.LiesOver (nuOf K E ν).1 := ⟨rfl⟩

def upInf (ν : InfinitePlace E) : InfiniteAdeleRing K →ₐ[K] ν.Completion :=
  (IsScalarTower.toAlgHom K (nuOf K E ν).Completion ν.Completion).comp
    (Pi.evalAlgHom K (fun v : InfinitePlace K => v.Completion) (nuOf K E ν))

scoped instance algebraInfiniteAdeleRing : Algebra K (InfiniteAdeleRing E) :=
  inferInstanceAs (Algebra K (Π ν : InfinitePlace E, ν.Completion))

scoped instance isScalarTowerInfiniteAdeleRing : IsScalarTower K E (InfiniteAdeleRing E) :=
  inferInstanceAs (IsScalarTower K E (Π ν : InfinitePlace E, ν.Completion))

def upInfAll : InfiniteAdeleRing K →ₐ[K] InfiniteAdeleRing E :=
  Pi.algHom K (fun ν : InfinitePlace E => ν.Completion) (fun ν => upInf K E ν)

end UpMaps

section CaseInert

variable (K L : Type) [Field K] [Field L] [Algebra K L] (t d : K)
  [Fact (Irreducible (quad t d))]
  [Fact (Irreducible (quad (algebraMap K L t) (algebraMap K L d)))]

abbrev EI := AdjoinRoot (quad t d)
abbrev MI := AdjoinRoot (quad (algebraMap K L t) (algebraMap K L d))

def phiEM : EI K t d →+* MI K L t d :=
  AdjoinRoot.lift (algebraMap K (MI K L t d)) (AdjoinRoot.root _) (by
    have h := AdjoinRoot.eval₂_root (quad (algebraMap K L t) (algebraMap K L d))
    rw [eval₂_eq_eval_map] at h ⊢
    rw [IsScalarTower.algebraMap_eq K L (MI K L t d), ← Polynomial.map_map, quad_map]
    exact h)

scoped instance algebraEM : Algebra (EI K t d) (MI K L t d) := (phiEM K L t d).toAlgebra

theorem algebraMap_EM : algebraMap (EI K t d) (MI K L t d) = phiEM K L t d := rfl

scoped instance isScalarTower_KEM : IsScalarTower K (EI K t d) (MI K L t d) :=
  IsScalarTower.of_algebraMap_eq fun k => by
    rw [algebraMap_EM, AdjoinRoot.algebraMap_eq, phiEM, AdjoinRoot.lift_of]

theorem algebraMap_EM_root :
    algebraMap (EI K t d) (MI K L t d) (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [algebraMap_EM, phiEM, AdjoinRoot.lift_root]

variable (σ : L ≃ₐ[K] L)

def tauI₀ (σ : L ≃ₐ[K] L) : MI K L t d →+* MI K L t d :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp (σ : L →+* L)) (AdjoinRoot.root _) (by
    have h := AdjoinRoot.eval₂_root (quad (algebraMap K L t) (algebraMap K L d))
    rw [eval₂_eq_eval_map] at h ⊢
    rw [← Polynomial.map_map, quad_map]
    simpa only [RingHom.coe_coe, AlgEquiv.commutes] using h)

theorem tauI₀_of (l : L) : tauI₀ K L t d σ (AdjoinRoot.of _ l) = AdjoinRoot.of _ (σ l) := by
  rw [tauI₀, AdjoinRoot.lift_of]; rfl

theorem tauI₀_root : tauI₀ K L t d σ (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [tauI₀, AdjoinRoot.lift_root]

theorem tauI₀_comp_symm : (tauI₀ K L t d σ).comp (tauI₀ K L t d σ.symm) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · ext l
    simp [tauI₀_of]
  · simp [tauI₀_root]

def tauI : MI K L t d ≃ₐ[EI K t d] MI K L t d :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (tauI₀ K L t d σ) (tauI₀ K L t d σ.symm)
    (tauI₀_comp_symm K L t d σ) (by simpa using tauI₀_comp_symm K L t d σ.symm)) (by
    intro e
    change tauI₀ K L t d σ (phiEM K L t d e) = phiEM K L t d e
    have : (tauI₀ K L t d σ).comp (phiEM K L t d) = phiEM K L t d := by
      apply AdjoinRoot.ringHom_ext
      · ext k
        simp only [RingHom.coe_comp, Function.comp_apply, phiEM, AdjoinRoot.lift_of]
        rw [IsScalarTower.algebraMap_apply K L (MI K L t d), AdjoinRoot.algebraMap_eq, tauI₀_of,
          AlgEquiv.commutes]
      · simp only [RingHom.coe_comp, Function.comp_apply, phiEM, AdjoinRoot.lift_root, tauI₀_root]
    exact RingHom.congr_fun this e)

theorem tauI_apply (x : MI K L t d) : tauI K L t d σ x = tauI₀ K L t d σ x := rfl

theorem tauI_algebraMap (l : L) : tauI K L t d σ (algebraMap L (MI K L t d) l) = algebraMap L _ (σ l) := by
  rw [tauI_apply, AdjoinRoot.algebraMap_eq, tauI₀_of]

theorem tauI_pow_algebraMap (i : ℕ) (l : L) :
    (tauI K L t d σ ^ i) (algebraMap L (MI K L t d) l) = algebraMap L _ ((σ ^ i) l) := by
  induction i generalizing l with
  | zero => simp
  | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, tauI_algebraMap, ih, pow_succ, AlgEquiv.mul_apply]

theorem tauI_pow_root (i : ℕ) : (tauI K L t d σ ^ i) (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, tauI_apply, tauI₀_root, ih]

scoped instance moduleFinite_LM : Module.Finite L (MI K L t d) := module_finite_adjoinRoot_quad _ _

variable [FiniteDimensional K L]

scoped instance moduleFinite_KM : Module.Finite K (MI K L t d) := Module.Finite.trans L _

scoped instance moduleFinite_EM : Module.Finite (EI K t d) (MI K L t d) :=
  Module.Finite.of_restrictScalars_finite K _ _

theorem finrank_EM [IsGalois K L] : Module.finrank (EI K t d) (MI K L t d) = Module.finrank K L := by
  have h1 := Module.finrank_mul_finrank K L (MI K L t d)
  have h2 := Module.finrank_mul_finrank K (EI K t d) (MI K L t d)
  rw [finrank_adjoinRoot_quad] at h1 h2
  omega

theorem tauI_generates [IsGalois K L] {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ τ', τ' ∈ Subgroup.zpowers (tauI K L t d σ)) ∧
      Fintype.card (MI K L t d ≃ₐ[EI K t d] MI K L t d) = Module.finrank (EI K t d) (MI K L t d) := by
  refine forall_mem_zpowers_of_card_le (tauI K L t d σ) _ AlgEquiv.card_le ?_
  intro i hi0 hin
  rw [finrank_EM] at hin
  have horder : orderOf σ = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  have hσi : σ ^ i ≠ 1 := pow_ne_one_of_lt_orderOf (Nat.pos_iff_ne_zero.mp hi0) (horder ▸ hin)
  intro h1
  apply hσi
  ext l
  have := tauI_pow_algebraMap K L t d σ i l
  rw [h1, AlgEquiv.one_apply] at this
  exact ((algebraMap L (MI K L t d)).injective this).symm

theorem caseInert [NumberField K] [NumberField L] [IsGalois K L] {σ : L ≃ₐ[K] L}
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hd0 : d ≠ 0)
    (Cu : GL (Fin 2) K) (hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) Cu) δv)
    (harch : ∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) Cu) δa) :
    ∃ p q : L, quad (algebraMap K L t) (algebraMap K L d) ∣
      twistPoly (σ : L →+* L) (Module.finrank K L) p q - X := by
  haveI : NumberField (EI K t d) := numberField_adjoinRoot_quad t d
  haveI : NumberField (MI K L t d) := numberField_adjoinRoot_quad _ _
  set τ := tauI K L t d σ with hτdef
  obtain ⟨hgenτ, hcard⟩ := tauI_generates K L t d hgen
  haveI : IsGalois (EI K t d) (MI K L t d) := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [Nat.card_eq_fintype_card, hcard]
  set αE : EI K t d := AdjoinRoot.root (quad t d)
  have hα : αE ^ 2 - algebraMap K (EI K t d) t * αE + algebraMap K (EI K t d) d = 0 := by
    rw [AdjoinRoot.algebraMap_eq]; exact root_quad_eq t d
  have hα0 : αE ≠ 0 := root_quad_ne_zero t d hd0
  have hτL : ∀ l : L, τ (algebraMap L (MI K L t d) l) = algebraMap L _ (σ l) := tauI_algebraMap K L t d σ

  have hfinE : ∀ w : HeightOneSpectrum (𝓞 (EI K t d)),
      ∃ z : w.adicCompletion (EI K t d) ⊗[EI K t d] MI K L t d,
        ∏ i ∈ Finset.range (Module.finrank (EI K t d) (MI K L t d)),
          (tauR (EI K t d) (MI K L t d) (w.adicCompletion (EI K t d)) τ)^[i] z
          = algebraMap (EI K t d) _ ((Units.mk0 αE hα0 : (EI K t d)ˣ) : EI K t d) := by
    intro w
    obtain ⟨δv, hδv⟩ := hfin (vOf K (EI K t d) w)
    rw [finrank_EM, Units.val_mk0]
    exact push_inert K L hgen t d (EI K t d) (MI K L t d) _ _ (upFin K (EI K t d) w) τ hτL αE hα Cu hCu δv hδv
  have hinfE : ∃ z : InfiniteAdeleRing (EI K t d) ⊗[EI K t d] MI K L t d,
        ∏ i ∈ Finset.range (Module.finrank (EI K t d) (MI K L t d)),
          (tauR (EI K t d) (MI K L t d) (InfiniteAdeleRing (EI K t d)) τ)^[i] z
          = algebraMap (EI K t d) _ ((Units.mk0 αE hα0 : (EI K t d)ˣ) : EI K t d) := by
    obtain ⟨δa, hδa⟩ := harch
    rw [finrank_EM, Units.val_mk0]
    exact push_inert K L hgen t d (EI K t d) (MI K L t d) _ _ (upInfAll K (EI K t d)) τ hτL αE hα Cu hCu δa hδa
  obtain ⟨b, hb⟩ := exists_prod_pow_eq_of_local (EI K t d) (MI K L t d) hgenτ (Units.mk0 αE hα0) hfinE hinfE
  rw [Units.val_mk0, algebraMap_EM_root, finrank_EM] at hb

  obtain ⟨p, q, hbpq⟩ := AdjoinRoot_exists_eq (algebraMap K L t) (algebraMap K L d) b
  refine ⟨p, q, ?_⟩
  rw [← AdjoinRoot.mk_eq_mk, AdjoinRoot.mk_X, ← hb, twistPoly, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hbpq, map_add (tauI K L t d σ ^ i), map_mul (tauI K L t d σ ^ i), ← AdjoinRoot.algebraMap_eq,
    tauI_pow_algebraMap, tauI_pow_algebraMap, ← hτdef, tauI_pow_root]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq,
    AlgEquiv.coe_pow, RingHom.coe_coe]

end CaseInert

section CaseSplit

open IntermediateField

variable (K L : Type) [Field K] [Field L] [Algebra K L] (t d : K)

theorem iterate_two_mul_eq {α : Type*} (f : α → α) (k : ℕ) : (f^[2])^[k] = f^[2 * k] :=
  (Function.iterate_mul f 2 k).symm

theorem caseSplit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [Fact (Irreducible (quad t d))] (hd0 : d ≠ 0) (hK : ∀ a : K, a ^ 2 - t * a + d ≠ 0)
    (lam : L) (hlam : lam ^ 2 - algebraMap K L t * lam + algebraMap K L d = 0)
    (Cu : GL (Fin 2) K) (hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) Cu) δv)
    (harch : ∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) Cu) δa) :
    ∃ p q : L, quad (algebraMap K L t) (algebraMap K L d) ∣
      twistPoly (σ : L →+* L) (Module.finrank K L) p q - X := by
  set tL := algebraMap K L t with htL
  set dL := algebraMap K L d with hdL
  set mu := tL - lam with hmu

  have hσt : σ tL = tL := σ.commutes t
  have hσd : σ dL = dL := σ.commutes d
  have hσroot : (σ lam) ^ 2 - tL * σ lam + dL = 0 := by
    have := congrArg σ hlam
    simpa only [map_sub, map_add, map_mul, map_pow, hσt, hσd, map_zero] using this
  have hσne : σ lam ≠ lam := by
    intro h
    obtain ⟨k, hk⟩ := mem_range_algebraMap_of_generator_apply_eq hgen h
    apply hK k
    apply (algebraMap K L).injective
    simp only [map_sub, map_add, map_mul, map_pow, map_zero, hk]
    exact hlam
  have hσlam : σ lam = tL - lam := by
    have h0 : (σ lam - lam) * (σ lam - (tL - lam)) = 0 := by linear_combination hσroot - hlam
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hσne
    · exact sub_eq_zero.mp h
  have hσmu : σ mu = lam := by rw [hmu, map_sub, hσt, hσlam, sub_sub_cancel]
  have hσσ : σ (σ lam) = lam := by rw [hσlam]; exact hσmu
  have hne : lam ≠ mu := fun h => hσne (by rw [hσlam, ← hmu, ← h])
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0] at hlam
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero, zero_add] at hlam
    exact hd0 ((algebraMap K L).injective (hlam.trans (map_zero _).symm))

  set E := K⟮lam⟯ with hE
  haveI : NumberField E := by
    haveI : FiniteDimensional ℚ E := Module.Finite.trans K E
    exact NumberField.mk
  have hint : IsIntegral K lam := Algebra.IsIntegral.isIntegral lam
  have hminpoly : minpoly K lam = quad t d := by
    symm
    apply minpoly.eq_of_irreducible_of_monic (Fact.out)
    · rw [quad]; simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]; exact hlam
    · exact quad_monic t d
  have hfinrankE : Module.finrank K E = 2 := by
    rw [hE, adjoin.finrank hint, hminpoly, quad_natDegree]
  set m := Module.finrank E L with hm
  have hKL : Module.finrank K L = 2 * m := by
    rw [← Module.finrank_mul_finrank K E L, hfinrankE]

  have hfixE : ∀ e : E, σ (σ (e : L)) = e := by
    have hle : K⟮lam⟯ ≤ fixedField (Subgroup.zpowers (σ * σ)) := by
      rw [adjoin_simple_le_iff, mem_fixedField_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have h1 : (σ * σ) lam = lam := hσσ
      have : (σ * σ) • lam = lam := h1
      rw [← MulAction.mem_stabilizer_iff] at this
      have hk : (σ * σ) ^ k ∈ MulAction.stabilizer (L ≃ₐ[K] L) lam := Subgroup.zpow_mem _ this k
      exact MulAction.mem_stabilizer_iff.mp hk
    intro e
    have := (mem_fixedField_iff _ _).mp (hle e.2) (σ * σ) (Subgroup.mem_zpowers _)
    exact this
  let τ : L ≃ₐ[E] L := AlgEquiv.ofRingEquiv (f := ((σ * σ : L ≃ₐ[K] L) : L ≃+* L)) (fun e => hfixE e)
  have hτ : ∀ x, τ x = σ (σ x) := fun x => rfl
  have hτpow : ∀ (k : ℕ) (x : L), (τ ^ k) x = (σ ^ (2 * k)) x := by
    intro k x
    rw [AlgEquiv.coe_pow, AlgEquiv.coe_pow, ← iterate_two_mul_eq]
    rfl
  have hpar : ∀ k, (σ ^ (2 * k)) lam = lam ∧ (σ ^ (2 * k + 1)) lam = mu := by
    intro k
    induction k with
    | zero => exact ⟨rfl, by simpa using hσlam⟩
    | succ k ih =>
        constructor
        · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ', AlgEquiv.mul_apply, ih.2, hσmu]
        · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, pow_succ', pow_succ', AlgEquiv.mul_apply,
            AlgEquiv.mul_apply, ih.2, hσmu, hσlam]
  set αE : E := AdjoinSimple.gen K lam
  have hαlam : algebraMap E L αE = lam := AdjoinSimple.algebraMap_gen K lam
  have hgenτ : ∀ τ' : L ≃ₐ[E] L, τ' ∈ Subgroup.zpowers τ := by
    intro τ'
    have hres : τ'.restrictScalars K ∈ Subgroup.zpowers σ := hgen _
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hres
    obtain ⟨i, hi⟩ := hres
    have hix : ∀ x, (σ ^ i) x = τ' x := fun x => by rw [hi]; rfl
    have hfix : (σ ^ i) lam = lam := by
      rw [hix, ← hαlam]
      exact τ'.commutes αE
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [zpow_natCast]
      ext x
      rw [hτpow, ← hk, hix]
    · exfalso
      rw [hk, (hpar k).2] at hfix
      exact hne hfix.symm
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  have hα0 : αE ≠ 0 := by
    intro h
    apply hlam0
    rw [← hαlam, h, map_zero]
  have hτL : ∀ l : L, τ (algebraMap L L l) = algebraMap L L (σ (σ l)) := fun l => rfl

  have hfinE : ∀ w : HeightOneSpectrum (𝓞 E), ∃ z : w.adicCompletion E ⊗[E] L,
      ∏ i ∈ Finset.range (Module.finrank E L), (tauR E L (w.adicCompletion E) τ)^[i] z
        = algebraMap E _ ((Units.mk0 αE hα0 : Eˣ) : E) := by
    intro w
    obtain ⟨δv, hδv⟩ := hfin (vOf K E w)
    rw [Units.val_mk0]
    exact push_split K L hgen t d E L _ _ (upFin K E w) τ hτL lam hlam hσlam m hKL αE hαlam Cu hCu δv hδv
  have hinfE : ∃ z : InfiniteAdeleRing E ⊗[E] L,
      ∏ i ∈ Finset.range (Module.finrank E L), (tauR E L (InfiniteAdeleRing E) τ)^[i] z
        = algebraMap E _ ((Units.mk0 αE hα0 : Eˣ) : E) := by
    obtain ⟨δa, hδa⟩ := harch
    rw [Units.val_mk0]
    exact push_split K L hgen t d E L _ _ (upInfAll K E) τ hτL lam hlam hσlam m hKL αE hαlam Cu hCu δa hδa
  obtain ⟨b, hb⟩ := exists_prod_pow_eq_of_local E L hgenτ (Units.mk0 αE hα0) hfinE hinfE
  rw [Units.val_mk0, hαlam] at hb

  have hb' : ∏ k ∈ Finset.range m, ((⇑(σ : L →+* L))^[2])^[k] b = lam := by
    rw [← hb]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hτpow, AlgEquiv.coe_pow, iterate_two_mul_eq]
    rfl

  set q := (b - 1) * (lam - mu)⁻¹ with hq
  set p := b - q * lam with hp
  have hsub : lam - mu ≠ 0 := sub_ne_zero.mpr hne
  have hpql : p + q * lam = b := by rw [hp]; ring
  have hpqm : p + q * mu = 1 := by
    rw [hp, hq]
    field_simp
    ring
  refine ⟨p, q, ?_⟩
  have hfac : quad tL dL = (X - C lam) * (X - C mu) := by
    have hprod : lam * mu = dL := by rw [hmu]; linear_combination -hlam
    have hsum : lam + mu = tL := by rw [hmu]; ring
    rw [quad, ← hprod, ← hsum]
    simp only [map_add, map_mul]
    ring
  rw [hfac]
  have hσ' : (σ : L →+* L) lam = mu := hσlam
  have hσ'' : (σ : L →+* L) mu = lam := hσmu
  apply IsCoprime.mul_dvd (isCoprime_X_sub_C_of_isUnit_sub (Ne.isUnit hsub))
  · rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_X, sub_eq_zero, hKL,
      eval_twistPoly_two_mul (σ : L →+* L) m p q lam mu hσ' hσ'', hpql, hpqm, map_one, mul_one]
    exact hb'
  · rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_X, sub_eq_zero, hKL,
      eval_twistPoly_two_mul (σ : L →+* L) m p q mu lam hσ'' hσ', hpql, hpqm, one_mul]
    rw [← hσ', ← hb', map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [iterate_two_mul_eq, ← Function.iterate_succ_apply, Function.iterate_succ_apply']

end CaseSplit

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

theorem isNormOf_conj (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (γ P : GL (Fin 2) K)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.map (algebraMap K A) γ) δ) :
    AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.map (algebraMap K A) (P⁻¹ * γ * P)) δ := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y * AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.map (algebraMap K A) P), ?_⟩
  rw [AutomorphicForm.IsNormConjugator] at hy ⊢
  simp only [map_mul, map_inv, hy]
  group

theorem main {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) K) (hγ : γ ∈ AutomorphicForm.ellipticCell K)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) γ) δv)
    (harch : ∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) γ) δa) :
    LT.TwistedNorm.IsNormClass hgen (ConjClasses.mk γ) := by
  set t := (γ : Matrix (Fin 2) (Fin 2) K).trace with ht
  set d := (γ : Matrix (Fin 2) (Fin 2) K).det with hd
  have hK : ∀ a : K, a ^ 2 - t * a + d ≠ 0 := quad_ne_zero_of_mem_ellipticCell γ hγ
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero γ
  haveI : Fact (Irreducible (quad t d)) := ⟨irreducible_quad_of_forall_ne t d hK⟩
  obtain ⟨P, hP⟩ := GL2.exists_conj_eq_traceDetCompanion_units γ (ne_smul_one_of_mem_ellipticCell γ hγ)
  set Cu := P⁻¹ * γ * P with hCudef
  have hCu : (Cu : Matrix (Fin 2) (Fin 2) K) = comp t d := hP
  have hfinC : ∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) Cu) δv := fun v => by
    obtain ⟨δv, h⟩ := hfin v
    exact ⟨δv, isNormOf_conj K L _ σ γ P δv h⟩
  have harchC : ∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) Cu) δa := by
    obtain ⟨δa, h⟩ := harch
    exact ⟨δa, isNormOf_conj K L _ σ γ P δa h⟩

  have key : ∃ p q : L, quad (algebraMap K L t) (algebraMap K L d) ∣
      twistPoly (σ : L →+* L) (Module.finrank K L) p q - X := by
    by_cases hsplit : ∃ lam : L, lam ^ 2 - algebraMap K L t * lam + algebraMap K L d = 0
    · obtain ⟨lam, hlam⟩ := hsplit
      exact caseSplit K L t d hgen hd0 hK lam hlam Cu hCu hfinC harchC
    · push Not at hsplit
      haveI : Fact (Irreducible (quad (algebraMap K L t) (algebraMap K L d))) :=
        ⟨irreducible_quad_of_forall_ne _ _ hsplit⟩
      exact caseInert K L t d hgen hd0 Cu hCu hfinC harchC
  obtain ⟨p, q, hdvd⟩ := key
  have hdL0 : algebraMap K L d ≠ 0 := by simpa using hd0
  obtain ⟨δ₁, hδ₁, hN⟩ := exists_sigmaNormPow_eq_of_dvd (algebraMap K L t) (algebraMap K L d)
    (σ : L →+* L) (σ.commutes t) (σ.commutes d) (Module.finrank K L) hdL0 p q hdvd

  set h := Matrix.GeneralLinearGroup.map (algebraMap K L) P with hh
  have hσh : Matrix.GeneralLinearGroup.map (σ : L →+* L) h⁻¹ = h⁻¹ := by
    rw [map_inv, hh]
    congr 1
    apply Units.ext; ext i j
    exact σ.commutes _
  have hNC : sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ₁
      = h⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap K L) γ * h := by
    apply Units.ext
    rw [hN, hh, ← map_inv, ← map_mul, ← map_mul, ← hCudef]
    change _ = ((Cu : Matrix (Fin 2) (Fin 2) K)).map (algebraMap K L)
    rw [hCu, comp_map]
  rw [isNormClass_mk_iff]
  refine ⟨(h⁻¹)⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h⁻¹, 1, ?_⟩
  rw [sigmaNormPow_sigmaConjElt _ _ (LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self
    (fun a => iterate_finrank_apply_of_generator hgen a) h⁻¹) δ₁, hNC]
  group

end Main

end R3NormCrit
p2m_reactivate "P2MW.S_AutomorphicForm_isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf.R3NormCrit"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf.R3NormCrit"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) K) (hγ : γ ∈ AutomorphicForm.ellipticCell K)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ δv : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) γ) δv)
    (harch : ∃ δa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
        (Matrix.GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) γ) δa) :
    LT.TwistedNorm.IsNormClass hgen (ConjClasses.mk γ) :=
  R3NormCrit.main K L hgen γ hγ hfin harch

end S_AutomorphicForm_isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf
end P2MW
export P2MW.S_AutomorphicForm_isNormClass_mk_of_mem_ellipticCell_of_forall_isNormOf (solution)
