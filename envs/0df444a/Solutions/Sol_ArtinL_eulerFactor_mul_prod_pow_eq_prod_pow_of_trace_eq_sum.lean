-- Prove2me | solution 1 for ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ed4d7317-9c71-568f-9415-66e6be2a29d5

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt
import Theorems.Thm_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace
import Theorems.Thm_Matrix_charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq
import Theorems.Thm_ArtinL_Abelian_inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace ArtinL
p2m_export "ArtinL" "charpolyRev_toMatrix eulerFactor coeff coeff_one Abelian.localValue Abelian.ofSubgroup eulerFactor_eq_charpolyRev_restrict_arithFrobAt trace_restrict_invariants_eq_inv_card_mul_sum_trace Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum"
namespace C3d
p2m_open "ArtinL"
open Polynomial PowerSeries

variable {K : Type*} [Field K]

theorem mul_add_of_mul {F G S T : K⟦X⟧}
    (hF : F * S = -(d⁄dX K F)) (hG : G * T = -(d⁄dX K G)) :
    (F * G) * (S + T) = -(d⁄dX K (F * G)) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  linear_combination G * hF + F * hG

theorem prod_sum_of_mul {α : Type*} (s : Finset α) (F : α → K⟦X⟧) (S : α → K⟦X⟧)
    (hF : ∀ i ∈ s, F i * S i = -(d⁄dX K (F i))) :
    (∏ i ∈ s, F i) * (∑ i ∈ s, S i) = -(d⁄dX K (∏ i ∈ s, F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact mul_add_of_mul (hF j (Finset.mem_insert_self j s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem coe_finset_prod {α : Type*} (s : Finset α) (P : α → K[X]) :
    ((∏ i ∈ s, P i : K[X]) : K⟦X⟧) = ∏ i ∈ s, ((P i : K[X]) : K⟦X⟧) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, Polynomial.coe_mul, ih]

def g (c : K) (f : ℕ) (k : ℕ) : K := if f ∣ k + 1 then (f : K) * c ^ ((k + 1) / f) else 0

theorem g_of_eq_mul (c : K) {f : ℕ} (hf : 0 < f) {k m : ℕ} (h : k + 1 = f * m) : g c f k = (f : K) * c ^ m := by
  rw [g, if_pos ⟨m, h⟩, h, Nat.mul_div_cancel_left _ hf]

theorem g_of_not_dvd (c : K) {f k : ℕ} (h : ¬ f ∣ k + 1) : g c f k = 0 := by
  rw [g, if_neg h]

theorem one_sub_C_mul_X_pow_mul_mk (c : K) {f : ℕ} (hf : 0 < f) :
    ((1 - Polynomial.C c * Polynomial.X ^ f : K[X]) : K⟦X⟧) * PowerSeries.mk (g c f) =
      -((derivative (1 - Polynomial.C c * Polynomial.X ^ f : K[X]) : K[X]) : K⟦X⟧) := by
  have hL : ((1 - Polynomial.C c * Polynomial.X ^ f : K[X]) : K⟦X⟧) = 1 - PowerSeries.C c * PowerSeries.X ^ f := by
    simp [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  rw [hL]
  ext k

  have L : PowerSeries.coeff k ((1 - PowerSeries.C c * PowerSeries.X ^ f) * PowerSeries.mk (g c f)) =
      g c f k - c * (if f ≤ k then g c f (k - f) else 0) := by
    rw [sub_mul, one_mul, map_sub, coeff_mk, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    congr 2
    split_ifs <;> simp [coeff_mk]

  have R : PowerSeries.coeff k (-((derivative (1 - Polynomial.C c * Polynomial.X ^ f : K[X]) : K[X]) : K⟦X⟧)) =
      if k + 1 = f then c * (f : K) else 0 := by
    rw [map_neg, Polynomial.coeff_coe, Polynomial.coeff_derivative, Polynomial.coeff_sub, Polynomial.coeff_one,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Nat.succ_ne_zero k)]
    by_cases h : k + 1 = f
    · rw [if_pos h, if_pos h]; push_cast; rw [← h]; push_cast; ring
    · rw [if_neg h, if_neg h]; ring
  rw [L, R]
  by_cases hk : f ∣ k + 1
  · obtain ⟨m, hm⟩ := hk
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    rw [g_of_eq_mul c hf hm]
    by_cases hfk : f ≤ k
    · have hm2 : 2 ≤ m := by
        by_contra hlt
        have h1 : m = 1 := by omega
        subst h1; omega
      have hsub : k - f + 1 = f * (m - 1) := by
        have : f * (m - 1) = f * m - f := Nat.mul_sub_one f m
        omega
      rw [if_pos hfk, g_of_eq_mul c hf hsub, if_neg (by omega)]
      rw [show m = (m - 1) + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring
    · have hm1 : m = 1 := by
        by_contra hne
        have h2 : 2 ≤ m := by omega
        have : f * 2 ≤ f * m := Nat.mul_le_mul_left f h2
        omega
      subst hm1
      rw [if_neg hfk, if_pos (by omega)]
      ring
  · rw [g_of_not_dvd c hk]
    have hkf : ¬ (k + 1 = f) := fun h => hk ⟨1, by omega⟩
    rw [if_neg hkf]
    by_cases hfk : f ≤ k
    · rw [if_pos hfk, g_of_not_dvd c (fun ⟨m, hm⟩ => hk ⟨m + 1, by
        have : f * (m + 1) = f * m + f := Nat.mul_succ f m
        omega⟩)]
      ring
    · rw [if_neg hfk]; ring

theorem coeff_logDeriv_prod_one_sub_C_mul_X_pow {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 0 < f i) {j : ℕ} (hj : 0 < j) :
    PowerSeries.coeff j
        (((-(Polynomial.X * derivative (∏ i ∈ s, (1 - Polynomial.C (c i) * Polynomial.X ^ f i : K[X]))) : K[X]) : K⟦X⟧) *
          ((∏ i ∈ s, (1 - Polynomial.C (c i) * Polynomial.X ^ f i : K[X]) : K[X]) : K⟦X⟧)⁻¹) =
      ∑ i ∈ s with f i ∣ j, (f i : K) * c i ^ (j / f i) := by
  classical
  set E : K[X] := ∏ i ∈ s, (1 - Polynomial.C (c i) * Polynomial.X ^ f i : K[X]) with hE

  have hES : (E : K⟦X⟧) * (∑ i ∈ s, PowerSeries.mk (g (c i) (f i))) = -(d⁄dX K (E : K⟦X⟧)) := by
    have := prod_sum_of_mul s (fun i => ((1 - Polynomial.C (c i) * Polynomial.X ^ f i : K[X]) : K⟦X⟧))
      (fun i => PowerSeries.mk (g (c i) (f i))) (fun i hi => by rw [derivative_coe]; exact one_sub_C_mul_X_pow_mul_mk (c i) (hf i hi))
    rw [← coe_finset_prod] at this
    exact this

  have hE0 : PowerSeries.constantCoeff (E : K⟦X⟧) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hE, Polynomial.coeff_zero_prod]
    rw [Finset.prod_eq_one fun i hi => ?_]
    · exact one_ne_zero
    rw [Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => (Nat.pos_iff_ne_zero.1 (hf i hi)) h.symm), mul_zero, sub_zero]
  have hEinv : (E : K⟦X⟧) * (E : K⟦X⟧)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hE0

  have hXS : ((-(Polynomial.X * derivative E) : K[X]) : K⟦X⟧) * ((E : K[X]) : K⟦X⟧)⁻¹ =
      PowerSeries.X * ∑ i ∈ s, PowerSeries.mk (g (c i) (f i)) := by
    rw [Polynomial.coe_neg, Polynomial.coe_mul, Polynomial.coe_X, ← derivative_coe]
    calc -(PowerSeries.X * d⁄dX K (E : K⟦X⟧)) * ((E : K[X]) : K⟦X⟧)⁻¹
        = PowerSeries.X * ((E : K⟦X⟧) * ∑ i ∈ s, PowerSeries.mk (g (c i) (f i))) * ((E : K[X]) : K⟦X⟧)⁻¹ := by
          rw [hES]; ring
      _ = PowerSeries.X * (∑ i ∈ s, PowerSeries.mk (g (c i) (f i))) * ((E : K⟦X⟧) * ((E : K[X]) : K⟦X⟧)⁻¹) := by ring
      _ = PowerSeries.X * ∑ i ∈ s, PowerSeries.mk (g (c i) (f i)) := by rw [hEinv, mul_one]
  rw [hXS]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, (Nat.sub_add_cancel hj).symm⟩
  rw [PowerSeries.coeff_succ_X_mul, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_mk, g]

end ArtinL.C3d

set_option maxHeartbeats 1600000 in
open scoped Classical in

theorem solution {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {k : ℕ} (H : Fin k → Subgroup (F ≃ₐ[ℚ] F)) (χ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ((ρF g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * g * x ∈ H i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0))
    {p : ℕ} (hp : p.Prime) :
    ArtinL.eulerFactor ρ p *
        ∏ i, (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))),
            if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v) *
                Polynomial.X ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1) ^ (-a i).toNat =
      ∏ i, (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))),
            if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v) *
                Polynomial.X ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1) ^ (a i).toNat := by
  classical

  haveI hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  obtain ⟨P, hPmax, hPover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
  haveI := hPmax
  haveI := hPover
  obtain ⟨h, hEuler⟩ := ArtinL.eulerFactor_eq_charpolyRev_restrict_arithFrobAt ρ F ρF hρ hp P
  rw [hEuler]

  set R := Deformation.matrixRepresentation ρF with hR

  have hp0 : ∀ i, ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ≠ 0 := fun i => by exact_mod_cast hp.ne_zero
  have hfin : ∀ i, {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))) |
      ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal}.Finite := fun i =>
    (Ideal.finite_factors ((Ideal.span_singleton_eq_bot.not).2 (hp0 i))).subset fun v hv =>
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  let S : ∀ i, Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i)))) := fun i => (hfin i).toFinset
  have hS : ∀ i v, v ∈ S i ↔ ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal := fun i v =>
    (hfin i).mem_toFinset
  let c : ∀ i, IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))) → ℂ := fun i v =>
    ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v
  let f : ∀ i, IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))) → ℕ := fun i v =>
    (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal
  have hf : ∀ i, ∀ v ∈ S i, 0 < f i v := by
    intro i v hv
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    haveI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
      refine ⟨hpmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_⟩
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      simpa using (hS i v).1 hv
    exact Ideal.inertiaDeg'_pos (Ideal.span {(p : ℤ)}) v.asIdeal
  have hE : ∀ i, (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))),
      if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal then
        (1 - Polynomial.C (ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v) *
          Polynomial.X ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
      else 1) = ∏ v ∈ S i, (1 - Polynomial.C (c i v) * Polynomial.X ^ f i v : Polynomial ℂ) := by
    intro i
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S i) (fun v hv => ?_)]
    · exact Finset.prod_congr rfl fun v hv => by rw [if_pos ((hS i v).1 hv)]
    · rw [Finset.mem_coe, hS]
      by_contra hpv
      exact hv (by simp only [if_neg hpv])
  simp only [hE]

  let V := Representation.invariants (R.comp (P.inertia (F ≃ₐ[ℚ] F)).subtype)
  let b := Module.finBasis ℂ V
  set T : V →ₗ[ℂ] V := (R (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P)).restrict h with hTdef
  set M : Matrix _ _ ℂ := LinearMap.toMatrix b b T with hM
  rw [← ArtinL.charpolyRev_toMatrix b]

  refine Matrix.charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq M
    (fun i => ∏ v ∈ S i, (1 - Polynomial.C (c i v) * Polynomial.X ^ f i v : Polynomial ℂ)) (fun i => ?_) a (fun j hj => ?_)
  ·
    rw [Polynomial.coeff_zero_prod]
    exact Finset.prod_eq_one fun v hv => by
      rw [Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun h0 => (Nat.pos_iff_ne_zero.1 (hf i v hv)) h0.symm), mul_zero, sub_zero]
  ·
    have hTpow : ∀ (m : ℕ) (x : V), ((T ^ m) x : (Fin n → ℂ)) = ((R (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P)) ^ m) (x : Fin n → ℂ) := by
      intro m
      induction m with
      | zero => intro x; simp
      | succ m ih =>
        intro x
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
        rfl
    have hstab : ∀ w ∈ V, R (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j) w ∈ V := by
      intro w hw
      have := (T ^ j) ⟨w, hw⟩ |>.2
      rwa [hTpow, ← map_pow] at this
    have hT : T ^ j = (R (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j)).restrict hstab :=
      LinearMap.ext fun x => Subtype.ext (by rw [hTpow, LinearMap.coe_restrict_apply, map_pow])

    have htrR : ∀ g : F ≃ₐ[ℚ] F, LinearMap.trace ℂ _ (R g) = ((ρF g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := by
      intro g
      rw [hR, Deformation.matrixRepresentation_apply, ← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)),
        LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    rw [hM, LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace, hT,
      ArtinL.trace_restrict_invariants_eq_inv_card_mul_sum_trace R (P.inertia (F ≃ₐ[ℚ] F)) (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j) hstab]
    simp only [htrR, htr, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_

    have hC3 := ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum F (H i) (χ i) hp P hj
    have hsupp : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))) =>
        if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal ∧ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j then
          ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : ℂ) *
            ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v ^ (j / (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal)
        else 0) ⊆ ↑(S i) := by
      intro v hv
      rw [Finset.mem_coe, hS]
      by_contra hpv
      exact hv (by simp only [hpv, false_and, if_false])
    rw [finsum_eq_sum_of_support_subset _ hsupp] at hC3
    have hC3' : (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)⁻¹ *
        ∑ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), ((Nat.card ↥(H i) : ℂ)⁻¹ *
          ∑ x : F ≃ₐ[ℚ] F,
            if hx : x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : F ≃ₐ[ℚ] F)) * x ∈ H i then
              (((χ i) ⟨x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : F ≃ₐ[ℚ] F)) * x, hx⟩ : ℂˣ) : ℂ)
            else 0) = ∑ v ∈ S i with f i v ∣ j, (f i v : ℂ) * c i v ^ (j / f i v) := by
      rw [hC3, Finset.sum_filter]
      exact Finset.sum_congr rfl fun v hv => by simp only [(hS i v).1 hv, true_and]; rfl
    rw [ArtinL.C3d.coeff_logDeriv_prod_one_sub_C_mul_X_pow (S i) (c i) (f i) (hf i) hj, ← hC3']
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun x _ => by ring

end S_ArtinL_eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
end P2MW
export P2MW.S_ArtinL_eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum (solution)
