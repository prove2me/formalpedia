-- Prove2me | solution 1 for ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0fdf54b3-824e-5e16-811f-3dca4bf81ca8

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_hasProd_inv_eval_eulerFactor_of_lSeriesSummable
import Theorems.Thm_ArtinL_eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
import Theorems.Thm_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver
import Theorems.Thm_ArtinL_LSeriesSummable_coeff_of_one_lt_re
import Theorems.Thm_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Classical in

theorem solution {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {k : ℕ} (H : Fin k → Subgroup (F ≃ₐ[ℚ] F)) (χ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ((ρF g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * g * x ∈ H i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0))
    {s : ℂ} (hs : 1 < s.re) :
    _root_.LSeries (ArtinL.coeff ρ) s *
        ∏ i, ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i)) s ^ (-a i).toNat =
      ∏ i, ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i)) s ^ (a i).toNat := by
  classical

  have hfin : GaloisFactorsThroughFiniteLevel ρ := by
    refine ⟨F, inferInstance, fun σ hσ => ?_⟩
    have h1 : AlgEquiv.restrictNormalHom F σ = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap F (AlgebraicClosure ℚ)).injective
      rw [show AlgEquiv.restrictNormalHom F σ = σ.restrictNormal F from rfl, AlgEquiv.restrictNormal_commutes,
        AlgEquiv.one_apply]
      exact hσ x.1 x.2
    rw [hρ, MonoidHom.comp_apply, h1, map_one]
  have hsum := ArtinL.LSeriesSummable_coeff_of_one_lt_re ρ hfin hs
  obtain ⟨-, hρprod⟩ := ArtinL.hasProd_inv_eval_eulerFactor_of_lSeriesSummable ρ hsum

  have hχprod := fun i => ArtinL.Abelian.hasProd_primes_inv_eval_prod_placesOver
    ↥(IntermediateField.fixedField (H i)) ↥F (ArtinL.Abelian.ofSubgroup (H i) (χ i)) hs

  have hL := hρprod.mul (hasProd_prod (s := Finset.univ) fun i _ => (hχprod i).pow (-a i).toNat)
  have hR := hasProd_prod (s := Finset.univ) fun i _ => (hχprod i).pow (a i).toNat
  refine HasProd.unique (hL.congr_fun fun q => ?_) hR

  have key := congrArg (fun P : Polynomial ℂ => (P.eval (((q : ℕ) : ℂ) ^ (-s)))⁻¹)
    (ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum ρ F ρF hρ H χ a htr q.2)
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_pow, mul_inv] at key
  rw [← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib] at key
  simp only [← inv_pow] at key
  simpa only [ArtinL.LSeries] using key.symm

end S_ArtinL_lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
end P2MW
export P2MW.S_ArtinL_lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum (solution)
