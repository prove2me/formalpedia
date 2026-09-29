-- Prove2me | solution 1 for AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f1af1af9-585b-50e4-916f-3f85741a95e7

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Theorems.Thm_NumberField_sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]

    (C : ℝ) (hC : 0 < C)
    (hCl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ENNReal, Measurable g →
        ∫⁻ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          ENNReal.ofReal C *
            ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hCi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
            (HaarQuotient.measure νZL N1 μN) ↔
          IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          C * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (hΞne : Ξ.Nonempty)

    (Δφ : Finset (GL (Fin 2) L)) (ΔK : Finset (GL (Fin 2) K))
    (n : GL (Fin 2) L → GL (Fin 2) K) (hn : ∀ t ∈ Δφ, n t ∈ ΔK)
    (hninj : ∀ t ∈ Δφ, ∀ t' ∈ Δφ, n t = n t' → t = t')
    (hnr : ∀ t ∈ Δφ, ((n t : Matrix (Fin 2) (Fin 2) K) 0 0 / (n t : Matrix (Fin 2) (Fin 2) K) 1 1) =
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1))

    (JL : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ) (JK : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (Win : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hJLi : ∀ t ∈ Δφ, Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * JL t wq.out)
      (HaarQuotient.measure νZL N1 μN))
    (hJKm : ∀ γ ∈ ΔK, Measurable (JK γ))
    (hJKi : ∀ γ ∈ ΔK, ∀ ξ ∈ Ξ,
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z) νZK)
    (hJK0 : ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm → JK γ z = 0)

    (cG cT cG' cT' : ℝ) (hcG : 0 < cG) (hcT : 0 < cT) (hcG' : 0 < cG') (hcT' : 0 < cT')
    (c₀' : NNReal) (hρ : (cG' * cT) / (cG * cT') = (c₀' : ℝ))
    (hwin : ∀ t ∈ Δφ, ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      JL t w = (Module.finrank K L : ℂ) * (((cG' * cT) / (cG * cT') : ℝ) : ℂ) * JK (n t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) +
        ((cG' * cT'⁻¹ : ℝ) : ℂ) * Win t w)
    (hvan : ∀ γ ∈ ΔK, (∀ t ∈ Δφ, n t ≠ γ) →
      ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z ∂νZK = 0)

    (κ₀L κL κ₀K κK : ℝ) (hκ₀K : 0 < κ₀K) (hκK : 0 < κK) :
    ∑ t ∈ Δφ, ((κ₀L : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
            then (1 / 2 : ℂ) else 1)) *
        (((κL : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * JL t wq.out ∂(HaarQuotient.measure νZL N1 μN)) =
      (Module.finrank K L : ℂ) * (((κ₀L : ℂ) * (κL : ℂ) * (C : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * (κK : ℂ) * (Ξ.card : ℂ))) *
        ∑ ξ ∈ Ξ, ∑ γ ∈ ΔK, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z ∂νZK) +
      ((cG' * cT'⁻¹ : ℝ) : ℂ) *
        ∑ t ∈ Δφ, ((κ₀L : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
            then (1 / 2 : ℂ) else 1)) *
          (((κL : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * Win t wq.out ∂(HaarQuotient.measure νZL N1 μN)) := by
  set Nrm := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hNrm
  set S : GL (Fin 2) K → ℂ := fun γ =>
    ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z ∂νZK with hS
  set ℓ : ℂ := (Module.finrank K L : ℂ) with hℓ
  set ρ : ℂ := (((cG' * cT) / (cG * cT') : ℝ) : ℂ) with hρdef
  set c' : ℂ := ((cG' * cT'⁻¹ : ℝ) : ℂ) with hc'
  have hcard : (Ξ.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hΞne).ne'
  have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hκ₀K0 : (κ₀K : ℂ) ≠ 0 := by exact_mod_cast hκ₀K.ne'
  have hκK0 : (κK : ℂ) ≠ 0 := by exact_mod_cast hκK.ne'
  have hρc : ρ = (c₀' : ℂ) := by
    rw [hρdef, hρ]

  have hL : ∀ t ∈ Δφ,
      ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * JL t wq.out
          ∂(HaarQuotient.measure νZL N1 μN) =
        ℓ * ρ * ((C : ℂ) / (Ξ.card : ℂ)) * S (n t) +
          c' * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * Win t wq.out
            ∂(HaarQuotient.measure νZL N1 μN) := by
    intro t ht
    obtain ⟨hbi, hb⟩ := NumberField.sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
      K L νZL νZK N1 hN1c hN1 μN C hC hCl hCi ξL hξc Ξ hΞ (JK (n t)) (hJKm (n t) (hn t ht))
      (fun ξ hξ => hJKi (n t) (hn t ht) ξ hξ) (hJK0 (n t) (hn t ht))
    have hbi' := hbi hΞne

    set P : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ → ℂ := fun wq =>
      ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
        JK (n t) (Nrm (wq.out : (AdeleRing (𝓞 L) L)ˣ)) with hP
    set Q : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ → ℂ := fun wq =>
      ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * Win t wq.out with hQ
    have hPi : Integrable P (HaarQuotient.measure νZL N1 μN) := by rw [hP, hNrm]; exact hbi'
    have hsplit : (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * JL t wq.out) =
        fun wq => (ℓ * ρ) * P wq + c' * Q wq := by
      funext wq
      simp only [hP, hQ]
      rw [hwin t ht]
      ring
    have hJi := hJLi t ht
    rw [hsplit] at hJi
    have hc'0 : c' ≠ 0 := by
      rw [hc']
      have : (cG' * cT'⁻¹ : ℝ) ≠ 0 := mul_ne_zero hcG'.ne' (inv_ne_zero hcT'.ne')
      exact_mod_cast this
    have hQi : Integrable Q (HaarQuotient.measure νZL N1 μN) := by
      have h1 : Integrable (fun wq => c' * Q wq) (HaarQuotient.measure νZL N1 μN) := by
        have := hJi.sub (hPi.const_mul (ℓ * ρ))
        refine this.congr (Filter.Eventually.of_forall fun wq => ?_)
        simp only [Pi.sub_apply]
        ring
      simpa only [← mul_assoc, inv_mul_cancel₀ hc'0, one_mul] using h1.const_mul c'⁻¹
    rw [hsplit, integral_add (hPi.const_mul _) (hQi.const_mul _), integral_const_mul, integral_const_mul]
    have hS' : S (n t) = ((Ξ.card : ℂ) / (C : ℂ)) *
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ, P wq ∂(HaarQuotient.measure νZL N1 μN) := by
      rw [hS, hP, hNrm]; exact hb
    have hPint : ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ, P wq ∂(HaarQuotient.measure νZL N1 μN) =
        ((C : ℂ) / (Ξ.card : ℂ)) * S (n t) := by
      rw [hS']
      field_simp
    rw [hPint]
    ring

  have hR : ∑ ξ ∈ Ξ, ∑ γ ∈ ΔK, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z ∂νZK) =
      ∑ t ∈ Δφ, ((κ₀K : ℂ) * (if ((n t : Matrix (Fin 2) (Fin 2) K) 0 0 / (n t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * S (n t)) := by
    rw [Finset.sum_comm]
    have h1 : ∀ γ ∈ ΔK, ∑ ξ ∈ Ξ, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z ∂νZK) =
        ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * S γ) := by
      intro γ _
      rw [hS, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl h1]
    have himg : Δφ.image n ⊆ ΔK := by
      intro γ hγ
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hγ
      exact hn t ht
    rw [← Finset.sum_subset himg ?_]
    · rw [Finset.sum_image fun t ht t' ht' h => hninj t ht t' ht' h]
    · intro γ hγ hγn
      have hv : S γ = 0 := by
        rw [hS]
        exact hvan γ hγ fun t ht heq => hγn (Finset.mem_image.mpr ⟨t, ht, heq⟩)
      rw [hv, mul_zero, mul_zero]
  rw [hR, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hL t ht, hnr t ht, hρc]
  field_simp

end S_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add
end P2MW
export P2MW.S_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add (solution)
