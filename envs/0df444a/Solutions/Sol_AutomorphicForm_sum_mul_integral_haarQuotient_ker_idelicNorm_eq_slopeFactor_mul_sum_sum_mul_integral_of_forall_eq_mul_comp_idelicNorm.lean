-- Prove2me | solution 1 for AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cc301cbd-5377-54e8-960f-466d91489e93

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Theorems.Thm_NumberField_sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm

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

    (IL : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ) (IK : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIKm : ∀ γ ∈ ΔK, Measurable (IK γ))
    (hIKi : ∀ γ ∈ ΔK, ∀ ξ ∈ Ξ,
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z) νZK)
    (hIK0 : ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm → IK γ z = 0)

    (c₀' : NNReal)
    (hmatch : ∀ t ∈ Δφ, ∀ w : (AdeleRing (𝓞 L) L)ˣ, IL t w = (c₀' : ℂ) * IK (n t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w))
    (hvan : ∀ γ ∈ ΔK, (∀ t ∈ Δφ, n t ≠ γ) →
      ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK = 0)

    (κ₀L κL κ₀K κK : ℝ) (hκ₀K : 0 < κ₀K) (hκK : 0 < κK) :
    ∑ t ∈ Δφ, 2 * ((κ₀L : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
            then (1 / 2 : ℂ) else 1)) *
        (((κL : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * IL t wq.out ∂(HaarQuotient.measure νZL N1 μN)) =
      (((κ₀L : ℂ) * (κL : ℂ) * (C : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * (κK : ℂ) * (Ξ.card : ℂ))) *
        ∑ ξ ∈ Ξ, ∑ γ ∈ ΔK, 2 * ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK) := by

  set Nrm := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hNrm
  set S : GL (Fin 2) K → ℂ := fun γ =>
    ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK with hS
  have hcard : (Ξ.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hΞne).ne'
  have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hκ₀K0 : (κ₀K : ℂ) ≠ 0 := by exact_mod_cast hκ₀K.ne'
  have hκK0 : (κK : ℂ) ≠ 0 := by exact_mod_cast hκK.ne'

  have hL : ∀ t ∈ Δφ,
      ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * IL t wq.out
          ∂(HaarQuotient.measure νZL N1 μN) =
        (c₀' : ℂ) * ((C : ℂ) / (Ξ.card : ℂ)) * S (n t) := by
    intro t ht
    have hb := (NumberField.sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
      K L νZL νZK N1 hN1c hN1 μN C hC hCl hCi ξL hξc Ξ hΞ (IK (n t)) (hIKm (n t) (hn t ht))
      (fun ξ hξ => hIKi (n t) (hn t ht) ξ hξ) (hIK0 (n t) (hn t ht))).2
    have hint : ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * IL t wq.out
          ∂(HaarQuotient.measure νZL N1 μN) =
        (c₀' : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            IK (n t) (Nrm (wq.out : (AdeleRing (𝓞 L) L)ˣ)) ∂(HaarQuotient.measure νZL N1 μN) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun wq => ?_)
      show _ = _
      dsimp only
      rw [hmatch t ht]
      ring
    rw [hint]
    have hS' : S (n t) = ((Ξ.card : ℂ) / (C : ℂ)) *
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            IK (n t) (Nrm (wq.out : (AdeleRing (𝓞 L) L)ˣ)) ∂(HaarQuotient.measure νZL N1 μN) := by
      rw [hS, hNrm]; exact hb
    rw [hS']
    field_simp

  have hR : ∑ ξ ∈ Ξ, ∑ γ ∈ ΔK, 2 * ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK) =
      ∑ t ∈ Δφ, 2 * ((κ₀K : ℂ) * (if ((n t : Matrix (Fin 2) (Fin 2) K) 0 0 / (n t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * S (n t)) := by
    rw [Finset.sum_comm]
    have h1 : ∀ γ ∈ ΔK, ∑ ξ ∈ Ξ, 2 * ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK) =
        2 * ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
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
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hL t ht, hnr t ht]
  field_simp

end S_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm
end P2MW
export P2MW.S_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm (solution)
