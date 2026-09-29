-- Prove2me | solution 1 for AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1b84dd86-b538-58a0-95d4-57b634316336

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.CharP.Lemmas
import Theorems.Thm_NumberField_subgroup_eq_top_of_forall_inertia_le
import Theorems.Thm_NumberField_exists_lift_mem_inertia_integralClosure
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le

open scoped Pointwise NumberField

theorem solution (H : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))) (hopen : IsOpen (H : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))) (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → A.inertiaSubgroupIn ℚ ≤ H) : H = ⊤ := by
  classical

  haveI hnorm : Normal ℚ (AlgebraicClosure ℚ) := by
    have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      inferInstance
    exact h

  obtain ⟨L, hLfin, hLnorm, hLH'⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ (AlgebraicClosure ℚ) _).mp (hopen.mem_nhds H.one_mem)
  haveI := hLfin
  haveI := hLnorm
  haveI : IsGalois ℚ L := @IsGalois.mk ℚ _ L _ _ inferInstance hLnorm
  have hLH : L.fixingSubgroup ≤ H := fun σ hσ => hLH' hσ

  let res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L
  haveI : NumberField L := NumberField.mk
  have htop : H.map res = ⊤ := by
    apply NumberField.subgroup_eq_top_of_forall_inertia_le
    intro Q hQ τ hτ
    haveI := hQ

    obtain ⟨q, hqchar⟩ := CharP.exists (𝓞 L ⧸ Q)
    haveI := hqchar
    haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q
      (Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField L))
    letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
    have hqprime : q.Prime := CharP.char_is_prime (𝓞 L ⧸ Q) q
    have hqQ : (q : 𝓞 L) ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact CharP.cast_eq_zero (𝓞 L ⧸ Q) q
    obtain ⟨σ, hστ, 𝔔, h𝔔max, hq𝔔, hσ𝔔⟩ :=
      NumberField.exists_lift_mem_inertia_integralClosure L Q hqQ τ hτ
    haveI := h𝔔max
    obtain ⟨A, hA, hσA⟩ :=
      ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn 𝔔 hqprime hq𝔔 σ hσ𝔔
    exact ⟨σ, hunr q hqprime A hA hσA, hστ⟩

  rw [Subgroup.eq_top_iff']
  intro σ
  have hmem : res σ ∈ H.map res := htop ▸ Subgroup.mem_top _
  obtain ⟨h, hh, hres⟩ := hmem
  have hker : h⁻¹ * σ ∈ L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv]
    change (res h)⁻¹ * res σ = 1
    rw [hres, inv_mul_cancel]
  have : h * (h⁻¹ * σ) ∈ H := H.mul_mem hh (hLH hker)
  simpa using this

end S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le
end P2MW
export P2MW.S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le (solution)
