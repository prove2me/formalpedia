-- Prove2me | solution 1 for AutomorphicForm.exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e89dafe9-9dec-5e10-9e09-939397d6abd2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace P2mSemiLocalUniformizer

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

abbrev F : Type := v.adicCompletion K

abbrev Rv : Type := L ⊗[K] v.adicCompletion K

abbrev bc : Rv K L v ≃ₐ[L] Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

theorem bc_apply (x : Rv K L v) : bc K L v x = HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v x := rfl

theorem mem_semiLocalIntegers_iff (x : Rv K L v) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ w : v.Extension (𝓞 L), bc K L v x w ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  rfl

theorem bc_one_tmul (c : F K v) (w : v.Extension (𝓞 L)) :
    bc K L v ((1 : L) ⊗ₜ[K] c) w = algebraMap (F K v) (w.1.adicCompletion L) c := by
  rw [bc_apply, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]

variable {K L v}

section Local

variable (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
  (ϖ : K) (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ))

abbrev ϖw (ϖ : K) (w : v.Extension (𝓞 L)) : w.1.adicCompletion L :=
  algebraMap (F K v) (w.1.adicCompletion L) (ϖ : F K v)

include hv hϖ

theorem valued_ϖw (w : v.Extension (𝓞 L)) : Valued.v (ϖw ϖ w) = WithZero.exp (-1 : ℤ) := by
  change Valued.v (HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w (ϖ : F K v)) = _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom, hv w.1 w.2, pow_one,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ]

theorem ϖw_ne_zero (w : v.Extension (𝓞 L)) : ϖw ϖ w ≠ 0 := by
  intro h
  have := valued_ϖw hv ϖ hϖ w
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

omit hv hϖ in

theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : γ = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem exists_eq_mul_of_lt_one (w : v.Extension (𝓞 L)) {x : w.1.adicCompletion L} (hx : Valued.v x < 1) :
    ∃ y : w.1.adicCompletion L, Valued.v y ≤ 1 ∧ x = ϖw ϖ w * y := by
  refine ⟨(ϖw ϖ w)⁻¹ * x, ?_, by rw [mul_inv_cancel_left₀ (ϖw_ne_zero hv ϖ hϖ w)]⟩
  rw [map_mul, map_inv₀, valued_ϖw hv ϖ hϖ w]
  have hx' := le_exp_neg_one_of_lt_one hx
  calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v x ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) :=
        mul_le_mul_right hx' _
    _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero

theorem exists_mul_eq_one_of_one_lt (w : v.Extension (𝓞 L)) {x : w.1.adicCompletion L} (hx : 1 < Valued.v x) :
    ∃ y : w.1.adicCompletion L, Valued.v y ≤ 1 ∧ ϖw ϖ w * x * y = 1 := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact not_lt_of_ge zero_le' hx
  have hinv : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
  obtain ⟨y, hy, hxy⟩ := exists_eq_mul_of_lt_one hv ϖ hϖ w hinv
  refine ⟨y, hy, ?_⟩
  rw [mul_assoc, mul_left_comm, ← hxy, mul_inv_cancel₀ hx0]

end Local

theorem part_one
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ϖ : K) (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ))
    (x : Rv K L v) (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v)
    (y : Rv K L v) (hy : y ∈ AutomorphicForm.semiLocalIntegers K L v)
    (h : x * x = ((1 : L) ⊗ₜ[K] (ϖ : F K v)) * y) :
    ∃ z ∈ AutomorphicForm.semiLocalIntegers K L v, x = ((1 : L) ⊗ₜ[K] (ϖ : F K v)) * z := by
  rw [mem_semiLocalIntegers_iff] at hx hy
  have hcomp : ∀ w : v.Extension (𝓞 L), ∃ zw : w.1.adicCompletion L, Valued.v zw ≤ 1 ∧ bc K L v x w = ϖw ϖ w * zw := by
    intro w
    refine exists_eq_mul_of_lt_one hv ϖ hϖ w ?_
    have hsq : bc K L v x w * bc K L v x w = ϖw ϖ w * bc K L v y w := by
      rw [← Pi.mul_apply, ← map_mul, h, map_mul, Pi.mul_apply, bc_one_tmul]
    have hle : Valued.v (bc K L v x w * bc K L v x w) ≤ WithZero.exp (-1 : ℤ) := by
      rw [hsq, map_mul, valued_ϖw hv ϖ hϖ w]
      have hyw : Valued.v (bc K L v y w) ≤ 1 := hy w
      calc WithZero.exp (-1 : ℤ) * Valued.v (bc K L v y w) ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul_right hyw _
        _ = WithZero.exp (-1 : ℤ) := mul_one _
    by_contra hge
    push Not at hge
    have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v (bc K L v x w * bc K L v x w) := by
      rw [map_mul]; exact one_le_mul hge hge
    have h2 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-1 : ℤ) := h1.trans hle
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    omega
  choose zw hzw1 hzw using hcomp
  refine ⟨(bc K L v).symm zw, ?_, ?_⟩
  · rw [mem_semiLocalIntegers_iff]
    intro w
    rw [AlgEquiv.apply_symm_apply]
    exact hzw1 w
  · apply (bc K L v).injective
    funext w
    rw [map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply, bc_one_tmul, hzw w]

theorem part_two
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ϖ : K) (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ))
    (x : Rv K L v) (hx : x ∉ AutomorphicForm.semiLocalIntegers K L v) :
    ∃ y ∈ AutomorphicForm.semiLocalIntegers K L v, ∃ e ∈ AutomorphicForm.semiLocalIntegers K L v,
      e ≠ 0 ∧ IsIdempotentElem e ∧ ((1 : L) ⊗ₜ[K] (ϖ : F K v)) * x * y = e := by
  classical
  rw [mem_semiLocalIntegers_iff, not_forall] at hx
  obtain ⟨w, hw⟩ := hx
  have hw' : 1 < Valued.v (bc K L v x w) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hw
    exact hw
  obtain ⟨yw, hyw1, hyw⟩ := exists_mul_eq_one_of_one_lt hv ϖ hϖ w hw'
  refine ⟨(bc K L v).symm (Pi.single w yw), ?_, (bc K L v).symm (Pi.single w 1), ?_, ?_, ?_, ?_⟩
  · rw [mem_semiLocalIntegers_iff]
    intro w'
    rw [AlgEquiv.apply_symm_apply]
    by_cases hww : w' = w
    · subst hww; rw [Pi.single_eq_same]; exact hyw1
    · rw [Pi.single_eq_of_ne hww]; exact zero_mem _
  · rw [mem_semiLocalIntegers_iff]
    intro w'
    rw [AlgEquiv.apply_symm_apply]
    by_cases hww : w' = w
    · subst hww; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hww]; exact zero_mem _
  · intro h
    have := congrArg (fun z => bc K L v z w) h
    simp only [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_zero, Pi.zero_apply] at this
    exact one_ne_zero this
  · change (bc K L v).symm (Pi.single w 1) * (bc K L v).symm (Pi.single w 1) = (bc K L v).symm (Pi.single w 1)
    rw [← map_mul, ← Pi.single_mul, mul_one]
  · apply (bc K L v).injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext w'
    rw [Pi.mul_apply, Pi.mul_apply, bc_one_tmul]
    by_cases hww : w' = w
    · subst hww
      rw [Pi.single_eq_same, Pi.single_eq_same]
      exact hyw
    · rw [Pi.single_eq_of_ne hww, Pi.single_eq_of_ne hww, mul_zero]

end P2mSemiLocalUniformizer

end

open NumberField IsDedekindDomain in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ϖ : K) (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) :
    (∀ x ∈ AutomorphicForm.semiLocalIntegers K L v, ∀ y ∈ AutomorphicForm.semiLocalIntegers K L v,
        x * x = ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * y →
        ∃ z ∈ AutomorphicForm.semiLocalIntegers K L v,
          x = ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * z) ∧
    (∀ x : L ⊗[K] v.adicCompletion K, x ∉ AutomorphicForm.semiLocalIntegers K L v →
        ∃ y ∈ AutomorphicForm.semiLocalIntegers K L v, ∃ e ∈ AutomorphicForm.semiLocalIntegers K L v,
          e ≠ 0 ∧ IsIdempotentElem e ∧
            ((1 : L) ⊗ₜ[K] (ϖ : v.adicCompletion K)) * x * y = e) :=
  ⟨fun x hx y hy h => P2mSemiLocalUniformizer.part_one hv ϖ hϖ x hx y hy h,
    fun x hx => P2mSemiLocalUniformizer.part_two hv ϖ hϖ x hx⟩

end S_AutomorphicForm_exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
end P2MW
export P2MW.S_AutomorphicForm_exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers (solution)
