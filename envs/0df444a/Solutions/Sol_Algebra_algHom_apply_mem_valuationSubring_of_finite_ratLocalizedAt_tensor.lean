-- Prove2me | solution 1 for Algebra.algHom_apply_mem_valuationSubring_of_finite_ratLocalizedAt_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/60b06235-0fae-545c-b3f7-15122eb5bef4

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_algHom_apply_mem_valuationSubring_of_finite_ratLocalizedAt_tensor
open scoped TensorProduct

set_option autoImplicit false

section secT

open TensorProduct

namespace G1Engine

section T1

variable (H : Type*) [CommRing H] (ℓ : ℕ)

noncomputable def muT (h : H) :
    TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H →ₗ[↥(GaloisRep.ratLocalizedAt ℓ)]
      TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H :=
  LinearMap.baseChange ↥(GaloisRep.ratLocalizedAt ℓ) (LinearMap.mulLeft ℤ h)

theorem muT_tmul (h : H) (c : ↥(GaloisRep.ratLocalizedAt ℓ)) (x : H) :
    muT H ℓ h (c ⊗ₜ[ℤ] x) = c ⊗ₜ[ℤ] (h * x) := by
  simp [muT, LinearMap.baseChange_tmul, LinearMap.mulLeft_apply]

theorem muT_pow_tmul (h : H) (i : ℕ) (x : H) :
    ((muT H ℓ h) ^ i) ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] x)
      = (1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (h ^ i * x) := by
  induction i generalizing x with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, one_mul]
  | succ i ih =>
    rw [pow_succ, Module.End.mul_apply, muT_tmul, ih (h * x), pow_succ, mul_assoc]

theorem muT_pow_one_tmul_one (h : H) (i : ℕ) :
    ((muT H ℓ h) ^ i) ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (1 : H))
      = (1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (h ^ i) := by
  rw [muT_pow_tmul, mul_one]

end T1

section T23

theorem ratArith (c : ℚ) (d : ℕ) (hdvd : c.den ∣ d) :
    (d : ℚ) * c = ((((d / c.den : ℕ) : ℤ) * c.num : ℤ) : ℚ) := by
  obtain ⟨k, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left k c.den_pos]
  push_cast
  rw [mul_comm (c.den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]

variable (H : Type*) [CommRing H] (ℓ : ℕ)

theorem exists_intRel
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H))
    (hℓ : ℓ.Prime) (h : H) :
    ∃ (n : ℕ) (a : ℕ → ℤ), ¬((ℓ : ℤ) ∣ a n) ∧
      (1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ]
          (∑ i ∈ Finset.range (n + 1), a i • h ^ i)
        = (0 : TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H) := by
  haveI := hfin
  obtain ⟨f, hmon, hf0⟩ :=
    LinearMap.exists_monic_and_aeval_eq_zero (R := ↥(GaloisRep.ratLocalizedAt ℓ))
      (f := muT H ℓ h)
  set n := f.natDegree with hn

  have h1 := congrArg
    (fun g : Module.End ↥(GaloisRep.ratLocalizedAt ℓ)
        (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H) =>
      g ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (1 : H))) hf0
  rw [Polynomial.aeval_eq_sum_range] at h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at h1
  have hsum : ∑ i ∈ Finset.range (n + 1),
      f.coeff i • ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (h ^ i)) = 0 := by
    calc ∑ i ∈ Finset.range (n + 1),
        f.coeff i • ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (h ^ i))
        = ∑ i ∈ Finset.range (n + 1), f.coeff i •
            (((muT H ℓ h) ^ i)
              ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (1 : H))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [muT_pow_one_tmul_one]
      _ = 0 := h1

  set d : ℕ := ∏ j ∈ Finset.range (n + 1), ((f.coeff j : ℚ)).den with hd
  have hcop : Nat.Coprime ℓ d :=
    Nat.Coprime.prod_right fun j _ => ((f.coeff j).2).symm
  set a : ℕ → ℤ := fun i => ((d / ((f.coeff i : ℚ)).den : ℕ) : ℤ) * ((f.coeff i : ℚ)).num
    with ha
  refine ⟨n, a, ?_, ?_⟩
  ·
    have hc1 : f.coeff n = 1 := hmon.coeff_natDegree
    have han : a n = (d : ℤ) := by
      rw [ha]; simp [hc1]
    rw [han, Int.natCast_dvd_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).mp hcop
  ·
    have key : ∀ i ∈ Finset.range (n + 1),
        (d : ↥(GaloisRep.ratLocalizedAt ℓ)) •
            (f.coeff i • ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (h ^ i)))
          = (1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (a i • h ^ i) := by
      intro i hi
      have hdvd : ((f.coeff i : ℚ)).den ∣ d := Finset.dvd_prod_of_mem _ hi
      have hdc : (d : ↥(GaloisRep.ratLocalizedAt ℓ)) * f.coeff i
          = ((a i : ℤ) : ↥(GaloisRep.ratLocalizedAt ℓ)) := by
        apply Subtype.ext
        rw [Subring.coe_mul, SubringClass.coe_natCast, SubringClass.coe_intCast]
        simp only [ha]
        exact ratArith (f.coeff i : ℚ) d hdvd
      rw [smul_smul, hdc, smul_tmul', smul_eq_mul, mul_one, ← zsmul_one (a i), smul_tmul]
    have hd0 : ∑ i ∈ Finset.range (n + 1),
        (1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (a i • h ^ i) = 0 := by
      calc ∑ i ∈ Finset.range (n + 1),
          (1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (a i • h ^ i)
          = ∑ i ∈ Finset.range (n + 1),
              (d : ↥(GaloisRep.ratLocalizedAt ℓ)) •
                (f.coeff i • ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (h ^ i))) := by
            refine Finset.sum_congr rfl fun i hi => (key i hi).symm
        _ = (d : ↥(GaloisRep.ratLocalizedAt ℓ)) • ∑ i ∈ Finset.range (n + 1),
              f.coeff i • ((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (h ^ i)) :=
            (Finset.smul_sum).symm
        _ = (d : ↥(GaloisRep.ratLocalizedAt ℓ)) •
              (0 : TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H) := by rw [hsum]
        _ = 0 := smul_zero _
    rw [← TensorProduct.tmul_sum] at hd0
    exact hd0

end T23

end G1Engine

end secT

namespace G1Engine

section secV

open ValuationSubring Finset IsLocalRing

variable {L : Type*} [Field L]

theorem rel_rearranged {x : L} (hx : x ≠ 0) {n : ℕ} {a : ℕ → ℤ}
    (hroot : ∑ i ∈ range (n + 1), (a i : L) * x ^ i = 0) :
    (a n : L) = -∑ i ∈ range n, (a i : L) * x⁻¹ ^ (n - i) := by
  have hxn : x ^ n ≠ 0 := pow_ne_zero n hx

  have hroot' : (∑ i ∈ range (n + 1), (a i : L) * x ^ i) * (x⁻¹) ^ n = 0 := by
    rw [hroot, zero_mul]
  rw [sum_mul] at hroot'

  rw [sum_range_succ] at hroot'
  have htop : (a n : L) * x ^ n * x⁻¹ ^ n = (a n : L) := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, mul_one]
  rw [htop] at hroot'

  have htail : ∀ i ∈ range n, (a i : L) * x ^ i * x⁻¹ ^ n = (a i : L) * x⁻¹ ^ (n - i) := by
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt (mem_range.mp hi)
    rw [mul_assoc]
    congr 1
    have h1 : x⁻¹ ^ n = x⁻¹ ^ i * x⁻¹ ^ (n - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hin]
    rw [h1, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, one_mul]
  rw [sum_congr rfl htail] at hroot'
  linear_combination hroot'

theorem mem_of_intPoly_root {B : ValuationSubring L} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hB : B.LiesOverPrime ℓ) {x : L} {n : ℕ} {a : ℕ → ℤ}
    (htop : ¬(ℓ : ℤ) ∣ a n)
    (hroot : ∑ i ∈ range (n + 1), (a i : L) * x ^ i = 0) : x ∈ B := by

  rcases eq_or_ne x 0 with hx0 | hx
  · exact hx0 ▸ B.zero_mem

  by_contra hxB
  have hyB : x⁻¹ ∈ B := (B.mem_or_inv_mem x).resolve_left hxB
  set y : ↥B := ⟨x⁻¹, hyB⟩ with hy_def
  have hy_nonunit : ¬IsUnit y := fun hu => hxB <| by
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    have h1 : x⁻¹ * (z : L) = 1 := by
      have h0 := congrArg (Subtype.val : ↥B → L) hz
      push_cast at h0
      exact h0
    have h2 : (z : L) = x := by
      have h3 : x * (x⁻¹ * (z : L)) = x * 1 := by rw [h1]
      rwa [← mul_assoc, mul_inv_cancel₀ hx, one_mul, mul_one] at h3
    exact h2 ▸ z.2

  have hy_max : y ∈ maximalIdeal ↥B := (IsLocalRing.mem_maximalIdeal y).mpr hy_nonunit

  have hrel := rel_rearranged hx hroot

  have hlift : ((a n : ℤ) : ↥B)
      = -∑ i ∈ range n, ((a i : ℤ) : ↥B) * y ^ (n - i) := by
    apply Subtype.ext
    push_cast
    simp only [hy_def]
    exact hrel

  have hmem : ((a n : ℤ) : ↥B) ∈ maximalIdeal ↥B := by
    rw [hlift]
    refine neg_mem (Ideal.sum_mem _ fun i hi => ?_)
    have hni : 1 ≤ n - i := Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_of_lt (mem_range.mp hi))
    rw [show n - i = (n - i - 1) + 1 from (Nat.sub_add_cancel hni).symm, pow_succ]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hy_max)

  have hunit : IsUnit ((a n : ℤ) : ↥B) := intCast_isUnit_of_not_dvd hℓ hB htop
  exact absurd hmem ((IsLocalRing.mem_maximalIdeal _).not.mpr (not_not.mpr hunit))

end secV

end G1Engine

namespace G1Engine

open TensorProduct

theorem sum_intCast_mul_pow_eq_zero_of_one_tmul {L : Type*} [Field L] [CharZero L]
    (H : Type*) [CommRing H] (ℓ : ℕ) (ψ : H →+* L) (h : H) (n : ℕ) (a : ℕ → ℤ)
    (hrel : (1 : ↥(GaloisRep.ratLocalizedAt ℓ)) ⊗ₜ[ℤ] (∑ i ∈ Finset.range (n + 1), a i • h ^ i)
      = (0 : TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H)) :
    ∑ i ∈ Finset.range (n + 1), (a i : L) * ψ h ^ i = 0 := by
  let β : ↥(GaloisRep.ratLocalizedAt ℓ) →ₗ[ℤ] H →ₗ[ℤ] L :=
    LinearMap.mk₂ ℤ (fun c x => ((c : ℚ) : L) * ψ x)
      (fun c₁ c₂ x => by push_cast; ring)
      (fun r c x => by simp only [zsmul_eq_mul]; push_cast; ring)
      (fun c x₁ x₂ => by simp only [map_add, mul_add])
      (fun r c x => by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring)
  have hΦ := congrArg (TensorProduct.lift β) hrel
  rw [TensorProduct.lift.tmul, map_zero] at hΦ
  have hβ : β 1 (∑ i ∈ Finset.range (n + 1), a i • h ^ i)
      = ∑ i ∈ Finset.range (n + 1), (a i : L) * ψ h ^ i := by
    show (((1 : ↥(GaloisRep.ratLocalizedAt ℓ)) : ℚ) : L) * ψ (∑ i ∈ Finset.range (n + 1), a i • h ^ i) = _
    rw [OneMemClass.coe_one, Rat.cast_one, one_mul, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, zsmul_eq_mul, map_pow]
  rw [hβ] at hΦ
  exact hΦ

theorem core (H : Type*) [CommRing H] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H))
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime ℓ)
    (ψ : H →+* AlgebraicClosure ℚ) (h : H) : ψ h ∈ B := by
  obtain ⟨n, a, han, hrel⟩ := exists_intRel H ℓ hfin hℓ h
  exact mem_of_intPoly_root hℓ hB han (sum_intCast_mul_pow_eq_zero_of_one_tmul H ℓ ψ h n a hrel)

end G1Engine

theorem solution
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (H : Type) [CommRing H] [Algebra ℤ H]
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) H))
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime ℓ)
    (ψ : H →ₐ[ℤ] AlgebraicClosure ℚ) (h : H) : ψ h ∈ B :=
  G1Engine.core H ℓ hℓ hfin B hB (ψ : H →+* AlgebraicClosure ℚ) h

end S_Algebra_algHom_apply_mem_valuationSubring_of_finite_ratLocalizedAt_tensor
end P2MW
export P2MW.S_Algebra_algHom_apply_mem_valuationSubring_of_finite_ratLocalizedAt_tensor (solution)
