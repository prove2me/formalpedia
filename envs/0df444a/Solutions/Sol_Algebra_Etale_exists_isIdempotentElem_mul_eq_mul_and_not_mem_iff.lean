-- Prove2me | solution 1 for Algebra.Etale.exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5b817a8b-d5a0-5ec6-b338-df1d164d0f53

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff

set_option autoImplicit false

open scoped TensorProduct

namespace SepIdempotent

variable {S B C : Type} [CommRing S] [CommRing B] [CommRing C] [Algebra S B] [Algebra S C]

theorem elem_mul_elem [Algebra.FormallyUnramified S B] [Algebra.EssFiniteType S B] :
    Algebra.FormallyUnramified.elem S B * Algebra.FormallyUnramified.elem S B = Algebra.FormallyUnramified.elem S B := by
  set t := Algebra.FormallyUnramified.elem S B with ht
  have h1 : 1 - t ∈ KaehlerDifferential.ideal S B := by
    simp only [KaehlerDifferential.ideal, RingHom.mem_ker, map_sub, map_one]
    rw [sub_eq_zero]
    exact (Algebra.FormallyUnramified.lmul_elem (R := S) (S := B)).symm
  have hkill : ∀ z ∈ KaehlerDifferential.ideal S B, z * t = 0 := by
    intro z hz
    rw [← KaehlerDifferential.span_range_eq_ideal] at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨s, rfl⟩
      exact Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem (R := S) s
    · exact zero_mul _
    · intro a b _ _ ha hb; rw [add_mul, ha, hb, add_zero]
    · intro r a _ ha; rw [smul_eq_mul, mul_assoc, ha, mul_zero]
  have := hkill _ h1
  rw [sub_mul, one_mul, sub_eq_zero] at this
  exact this.symm

end SepIdempotent

theorem solution
    {S B C : Type} [CommRing S] [CommRing B] [CommRing C] [Algebra S B] [Algebra S C] [Algebra.Etale S B]
    (x y : B →ₐ[S] C) :
    ∃ e : C, IsIdempotentElem e ∧ (∀ b : B, e * x b = e * y b) ∧
      (algebraMap C (Localization.Away e)).comp x.toRingHom = (algebraMap C (Localization.Away e)).comp y.toRingHom ∧
      (∀ 𝔭 : Ideal C, 𝔭.IsPrime → (e ∉ 𝔭 ↔ ∀ b : B, x b - y b ∈ 𝔭)) ∧
      (∀ (k : Type) [Field k] (χ : C →+* k), χ.comp x.toRingHom = χ.comp y.toRingHom → χ e = 1) := by
  classical
  haveI : Algebra.FormallyUnramified S B := inferInstance
  haveI : Algebra.EssFiniteType S B := inferInstance
  set t := Algebra.FormallyUnramified.elem S B with ht
  let Φ : B ⊗[S] B →ₐ[S] C := Algebra.TensorProduct.productMap x y

  have hidem : IsIdempotentElem (Φ t) := by
    show Φ t * Φ t = Φ t
    rw [← map_mul, SepIdempotent.elem_mul_elem]

  have hxy : ∀ b : B, Φ t * x b = Φ t * y b := by
    intro b
    have h1 : Φ (t * (b ⊗ₜ[S] (1 : B))) = Φ t * x b := by
      rw [map_mul, Algebra.TensorProduct.productMap_left_apply]
    have h2 : Φ (t * ((1 : B) ⊗ₜ[S] b)) = Φ t * y b := by
      rw [map_mul, Algebra.TensorProduct.productMap_right_apply]
    rw [← h1, ← h2, mul_comm t, mul_comm t, Algebra.FormallyUnramified.one_tmul_mul_elem]

  have hcrit : ∀ 𝔭 : Ideal C, 𝔭.IsPrime → (Φ t ∉ 𝔭 ↔ ∀ b : B, x b - y b ∈ 𝔭) := by
    intro 𝔭 h𝔭
    constructor
    · intro he b
      have h0 : Φ t * (x b - y b) ∈ 𝔭 := by rw [mul_sub, hxy b, sub_self]; exact 𝔭.zero_mem
      rcases h𝔭.mem_or_mem h0 with h | h
      · exact absurd h he
      · exact h
    · intro hb he

      apply h𝔭.ne_top
      rw [Ideal.eq_top_iff_one]
      let q : C →+* C ⧸ 𝔭 := Ideal.Quotient.mk 𝔭
      have hq : ∀ z : B ⊗[S] B, q (Φ z) = q (x (Algebra.TensorProduct.lmul' S z)) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a b =>
          rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul, map_mul,
            map_mul]
          congr 1
          exact (Ideal.Quotient.eq.mpr (hb b)).symm
        | add a b ha hb' => simp only [map_add, ha, hb']
      have h1 : q (Φ t) = 1 := by rw [hq, Algebra.FormallyUnramified.lmul_elem, map_one, map_one]
      have h0 : q (Φ t) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr he
      rw [h0] at h1
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]
      exact h1.symm
  refine ⟨Φ t, hidem, hxy, ?_, hcrit, ?_⟩
  ·
    ext b
    show algebraMap C (Localization.Away (Φ t)) (x b) = algebraMap C (Localization.Away (Φ t)) (y b)
    have hu : IsUnit (algebraMap C (Localization.Away (Φ t)) (Φ t)) := IsLocalization.Away.algebraMap_isUnit (Φ t)
    apply hu.mul_left_cancel
    rw [← map_mul, ← map_mul, hxy b]
  ·
    intro k _ χ hχ
    have hker : ∀ b : B, x b - y b ∈ RingHom.ker χ := by
      intro b
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact congrArg (fun f : B →+* k => f b) hχ
    have hne : Φ t ∉ RingHom.ker χ := (hcrit _ (RingHom.ker_isPrime χ)).mpr hker
    rw [RingHom.mem_ker] at hne
    have hid : IsIdempotentElem (χ (Φ t)) := hidem.map χ
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hid with h | h
    · exact absurd h hne
    · exact h

end S_Algebra_Etale_exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff
end P2MW
export P2MW.S_Algebra_Etale_exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff (solution)
