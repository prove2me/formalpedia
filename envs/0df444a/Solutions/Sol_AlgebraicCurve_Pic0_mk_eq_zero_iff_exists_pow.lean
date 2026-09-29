-- Prove2me | solution 1 for AlgebraicCurve.Pic0.mk_eq_zero_iff_exists_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6db69f31-da06-509c-b5f9-5934846abcd4

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_mk_eq_zero_iff_exists_pow
set_option Elab.async false

set_option autoImplicit false

open AlgebraicCurve

private theorem ord_algebraMap_aux {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
    have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
    have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
      rw [← map_inv₀]; exact v.algebraMap_mem' c⁻¹
    let u : v.toValuationSubringˣ :=
      ⟨⟨_, hmem⟩, ⟨_, hmem'⟩,
        Subtype.ext (mul_inv_cancel₀ hc'),
        Subtype.ext (inv_mul_cancel₀ hc')⟩
    exact v.ord_coe_unit u
private theorem mk_eq_zero_iff_aux {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by
  rw [show Pic0.mk D = QuotientAddGroup.mk D from rfl, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]
private theorem ord_pow_aux {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (h : F) (n : ℕ) : v.ord (h ^ n) = n * v.ord h := by
  rw [← zpow_natCast]; exact v.ord_zpow h n
private theorem mk_eq_zero_of_eq_algebraMap_mul_pow {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0)
    {D : Divisor.degZero (K := K) (F := F)}
    (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) (c : K) (h : F)
    (hfch : f = algebraMap K F c * h ^ n) : Pic0.mk D = 0 := by
  have hne : algebraMap K F c ≠ 0 ∧ h ^ n ≠ 0 := mul_ne_zero_iff.mp (hfch ▸ hf)
  have hh : h ≠ 0 := fun h0 => hne.2 (by rw [h0]; exact zero_pow hn)
  rw [mk_eq_zero_iff_aux]
  refine ⟨h, hh, fun v => ?_⟩
  have h1 : v.ord f = n * v.ord h := by
    rw [hfch, v.ord_mul hne.1 hne.2, ord_algebraMap_aux, zero_add, ord_pow_aux]
  have h2 : (n : ℤ) * (D : Divisor K F) v = n * v.ord h := (hfD v).symm.trans h1
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) h2
private theorem exists_algebraMap_mul_pow_of_mk_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → u ∈ (algebraMap K F).range)
    {n : ℕ} {f : F} (hf : f ≠ 0) {D : Divisor.degZero (K := K) (F := F)}
    (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) (hD : Pic0.mk D = 0) :
    ∃ c : K, c ≠ 0 ∧ ∃ h : F, h ≠ 0 ∧ f = algebraMap K F c * h ^ n := by
  rw [mk_eq_zero_iff_aux] at hD
  obtain ⟨h, hh, hDh⟩ := hD
  have hhn : h ^ n ≠ 0 := pow_ne_zero n hh
  have hu0 : f * (h ^ n)⁻¹ ≠ 0 := mul_ne_zero hf (inv_ne_zero hhn)
  have hu : ∀ v : Place K F, v.ord (f * (h ^ n)⁻¹) = 0 := fun v => by
    rw [v.ord_mul hf (inv_ne_zero hhn), v.ord_inv, ord_pow_aux, ← hDh v, hfD v]; ring
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (hconst _ hu0 hu)
  refine ⟨c, ?_, h, hh, ?_⟩
  · rintro rfl
    rw [map_zero] at hc
    exact hu0 hc.symm
  · rw [hc, inv_mul_cancel_right₀ hhn]
private theorem mk_eq_zero_of_eq_pow {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0)
    {D : Divisor.degZero (K := K) (F := F)}
    (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) (h : F) (hfh : f = h ^ n) :
    Pic0.mk D = 0 :=
  mk_eq_zero_of_eq_algebraMap_mul_pow hn hf hfD 1 h (by rw [map_one, one_mul]; exact hfh)
private theorem exists_pow_of_mk_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → u ∈ (algebraMap K F).range)
    {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0) {D : Divisor.degZero (K := K) (F := F)}
    (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) (hD : Pic0.mk D = 0) :
    ∃ h : F, h ≠ 0 ∧ f = h ^ n := by
  obtain ⟨c, hc, h, hh, hfch⟩ := exists_algebraMap_mul_pow_of_mk_eq_zero hconst hf hfD hD
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hn)
  refine ⟨algebraMap K F d * h, mul_ne_zero ?_ hh, ?_⟩
  · refine (map_ne_zero _).mpr (fun h0 => hc ?_)
    rw [← hd, h0, zero_pow hn]
  · rw [mul_pow, ← map_pow, hd, hfch]
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → u ∈ (algebraMap K F).range)
    {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0) {D : Divisor.degZero (K := K) (F := F)}
    (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) :
    Pic0.mk D = 0 ↔ ∃ h : F, h ≠ 0 ∧ f = h ^ n :=
  ⟨exists_pow_of_mk_eq_zero hconst hn hf hfD,
    fun ⟨h, _, hfh⟩ => mk_eq_zero_of_eq_pow hn hf hfD h hfh⟩

#print axioms solution

end S_AlgebraicCurve_Pic0_mk_eq_zero_iff_exists_pow
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_mk_eq_zero_iff_exists_pow (solution)
