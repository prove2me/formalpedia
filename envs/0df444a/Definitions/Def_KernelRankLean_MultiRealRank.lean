-- Prove2me | Definitions.Def_KernelRankLean_MultiRealRank
-- name    : KernelRankLean_MultiRealRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T02:12:52.908541+00:00
-- url     : https://prove2.me/theorems/7d4a9970-2520-4687-9557-c0df69d351f7
-- title:
--   Multi Real Rank
-- statement:
--   Definitions and structural lemmas for Multi Real Rank, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Theorems.Thm_KernelRank_IsSumOfProducts_finsetSum
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same


set_option autoImplicit true
open Complex Polynomial NNReal
namespace KernelRank
theorem re_prod_eq_sum_re {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℂ) :
    (∏ j, z j).re = (2 : ℝ) ^ (d - 1) / d *
      ∑ m : Fin d, (-1 : ℝ) ^ (m : ℕ) *
        ∏ j : Fin d, (z j * exp (-Real.pi * I * (m : ℕ) / d)).re := by
  have hd_pos : 0 < d := hd
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  apply Complex.ofReal_inj.mp
  push_cast
  have hre (w : ℂ) : (w.re : ℂ) = (starRingEnd ℂ w + w) / 2 := by
    rw [Complex.re_eq_add_conj]
    ring
  simp_rw [hre]
  have hconj_rot (j : Fin d) (m : ℕ) :
      starRingEnd ℂ (z j * exp (-Real.pi * I * m / d)) =
        starRingEnd ℂ (z j) * exp (Real.pi * I * m / d) := by
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp [div_eq_mul_inv]
  have hprod_div (m : Fin d) :
      (∏ j : Fin d,
        (starRingEnd ℂ (z j * exp (-Real.pi * I * (m : ℕ) / d)) +
          z j * exp (-Real.pi * I * (m : ℕ) / d)) / 2) =
      ((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ((∏ j ∈ S, starRingEnd ℂ (z j)) * ∏ j ∈ Finset.univ \ S, z j) *
            (exp (Real.pi * I * (m : ℕ) / d) ^ S.card *
              exp (-Real.pi * I * (m : ℕ) / d) ^ (d - S.card)) := by
    simp_rw [hconj_rot, div_eq_mul_inv]
    rw [Finset.prod_mul_distrib]
    have h2 : (∏ _j : Fin d, (2 : ℂ)⁻¹) = ((2 : ℂ) ^ d)⁻¹ := by simp
    rw [h2, mul_comm _ (((2 : ℂ) ^ d)⁻¹)]
    congr 1
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hsub : S ⊆ Finset.univ := Finset.mem_powerset.mp hS
    have hcard : (Finset.univ \ S).card = d - S.card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      hcard]
    ring
  simp_rw [hprod_div]
  let Z (S : Finset (Fin d)) : ℂ :=
    (∏ j ∈ S, starRingEnd ℂ (z j)) * ∏ j ∈ Finset.univ \ S, z j
  change _ = (2 : ℂ) ^ (d - 1) / d *
    ∑ m : Fin d, (-1 : ℂ) ^ (m : ℕ) * (((2 : ℂ) ^ d)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
        (exp (Real.pi * I * (m : ℕ) / d) ^ S.card *
          exp (-Real.pi * I * (m : ℕ) / d) ^ (d - S.card)))
  have hpull : ∑ m : Fin d,
      (-1 : ℂ) ^ (m : ℕ) * (((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
          (exp (Real.pi * I * (m : ℕ) / d) ^ S.card *
            exp (-Real.pi * I * (m : ℕ) / d) ^ (d - S.card))) =
      ((2 : ℂ) ^ d)⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
        ∑ m ∈ Finset.range d,
          (-1 : ℂ) ^ m * (exp (Real.pi * I * m / d) ^ S.card *
            exp (-Real.pi * I * m / d) ^ (d - S.card)) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun m : ℕ => (-1 : ℂ) ^ m * (((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
          (exp (Real.pi * I * m / d) ^ S.card *
            exp (-Real.pi * I * m / d) ^ (d - S.card)))) d]
    simp_rw [← mul_assoc ((-1 : ℂ) ^ _) (((2 : ℂ) ^ d)⁻¹),
      mul_comm ((-1 : ℂ) ^ _) (((2 : ℂ) ^ d)⁻¹), mul_assoc (((2 : ℂ) ^ d)⁻¹), ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun m _ => by ring
  rw [hpull]
  have hinner (S : Finset (Fin d)) (hS : S ∈ (Finset.univ : Finset (Fin d)).powerset) :
      (∑ m ∈ Finset.range d,
        (-1 : ℂ) ^ m * (exp (Real.pi * I * m / d) ^ S.card *
          exp (-Real.pi * I * m / d) ^ (d - S.card))) =
        if S = ∅ ∨ S = Finset.univ then (d : ℂ) else 0 := by
    have hcard_le : S.card ≤ d := by
      simpa using Finset.card_le_univ S
    let w : ℂ := exp (2 * Real.pi * I * S.card / d)
    have hterm (m : ℕ) :
        (-1 : ℂ) ^ m * (exp (Real.pi * I * m / d) ^ S.card *
          exp (-Real.pi * I * m / d) ^ (d - S.card)) = w ^ m := by
      have hm1 : (-1 : ℂ) ^ m = exp (Real.pi * I * m) := by
        rw [mul_comm (Real.pi * I) (m : ℂ), exp_nat_mul, exp_pi_mul_I]
      rw [hm1, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add, ← exp_nat_mul]
      congr 1
      have hsub_cast : ((d - S.card : ℕ) : ℂ) = (d : ℂ) - (S.card : ℂ) :=
        Nat.cast_sub hcard_le
      rw [hsub_cast]
      field_simp
      ring
    simp_rw [hterm]
    split_ifs with hSu
    · rcases hSu with rfl | rfl
      · simp [w]
      · have hw1 : w = 1 := by
          simp only [w, Finset.card_univ, Fintype.card_fin]
          have : 2 * Real.pi * I * (d : ℂ) / (d : ℂ) = 2 * Real.pi * I := by field_simp
          rw [this, exp_two_pi_mul_I]
        simp [hw1]
    · push Not at hSu
      have hpos_S : 0 < S.card := Finset.card_pos.mpr hSu.1
      have hlt_S : S.card < d := by
        have hssub : S ⊂ Finset.univ := (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_univ S, hSu.2⟩)
        simpa using Finset.card_lt_card hssub
      have hwd : w ^ d = 1 := by
        rw [← exp_nat_mul]
        have hexp : (d : ℂ) * (2 * Real.pi * I * S.card / d) =
            (S.card : ℂ) * (2 * Real.pi * I) := by field_simp
        rw [hexp, exp_nat_mul_two_pi_mul_I]
      have hw1 : w ≠ 1 := by
        intro h1
        rw [exp_eq_one_iff] at h1
        obtain ⟨m, hm⟩ := h1
        have hpi : (2 : ℂ) * Real.pi * I ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            I_ne_zero
        have heq : (S.card : ℂ) = (m : ℂ) * d := by
          apply mul_right_cancel₀ hpi
          have hm' : 2 * Real.pi * I * (S.card : ℂ) = (m : ℂ) * (2 * Real.pi * I) * d :=
            (div_eq_iff hd0).mp hm
          linear_combination hm'
        have hz : (S.card : ℤ) = m * d := by exact_mod_cast heq
        rcases le_or_gt m 0 with hm_le | hm_pos
        · have : m * (d : ℤ) ≤ 0 :=
            Int.mul_nonpos_of_nonpos_of_nonneg hm_le (Int.natCast_nonneg d)
          omega
        · have hm1 : 1 ≤ m := by omega
          have : 1 * (d : ℤ) ≤ m * (d : ℤ) :=
            Int.mul_le_mul_of_nonneg_right hm1 (Int.natCast_nonneg d)
          omega
      have hgeom := geom_sum_mul w d
      rw [hwd, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hw1)
  have hsumZ : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
      (∑ m ∈ Finset.range d,
        (-1 : ℂ) ^ m * (exp (Real.pi * I * m / d) ^ S.card *
          exp (-Real.pi * I * m / d) ^ (d - S.card))) =
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        Z S * if S = ∅ ∨ S = Finset.univ then (d : ℂ) else 0 :=
    Finset.sum_congr rfl fun S hS => by rw [hinner S hS]
  rw [hsumZ]
  simp only [mul_ite, mul_zero, ← Finset.sum_filter]
  have hfilt : (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => S = ∅ ∨ S = Finset.univ) = {∅, Finset.univ} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
  have hne_univ : (∅ : Finset (Fin d)) ≠ Finset.univ := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  rw [hfilt, Finset.sum_pair hne_univ]
  have hpow2 : (2 : ℂ) ^ d = (2 : ℂ) ^ (d - 1) * 2 := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
  have h2ne : (2 : ℂ) ^ (d - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [Z, Finset.prod_empty, Finset.sdiff_empty, Finset.sdiff_self, map_one, mul_one,
    ← map_prod (starRingEnd ℂ), hpow2]
  field_simp
  ring
lemma IsSumOfProducts.re {d N : ℕ} (hd : 1 ≤ d) {X : Fin d → Type*}
    {K : (∀ j, X j) → ℂ} (hK : IsSumOfProducts K N) :
    IsSumOfProducts (fun x => (K x).re) (N * d) := by
  obtain ⟨f, hf⟩ := hK
  have hsingle (n : Fin N) :
      IsSumOfProducts (fun x : ∀ j, X j => (∏ j, f n j (x j)).re) d := by
    let j₀ : Fin d := ⟨0, hd⟩
    refine ⟨fun m j u =>
      if j = j₀ then
        (2 : ℝ) ^ (d - 1) / d * (-1 : ℝ) ^ (m : ℕ) *
          (f n j u * exp (-Real.pi * I * (m : ℕ) / d)).re
      else
        (f n j u * exp (-Real.pi * I * (m : ℕ) / d)).re, fun x => ?_⟩
    dsimp only
    rw [re_prod_eq_sum_re hd (fun j => f n j (x j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => (f n j (x j) * exp (-Real.pi * I * (m : ℕ) / d)).re) (Finset.mem_univ j₀)]
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    have her : ∏ j ∈ Finset.univ.erase j₀,
        (if j = j₀ then
          (2 : ℝ) ^ (d - 1) / d * (-1 : ℝ) ^ (m : ℕ) *
            (f n j (x j) * exp (-Real.pi * I * (m : ℕ) / d)).re
        else
          (f n j (x j) * exp (-Real.pi * I * (m : ℕ) / d)).re) =
        ∏ j ∈ Finset.univ.erase j₀,
          (f n j (x j) * exp (-Real.pi * I * (m : ℕ) / d)).re :=
      Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    rw [her]
    simp only [↓reduceIte]
    ring
  have hsum := IsSumOfProducts.finsetSum hsingle
  have hcard : (∑ _n : Fin N, d) = N * d := by simp
  rw [hcard] at hsum
  have heq : (fun x : ∀ j, X j => (K x).re) = fun x => ∑ n : Fin N, (∏ j, f n j (x j)).re := by
    funext x
    rw [hf x, Complex.re_sum]
  rwa [← heq] at hsum
abbrev RealExpSpace {ι_R ι_C : Type*} (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) : Type _ :=
  (∀ i, Fin (m_R i) → ℝ) × (∀ k, Fin (m_C k) → ℂ)
abbrev CplxExpSpace {ι_C : Type*} (m_C : ι_C → ℕ) : Type _ :=
  ∀ k, Fin (m_C k) → ℂ
def singleRealCoeff {ι : Type*} [DecidableEq ι] {m : ι → ℕ} (i₀ : ι) (q₀ : Fin (m i₀))
    (a : ℝ) : ∀ i, Fin (m i) → ℝ :=
  fun i q => if h : i = i₀ then if h ▸ q = q₀ then a else 0 else 0
@[simp]
lemma singleRealCoeff_same {ι : Type*} [DecidableEq ι] {m : ι → ℕ} (i₀ : ι) (q₀ : Fin (m i₀))
    (a : ℝ) : singleRealCoeff i₀ q₀ a i₀ q₀ = a := by
  simp [singleRealCoeff]
def embRealCoeff {ι_R ι_C : Type*} [DecidableEq ι_R] {m_R : ι_R → ℕ} {m_C : ι_C → ℕ}
    (i₀ : ι_R) (q₀ : Fin (m_R i₀)) : ℝ →ₗ[ℝ] RealExpSpace m_R m_C where
  toFun a := (singleRealCoeff i₀ q₀ a, 0)
  map_add' a b := by
    ext i q
    · by_cases hi : i = i₀
      · subst hi
        by_cases hq : q = q₀ <;> simp [singleRealCoeff, hq]
      · simp [singleRealCoeff, hi]
    · simp
  map_smul' r a := by
    ext i q
    · by_cases hi : i = i₀
      · subst hi
        by_cases hq : q = q₀ <;> simp [singleRealCoeff, hq]
      · simp [singleRealCoeff, hi]
    · simp
noncomputable def embCplxCoeff {ι_C : Type*} [DecidableEq ι_C] {m_C : ι_C → ℕ}
    (k₀ : ι_C) (q₀ : Fin (m_C k₀)) : ℂ →ₗ[ℝ] CplxExpSpace m_C where
  toFun z := singleCoeff k₀ q₀ z
  map_add' a b := by
    ext k q
    by_cases hk : k = k₀
    · subst hk
      by_cases hq : q = q₀ <;> simp [singleCoeff, hq]
    · simp [singleCoeff, hk]
  map_smul' r a := by
    ext k q
    by_cases hk : k = k₀
    · subst hk
      by_cases hq : q = q₀ <;> simp [singleCoeff, hq, Complex.real_smul]
    · simp [singleCoeff, hk]
noncomputable def realTruncForm {ι_R : Type*} [Fintype ι_R] (d : ℕ) (m_R c_R : ι_R → ℕ)
    (w_R : ι_R → ℕ → ℝ) (u : Fin d → ∀ i, Fin (m_R i) → ℝ) : ℝ :=
  ∑ i : ι_R, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i),
    w_R i (∑ j, (q j : ℕ)) * ∏ j : Fin d, u j i (q j)
noncomputable def cplxTruncForm {ι_C : Type*} [Fintype ι_C] (d : ℕ) (m_C c_C : ι_C → ℕ)
    (w_C : ι_C → ℕ → ℂ) (u : Fin d → CplxExpSpace m_C) : ℝ :=
  ∑ k : ι_C, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c_C k),
    (w_C k (∑ j, (q j : ℕ)) * ∏ j : Fin d, u j k (q j)).re
noncomputable def realExpForm {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C]
    (d : ℕ) (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_R : ι_R → ℕ) (c_C : ι_C → ℕ)
    (w_R : ι_R → ℕ → ℝ) (w_C : ι_C → ℕ → ℂ)
    (u : Fin d → RealExpSpace m_R m_C) : ℝ :=
  realTruncForm d m_R c_R w_R (fun j => (u j).1) +
    cplxTruncForm d m_C c_C w_C (fun j => (u j).2)
def projRealExp {ι_R ι_C : Type*} {m_R : ι_R → ℕ} {m_C : ι_C → ℕ}
    (i : ι_R) (q : Fin (m_R i)) : RealExpSpace m_R m_C →ₗ[ℝ] ℝ where
  toFun x := x.1 i q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def projCplxExp {ι_R ι_C : Type*} {m_R : ι_R → ℕ} {m_C : ι_C → ℕ}
    (k : ι_C) (q : Fin (m_C k)) : RealExpSpace m_R m_C →ₗ[ℝ] ℂ where
  toFun x := x.2 k q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def realExpMultilinearMap {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C]
    (d : ℕ) (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_R : ι_R → ℕ) (c_C : ι_C → ℕ)
    (w_R : ι_R → ℕ → ℝ) (w_C : ι_C → ℕ → ℂ) :
    MultilinearMap ℝ (fun _ : Fin d => RealExpSpace m_R m_C) ℝ :=
  (∑ i : ι_R, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i),
    w_R i (∑ j, (q j : ℕ)) •
      (MultilinearMap.mkPiAlgebra ℝ (Fin d) ℝ).compLinearMap
        (fun j => projRealExp i (q j))) +
  (∑ k : ι_C, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c_C k),
    ({ toFun := fun z : ℂ => (w_C k (∑ j, (q j : ℕ)) * z).re
       map_add' := fun a b => by simp [mul_add]
       map_smul' := fun r a => by simp [Complex.real_smul, Complex.mul_re]; ring } :
      ℂ →ₗ[ℝ] ℝ).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℝ (Fin d) ℂ).compLinearMap
        (fun j => projCplxExp k (q j))))
end KernelRank


