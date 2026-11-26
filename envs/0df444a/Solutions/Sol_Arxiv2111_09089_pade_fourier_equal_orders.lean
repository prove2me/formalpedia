-- Prove2me | solution 1 for Arxiv2111_09089.pade_fourier_equal_orders
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T02:17:15.342266+00:00
-- url     : https://prove2.me/submissions/af1d2bc8-23f7-4ef0-86a0-678477bce06c

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

set_option autoImplicit false
open Complex Filter Topology
open Arxiv2111_09089

namespace S75PF

noncomputable def pI (a : ℤ → ℂ) (L : ℕ) (η : ℂ) : ℂ :=
  ∑ l ∈ Finset.Icc (-(L : ℤ)) L, a l * η ^ (l - L)
noncomputable def pZ (a : ℤ → ℂ) (L : ℕ) (η : ℂ) : ℂ :=
  ∑ l ∈ Finset.Icc (-(L : ℤ)) L, a l * η ^ (l + L).toNat

lemma inv_pow_tendsto (n : ℕ) (hn : 0 < n) :
    Tendsto (fun η : ℂ => η ^ (-(n : ℤ))) (cocompact ℂ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun η : ℂ => ‖η‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h2 : Tendsto (fun η : ℂ => ‖η‖ ^ n) (cocompact ℂ) atTop :=
    (tendsto_pow_atTop hn.ne').comp h1
  have h : Tendsto (fun η : ℂ => (‖η‖ ^ n)⁻¹) (cocompact ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h2
  refine h.congr fun η => ?_
  simp [norm_zpow, zpow_neg, zpow_natCast]

lemma pInf_tendsto (a : ℤ → ℂ) (L : ℕ) :
    Tendsto (fun η : ℂ => pI a L η) (cocompact ℂ) (𝓝 (a L)) := by
  unfold pI
  have : a L = ∑ l ∈ Finset.Icc (-(L : ℤ)) L, if l = L then a l else 0 := by
    rw [Finset.sum_ite_eq']; simp
  rw [this]
  refine tendsto_finsetSum _ fun l hl => ?_
  rcases eq_or_ne l L with rfl | hne
  · simp
  · rw [if_neg hne]
    have hl' : l < L := lt_of_le_of_ne (Finset.mem_Icc.1 hl).2 hne
    obtain ⟨n, hn⟩ : ∃ n : ℕ, l - L = -(n : ℤ) ∧ 0 < n := ⟨(L - l).toNat, by omega, by omega⟩
    rw [hn.1]
    simpa using (inv_pow_tendsto n hn.2).const_mul (a l)

lemma lp_eq_inf (a : ℤ → ℂ) (L : ℕ) (η : ℂ) (hη : η ≠ 0) :
    laurentPoly a L η = η ^ (L : ℤ) * pI a L η := by
  unfold laurentPoly pI
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [zpow_sub₀ hη]
  field_simp

lemma p0_tendsto (a : ℤ → ℂ) (L : ℕ) :
    Tendsto (fun η : ℂ => pZ a L η) (𝓝[≠] 0) (𝓝 (a (-(L : ℤ)))) := by
  unfold pZ
  have hc : Continuous (fun η : ℂ => ∑ l ∈ Finset.Icc (-(L : ℤ)) L, a l * η ^ (l + L).toNat) := by
    fun_prop
  have h0 : (∑ l ∈ Finset.Icc (-(L : ℤ)) L, a l * (0 : ℂ) ^ (l + L).toNat) = a (-(L : ℤ)) := by
    rw [Finset.sum_eq_single (-(L : ℤ))]
    · simp
    · intro l hl hne
      have : (l + L).toNat ≠ 0 := by
        have := (Finset.mem_Icc.1 hl).1; omega
      simp [zero_pow this]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h
  rw [← h0]
  exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

lemma lp_eq_zero (a : ℤ → ℂ) (L : ℕ) (η : ℂ) (hη : η ≠ 0) :
    laurentPoly a L η = η ^ (-(L : ℤ)) * pZ a L η := by
  unfold laurentPoly pZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have : ((l + L).toNat : ℤ) = l + L := by have := (Finset.mem_Icc.1 hl).1; omega
  rw [← zpow_natCast, this, zpow_add₀ hη]
  field_simp
  rw [mul_assoc, ← zpow_add₀ hη]; simp

end S75PF

open S75PF in
theorem solution (α : ℝ) (hα : 0 < α) (g : ℂ → ℂ) (a b : ℤ → ℂ) (L M : ℕ)
    (haL : a L ≠ 0) (haL' : a (-(L : ℤ)) ≠ 0) (hbM : b M ≠ 0) (hbM' : b (-(M : ℤ)) ≠ 0)
    (hg0 : g (xiOfMu α (-I)) ≠ 0) (hginf : g (xiOfMu α I) ≠ 0)
    (h0 : Tendsto (padeFourier a b L M) (𝓝[≠] 0) (𝓝 (g (xiOfMu α (-I)))))
    (hinf : Tendsto (padeFourier a b L M) (cocompact ℂ) (𝓝 (g (xiOfMu α I)))) :
    L = M ∧ a (-(M : ℤ)) / b (-(M : ℤ)) = g (xiOfMu α (-I)) ∧
      a M / b M = g (xiOfMu α I) := by
  have hpq : Tendsto (fun η => pI a L η / pI b M η) (cocompact ℂ) (𝓝 (a L / b M)) :=
    (pInf_tendsto a L).div (pInf_tendsto b M) hbM
  have hev : ∀ᶠ η in cocompact ℂ, η ≠ 0 := by
    have : ({0}ᶜ : Set ℂ) ∈ cocompact ℂ := (isCompact_singleton).compl_mem_cocompact
    exact this
  have hrat : ∀ η : ℂ, η ≠ 0 → padeFourier a b L M η = η ^ ((L : ℤ) - M) * (pI a L η / pI b M η) := by
    intro η hη
    unfold padeFourier
    rw [lp_eq_inf a L η hη, lp_eq_inf b M η hη, zpow_sub₀ hη]
    field_simp
  have hLM : L = M := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · -- ratio tends to 0
      have h1 : Tendsto (fun η : ℂ => η ^ ((L : ℤ) - M) * (pI a L η / pI b M η)) (cocompact ℂ) (𝓝 (0 * (a L / b M))) := by
        obtain ⟨n, hn⟩ : ∃ n : ℕ, (L : ℤ) - M = -(n : ℤ) ∧ 0 < n := ⟨M - L, by omega, by omega⟩
        rw [hn.1]
        exact (inv_pow_tendsto n hn.2).mul hpq
      rw [zero_mul] at h1
      have h2 : Tendsto (padeFourier a b L M) (cocompact ℂ) (𝓝 0) :=
        h1.congr' (hev.mono fun η hη => (hrat η hη).symm)
      exact hginf (tendsto_nhds_unique hinf h2)
    · have hn : ‖a L / b M‖ > 0 := norm_pos_iff.2 (div_ne_zero haL hbM)
      have g1 : Tendsto (fun η : ℂ => ‖η‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
      have g2 : Tendsto (fun η : ℂ => ‖η‖ ^ (L - M)) (cocompact ℂ) atTop :=
        (tendsto_pow_atTop (by omega)).comp g1
      have g3 : Tendsto (fun η : ℂ => ‖pI a L η / pI b M η‖) (cocompact ℂ) (𝓝 ‖a L / b M‖) :=
        hpq.norm
      have h1 : Tendsto (fun η : ℂ => ‖η‖ ^ (L - M) * ‖pI a L η / pI b M η‖) (cocompact ℂ) atTop :=
        g2.atTop_mul_pos hn g3
      have h2 : Tendsto (fun η => ‖padeFourier a b L M η‖) (cocompact ℂ) atTop := by
        refine h1.congr' (hev.mono fun η hη => ?_)
        simp only [Function.comp]
        rw [hrat η hη, norm_mul, norm_zpow, show ((L : ℤ) - M) = ((L - M : ℕ) : ℤ) by omega,
          zpow_natCast]
      exact not_tendsto_nhds_of_tendsto_atTop h2 _ hinf.norm
  subst hLM
  refine ⟨rfl, ?_, ?_⟩
  · have h1 : Tendsto (fun η => pZ a L η / pZ b L η) (𝓝[≠] 0) (𝓝 (a (-(L : ℤ)) / b (-(L : ℤ)))) :=
      (p0_tendsto a L).div (p0_tendsto b L) hbM'
    refine tendsto_nhds_unique (h1.congr' ?_) h0
    filter_upwards [self_mem_nhdsWithin] with η hη
    unfold padeFourier
    rw [lp_eq_zero a L η hη, lp_eq_zero b L η hη]
    have : η ^ (-(L : ℤ)) ≠ 0 := zpow_ne_zero _ hη
    rw [mul_div_mul_left _ _ this]
  · have h1 : Tendsto (padeFourier a b L L) (cocompact ℂ) (𝓝 (a L / b L)) := by
      refine hpq.congr' (hev.mono fun η hη => ?_)
      rw [hrat η hη, sub_self, zpow_zero, one_mul]
    exact tendsto_nhds_unique h1 hinf
