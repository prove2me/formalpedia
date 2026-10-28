-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_32
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T11:20:23.278263+00:00
-- url     : https://prove2.me/submissions/c7812290-462a-4050-87a1-865873010f19

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

open Filter
open scoped Topology

namespace PriorLog

namespace Queelius.APrioriTSP

theorem log_ratio (x y : ℝ) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    x / y - x < Real.log (1 - x) / Real.log (1 - y) ∧
      Real.log (1 - x) / Real.log (1 - y) < x / y := by
  have hy0 : 0 < y := hx.trans hxy
  have hx1 : x < 1 := hxy.trans hy
  have ha : 0 < 1 - x := by linarith
  have hb : 0 < 1 - y := by linarith
  have hlnx : Real.log (1 - x) < 0 := Real.log_neg ha (by linarith)
  have hlny : Real.log (1 - y) < 0 := Real.log_neg hb (by linarith)
  have hlowx : x < -Real.log (1 - x) := by
    have hh := Real.log_lt_sub_one_of_pos ha (by linarith : 1 - x ≠ 1)
    linarith
  have hupy : -Real.log (1 - y) < y / (1 - y) := by
    have hh := Real.log_lt_sub_one_of_pos (inv_pos.mpr hb)
      (by intro he; have he' := (inv_eq_one.mp he); linarith : (1 - y)⁻¹ ≠ 1)
    rw [Real.log_inv] at hh
    convert hh using 1
    field_simp
    ring
  constructor
  · rw [show Real.log (1 - x) / Real.log (1 - y) =
        (-Real.log (1 - x)) / (-Real.log (1 - y)) by ring,
      lt_div_iff₀ (neg_pos.mpr hlny)]
    have hfac : 0 < x / y - x := by
      have : x < x / y := (lt_div_iff₀ hy0).2 (by nlinarith)
      linarith
    have hh := mul_lt_mul_of_pos_left hupy hfac
    have heq : (x / y - x) * (y / (1 - y)) = x := by field_simp <;> ring
    rw [heq] at hh
    exact hh.trans hlowx
  · have hc := strictConcaveOn_log_Ioi.secant_strict_mono
      (a := (1 : ℝ)) (x := 1 - y) (y := 1 - x)
      (by norm_num) hb ha (by linarith) (by linarith) (by linarith)
    simp only [Real.log_one, sub_zero, sub_sub_cancel_left] at hc
    rw [div_lt_iff_of_neg hlny]
    have hs : Real.log (1 - x) / (-x) < Real.log (1 - y) / (-y) := by
      simpa using hc
    have hm : Real.log (1 - y) * x < Real.log (1 - x) * y := by
      have he := mul_lt_mul_of_pos_left hs (mul_pos hx hy0)
      field_simp at he
      nlinarith
    apply (mul_lt_mul_iff_left₀ hy0).mp
    calc
      (x / y * Real.log (1 - y)) * y = Real.log (1 - y) * x := by field_simp <;> ring
      _ < Real.log (1 - x) * y := hm

end Queelius.APrioriTSP

open APrioriTSP.Sampling

/-- Proposition 31 (p. 30): for `0 < x < y < 1`,
`x/y − x < ln(1 − x)/ln(1 − y) < x/y`. -/
theorem solution (x y : ℝ) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    x / y - x < Real.log (1 - x) / Real.log (1 - y) ∧
      Real.log (1 - x) / Real.log (1 - y) < x / y := by
  exact Queelius.APrioriTSP.log_ratio x y hx hxy hy


end PriorLog

namespace Queelius.CopyCount

lemma p_one (σ lam ε : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hlam : 0 < lam)
    (hε : 0 < ε) (hε1 : ε < 1) : ∃ k : ℕ,
    (1 - (1 - ε) ^ k ≤ 1 ∧ (1 : ℝ) ≤ ε * k) ∧
    (1 - (1 : ℝ)) ^ σ ≤ (1 - σ * ε) ^ k ∧
    1 - (1 - (1 : ℝ)) ^ σ ≤ (1 + lam) * (1 - (1 - σ * ε) ^ k) ∧
    (1 - ε) ^ k ≤ lam := by
  have ha0 : 0 < 1 - ε := by linarith
  have hb0 : 0 < 1 - σ * ε := by nlinarith
  have hb1 : 1 - σ * ε < 1 := by nlinarith
  have ht : 0 < lam / (1 + lam) := div_pos hlam (by linarith)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1
  have he := hp.eventually (Iio_mem_nhds ht)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  obtain ⟨K, hK⟩ := exists_nat_ge (1 / ε)
  let k := max N K
  have hk : 1 / ε ≤ (k : ℝ) := le_trans hK (by exact_mod_cast le_max_right N K)
  have hkp : 1 ≤ ε * k := by
    have h := (div_le_iff₀ hε).1 hk
    nlinarith
  have hpow : (1 - σ * ε) ^ k < lam / (1 + lam) := hN k (le_max_left _ _)
  have hpow' := (lt_div_iff₀ (show 0 < 1 + lam by linarith)).1 hpow
  have hcmp : (1 - ε) ^ k ≤ (1 - σ * ε) ^ k := by
    apply pow_le_pow_left₀ ha0.le
    nlinarith
  refine ⟨k, ⟨?_, hkp⟩, ?_, ?_, ?_⟩
  · linarith [pow_nonneg ha0.le k]
  · simp only [sub_self, Real.zero_rpow (ne_of_gt hσ0)]
    exact pow_nonneg hb0.le _
  · simp only [sub_self, Real.zero_rpow (ne_of_gt hσ0)]
    nlinarith
  · have hc : lam / (1 + lam) < lam := div_lt_self hlam (by linarith)
    exact hcmp.trans (hpow.trans hc).le

lemma log_lower (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) : p < -Real.log (1 - p) := by
  have h := Real.log_lt_sub_one_of_pos (show 0 < 1 - p by linarith [hp.2])
    (show 1 - p ≠ 1 by linarith [hp.1])
  linarith

lemma log_upper (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    (-Real.log (1 - ε)) * (1 - ε) ≤ ε := by
  have ha : 0 < 1 - ε := by linarith [hε.2]
  have hh := Real.log_lt_sub_one_of_pos (inv_pos.mpr ha)
    (by intro h; have := inv_eq_one.mp h; linarith [hε.1] : (1 - ε)⁻¹ ≠ 1)
  rw [Real.log_inv] at hh
  have h := mul_le_mul_of_nonneg_right hh.le ha.le
  have he : ((1 - ε)⁻¹ - 1) * (1 - ε) = ε := by field_simp; ring
  rwa [he] at h

lemma rpow_log_identity (a q : ℝ) (ha : 0 < a) (ha1 : a < 1) (hq : 0 < q) :
    a ^ (Real.log q / Real.log a) = q := by
  rw [Real.rpow_def_of_pos ha]
  have hln : Real.log a ≠ 0 := ne_of_lt (Real.log_neg ha ha1)
  have he : Real.log a * (Real.log q / Real.log a) = Real.log q := by field_simp
  rw [he, Real.exp_log hq]

lemma rpow_log_swap (a b q : ℝ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) :
    b ^ (Real.log q / Real.log a) = q ^ (Real.log b / Real.log a) := by
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hq]
  congr 1
  ring

lemma floor_power_bounds (a x : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    a ^ x ≤ a ^ (⌊x⌋₊ : ℕ) ∧ a ^ (⌊x⌋₊ : ℕ) ≤ a ^ (x - 1) := by
  rw [← Real.rpow_natCast]
  constructor
  · exact Real.rpow_le_rpow_of_exponent_ge ha ha1 (Nat.floor_le hx)
  · apply Real.rpow_le_rpow_of_exponent_ge ha ha1
    linarith [Nat.lt_floor_add_one x]

end Queelius.CopyCount

open APrioriTSP.Sampling
namespace Queelius.CopyCount

lemma pointwise (σ lam p ε κ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hlam : 0 < lam) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hmargin : ε * (-Real.log (1 - p) + 1) ≤ -Real.log (1 - p) - p)
    (herror : (1 - σ * ε)⁻¹ * (1 - p) ^ (-σ * ε) ≤ 1 + κ)
    (hκ : 1 - (1 - p) ^ σ ≤ (1 + lam) * (1 - (1 + κ) * (1 - p) ^ σ))
    (hlamε : ε ≤ lam / (1 + lam)) :
    ∃ k : ℕ, (1 - (1 - ε) ^ k ≤ p ∧ p ≤ ε * k) ∧
      (1 - p) ^ σ ≤ (1 - σ * ε) ^ k ∧
      1 - (1 - p) ^ σ ≤ (1 + lam) * (1 - (1 - σ * ε) ^ k) ∧
      (1 - ε) ^ k ≤ (1 + lam) * (1 - p) := by
  let a := 1 - ε
  let b := 1 - σ * ε
  let q := 1 - p
  let L := -Real.log q
  let M := -Real.log a
  let y := L / M
  let k := ⌊y⌋₊
  have ha0 : 0 < a := by dsimp [a]; linarith [hε.2]
  have ha1 : a < 1 := by dsimp [a]; linarith [hε.1]
  have hb0 : 0 < b := by dsimp [b]; nlinarith [hε.1,hε.2]
  have hb1 : b < 1 := by dsimp [b]; nlinarith [hε.1]
  have hq0 : 0 < q := by dsimp [q]; linarith [hp.2]
  have hq1 : q < 1 := by dsimp [q]; linarith [hp.1]
  have hL : 0 < L := neg_pos.mpr (Real.log_neg hq0 hq1)
  have hM : 0 < M := neg_pos.mpr (Real.log_neg ha0 ha1)
  have hy : 0 < y := div_pos hL hM
  have heY : Real.log q / Real.log a = y := by dsimp [y,L,M]; ring
  have hMy : M * y = L := by dsimp [y]; field_simp
  have hfloor := floor_power_bounds a y ha0 ha1.le hy.le
  have hfloorB := floor_power_bounds b y hb0 hb1.le hy.le
  have haY : a ^ y = q := by rw [← heY]; exact rpow_log_identity a q ha0 ha1 hq0
  have hεk : p ≤ ε * k := by
    have hbound : M * a ≤ ε := log_upper ε hε
    have hh := mul_le_mul_of_nonneg_right hbound hy.le
    have hm := congrArg (fun z : ℝ => z * a) hMy
    have hg : p + ε ≤ L * a := by dsimp [a,L,q] at *; nlinarith
    have hk : y - 1 ≤ (k : ℝ) := by dsimp [k]; linarith [Nat.lt_floor_add_one y]
    have hh' := mul_le_mul_of_nonneg_left hk hε.1.le
    nlinarith
  have hratio := PriorLog.solution (σ * ε) ε (mul_pos hσ0 hε.1)
    (by nlinarith [hε.1]) hε.2
  have hdiv : σ * ε / ε = σ := by field_simp [ne_of_gt hε.1]
  rw [hdiv] at hratio
  have hby : b ^ y = q ^ (Real.log b / Real.log a) := by
    rw [← heY]
    exact rpow_log_swap a b q ha0 hb0 hq0
  have hlow : q ^ σ ≤ b ^ k := by
    have hh := Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hratio.2.le
    rw [← hby] at hh
    exact hh.trans hfloorB.1
  have hup : b ^ k ≤ (1 + κ) * q ^ σ := by
    calc
      _ ≤ b ^ (y - 1) := hfloorB.2
      _ = b⁻¹ * q ^ (Real.log b / Real.log a) := by
        rw [Real.rpow_sub_one (ne_of_gt hb0), hby]
        ring
      _ ≤ b⁻¹ * q ^ (σ - σ * ε) := by
        apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hb0).le
        exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hratio.1.le
      _ = (b⁻¹ * q ^ (-σ * ε)) * q ^ σ := by
        rw [show σ - σ * ε = σ + (-σ * ε) by ring, Real.rpow_add hq0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right herror (Real.rpow_pos_of_pos hq0 σ).le
  have haup : a ^ k ≤ (1 + lam) * q := by
    calc
      _ ≤ a ^ (y - 1) := hfloor.2
      _ = q / a := by rw [Real.rpow_sub_one (ne_of_gt ha0), haY]
      _ ≤ _ := by
        apply (div_le_iff₀ ha0).2
        have hLam := (le_div_iff₀ (show 0 < 1 + lam by linarith)).1 hlamε
        dsimp [a]
        nlinarith [mul_nonneg hq0.le (show 0 ≤ lam - ε * (1 + lam) by nlinarith)]
  refine ⟨k, ⟨?_,hεk⟩, hlow, ?_, haup⟩
  · have hh := hfloor.1
    rw [haY] at hh
    dsimp [a,q] at hh
    linarith
  · dsimp [b,q] at hup
    have hh := mul_le_mul_of_nonneg_left (sub_le_sub_left hup 1) (show 0 ≤ 1 + lam by linarith)
    exact hκ.trans hh

end Queelius.CopyCount

open APrioriTSP.Sampling

/-- Lemma 32 (p. 31): choosing the number `k` of copies of a customer. -/
theorem solution (σ lam p : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hlam : 0 < lam)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ εp : ℝ, 0 < εp ∧ εp < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εp → ∃ k : ℕ,
      (1 - (1 - ε) ^ k ≤ p ∧ p ≤ ε * k) ∧
      (1 - p) ^ σ ≤ (1 - σ * ε) ^ k ∧
      1 - (1 - p) ^ σ ≤ (1 + lam) * (1 - (1 - σ * ε) ^ k) ∧
      (p < 1 → (1 - ε) ^ k ≤ (1 + lam) * (1 - p)) ∧
      (p = 1 → (1 - ε) ^ k ≤ lam) := by
  by_cases hpOne : p = 1
  · subst p
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro ε hε hεle
    have hε1 : ε < 1 := by linarith
    obtain ⟨k,h1,h2,h3,h4⟩ := Queelius.CopyCount.p_one σ lam ε hσ0 hσ1 hlam hε hε1
    exact ⟨k,h1,h2,h3,(by intro h; linarith),(by intro h; exact h4)⟩
  have hp : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, lt_of_le_of_ne hp1 hpOne⟩
  let q := 1 - p
  let Q := q ^ σ
  let L := -Real.log q
  let κ := lam * (1 - Q) / ((1 + lam) * Q)
  have hq0 : 0 < q := by dsimp [q]; linarith [hp.2]
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hq0 σ
  have hQ1 : Q < 1 := Real.rpow_lt_one hq0.le hq1 hσ0
  have hL : p < L := Queelius.CopyCount.log_lower p hp
  have hL1 : 0 < L + 1 := by linarith
  have hκ0 : 0 < κ := div_pos (mul_pos hlam (by linarith)) (mul_pos (by linarith) hQ0)
  have hQne : Q ≠ 0 := ne_of_gt hQ0
  have hLamne : 1 + lam ≠ 0 := by linarith
  have hκeq : (1 + lam) * (1 - (1 + κ) * Q) = 1 - Q := by
    dsimp [κ]
    field_simp
    ring
  let F := fun ε : ℝ => (1 - σ * ε)⁻¹ * q ^ (-σ * ε)
  have hc1 : ContinuousAt (fun ε : ℝ => (1 - σ * ε)⁻¹) 0 := by
    have hbase : ContinuousAt (fun ε : ℝ => 1 - σ * ε) 0 := by fun_prop
    exact hbase.inv₀ (by norm_num)
  have hc2 : ContinuousAt (fun ε : ℝ => q ^ (-σ * ε)) 0 := by
    have hbase : Continuous (fun ε : ℝ => Real.exp (Real.log q * (-σ * ε))) := by fun_prop
    simpa only [Real.rpow_def_of_pos hq0] using hbase.continuousAt
  have hc : ContinuousAt F 0 := hc1.mul hc2
  have hf0 : F 0 = 1 := by simp [F]
  have hev : ∀ᶠ ε in nhds (0 : ℝ), F ε < 1 + κ :=
    hc.tendsto.eventually (Iio_mem_nhds (show F 0 < 1 + κ by rw [hf0]; linarith))
  obtain ⟨δ,hδ0,hδ⟩ := Metric.eventually_nhds_iff.1 hev
  let ep := min (1 / 2 : ℝ) (min ((L - p) / (L + 1)) (min (δ / 2) (lam / (1 + lam))))
  have hep0 : 0 < ep := by dsimp [ep]; positivity
  have hep1 : ep < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨ep,hep0,hep1,?_⟩
  intro ε hε hεep
  have heps : ε ≤ 1 / 2 ∧ ε ≤ (L - p) / (L + 1) ∧ ε ≤ δ / 2 ∧ ε ≤ lam / (1 + lam) := by
    simpa only [ep, le_min_iff] using hεep
  have hε1 : ε < 1 := by linarith [heps.1]
  have hmargin : ε * (-Real.log (1 - p) + 1) ≤ -Real.log (1 - p) - p := by
    change ε * (L + 1) ≤ L - p
    exact (le_div_iff₀ hL1).1 heps.2.1
  have hdist : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    linarith [heps.2.2.1]
  have herror : (1 - σ * ε)⁻¹ * (1 - p) ^ (-σ * ε) ≤ 1 + κ := (hδ hdist).le
  have hκ : 1 - (1 - p) ^ σ ≤ (1 + lam) * (1 - (1 + κ) * (1 - p) ^ σ) := hκeq.ge
  obtain ⟨k,h1,h2,h3,h4⟩ := Queelius.CopyCount.pointwise σ lam p ε κ hσ0 hσ1 hlam hp ⟨hε,hε1⟩
    hmargin herror hκ heps.2.2.2
  exact ⟨k,h1,h2,h3,(by intro h; exact h4),(by intro h; exact False.elim (hpOne h))⟩

