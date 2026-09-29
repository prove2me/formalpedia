-- Prove2me | Definitions.Def_CK_CKLaneA3V_Series
-- name    : CK_CKLaneA3V_Series
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:24:38.237448+00:00
-- url     : https://prove2.me/theorems/d8e2d80a-1f8f-475b-80b8-a8491220ed62
-- title:
--   Courtade–Kumar proof module `CKLaneA3V.Series` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3V.Series` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3V.Series` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3V.Series (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3V/Series.lean)

import Definitions.Def_CK_CKLaneA3V_TMFun

/-!
# CKLaneA3V.Series — analytic series remainders (atanh, atanh/x, log(1-y), divided difference)
-/

namespace CKLaneA3V

open Finset

noncomputable def atanhR (x : ℝ) : ℝ := Real.log ((1 + x) / (1 - x)) / 2

theorem sum_odd_identity (x : ℝ) (K : ℕ) :
    ∑ i ∈ range (2 * K), (x ^ (i + 1) / ((i : ℝ) + 1) - (-x) ^ (i + 1) / ((i : ℝ) + 1)) =
      2 * ∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h2 : 2 * (K + 1) = 2 * K + 1 + 1 := by ring
    rw [h2, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    have hodd : (-x) ^ (2 * K + 1) = -(x ^ (2 * K + 1)) := Odd.neg_pow ⟨K, rfl⟩ x
    have heven : (-x) ^ (2 * K + 1 + 1) = x ^ (2 * K + 1 + 1) := Even.neg_pow ⟨K + 1, by ring⟩ x
    rw [hodd, heven]
    push_cast
    ring

theorem atanh_series {x : ℝ} (hx : |x| < 1) (K : ℕ) :
    |atanhR x - ∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)| ≤ |x| ^ (2 * K + 1) / (1 - |x|) := by
  have h1 := Real.abs_log_sub_add_sum_range_le hx (2 * K)
  have hx' : |-x| < 1 := by rwa [abs_neg]
  have h2 := Real.abs_log_sub_add_sum_range_le hx' (2 * K)
  rw [abs_neg, sub_neg_eq_add] at h2
  have hp : 0 < 1 + x := by have := (abs_lt.mp hx).1; linarith
  have hm : 0 < 1 - x := by have := (abs_lt.mp hx).2; linarith
  have hlog : Real.log ((1 + x) / (1 - x)) = Real.log (1 + x) - Real.log (1 - x) :=
    Real.log_div hp.ne' hm.ne'
  have hid := sum_odd_identity x K
  rw [sum_sub_distrib] at hid
  set S1 := ∑ i ∈ range (2 * K), x ^ (i + 1) / ((i : ℝ) + 1)
  set S2 := ∑ i ∈ range (2 * K), (-x) ^ (i + 1) / ((i : ℝ) + 1)
  set Sk := ∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)
  have hkey : atanhR x - Sk = ((S2 + Real.log (1 + x)) - (S1 + Real.log (1 - x))) / 2 := by
    unfold atanhR; rw [hlog]; linarith
  rw [hkey, abs_div, abs_two]
  have := abs_sub (S2 + Real.log (1 + x)) (S1 + Real.log (1 - x))
  have hden : 0 < 1 - |x| := by linarith
  have e : |x| ^ (2 * K + 1) / (1 - |x|) = (|x| ^ (2 * K + 1) / (1 - |x|) + |x| ^ (2 * K + 1) / (1 - |x|)) / 2 := by ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

theorem atanh_div_series {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) (K : ℕ) :
    |atanhR x / x - ∑ k ∈ range K, x ^ (2 * k) / (2 * (k : ℝ) + 1)| ≤ |x| ^ (2 * K) / (1 - |x|) := by
  have h := atanh_series hx K
  have hxa : 0 < |x| := abs_pos.mpr hx0
  have hden : 0 < 1 - |x| := by linarith
  have hsum : ∑ k ∈ range K, x ^ (2 * k) / (2 * (k : ℝ) + 1) =
      (∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) / x := by
    rw [sum_div]; congr 1; ext k
    rw [eq_div_iff hx0, pow_succ]; ring
  rw [hsum, ← sub_div, abs_div, div_le_iff₀ hxa]
  calc _ ≤ |x| ^ (2 * K + 1) / (1 - |x|) := h
    _ = |x| ^ (2 * K) / (1 - |x|) * |x| := by rw [pow_succ]; ring

theorem log1m_series {y : ℝ} (hy : |y| < 1) (n : ℕ) :
    |Real.log (1 - y) + ∑ i ∈ range n, y ^ (i + 1) / ((i : ℝ) + 1)| ≤ |y| ^ (n + 1) / (1 - |y|) := by
  have := Real.abs_log_sub_add_sum_range_le hy n
  rwa [add_comm] at this

theorem hasDerivAt_atanhR {z : ℝ} (hz : |z| < 1) : HasDerivAt atanhR (1 / (1 - z ^ 2)) z := by
  have hp : 0 < 1 + z := by have := (abs_lt.mp hz).1; linarith
  have hm : 0 < 1 - z := by have := (abs_lt.mp hz).2; linarith
  have hnum : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have hden : HasDerivAt (fun z : ℝ => 1 - z) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have hq := hnum.div hden hm.ne'
  have hl := hq.log (div_pos hp hm).ne'
  have h2 := hl.div_const 2
  have h1m : (1 : ℝ) - z ≠ 0 := hm.ne'
  have h1p : (1 : ℝ) + z ≠ 0 := hp.ne'
  have h1z : (1 : ℝ) - z ^ 2 ≠ 0 := by
    have : (1 : ℝ) - z ^ 2 = (1 - z) * (1 + z) := by ring
    rw [this]; exact mul_ne_zero h1m h1p
  have key : (1 : ℝ) / (1 - z ^ 2) =
      ((1 * (1 - z) - (1 + z) * (-1)) / (1 - z) ^ 2) / ((1 + z) / (1 - z)) / 2 := by
    field_simp; ring
  rw [key]
  exact h2

theorem sum_even_pow_eq (z : ℝ) (hz : z ^ 2 ≠ 1) (K : ℕ) :
    ∑ k ∈ range K, z ^ (2 * k) = (1 - z ^ (2 * K)) / (1 - z ^ 2) := by
  have h1 : (1 - z ^ 2) ≠ 0 := by intro h; apply hz; linarith
  rw [eq_div_iff h1]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, add_mul, ih]
    have : z ^ (2 * (K + 1)) = z ^ (2 * K) * z ^ 2 := by rw [← pow_add]; ring_nf
    rw [this]; ring

/-- `F K z = atanh z - Σ_{k<K} z^(2k+1)/(2k+1)` -/
noncomputable def atanhRem (K : ℕ) (z : ℝ) : ℝ :=
  atanhR z - ∑ k ∈ range K, z ^ (2 * k + 1) / (2 * (k : ℝ) + 1)

theorem hasDerivAt_atanhRem (K : ℕ) {z : ℝ} (hz : |z| < 1) :
    HasDerivAt (atanhRem K) (z ^ (2 * K) / (1 - z ^ 2)) z := by
  have hA := hasDerivAt_atanhR hz
  have hS : HasDerivAt (fun z => ∑ k ∈ range K, z ^ (2 * k + 1) / (2 * (k : ℝ) + 1))
      (∑ k ∈ range K, z ^ (2 * k)) z := by
    have := HasDerivAt.fun_sum (u := range K) (A := fun k z => z ^ (2 * k + 1) / (2 * (k : ℝ) + 1))
      (A' := fun k => z ^ (2 * k)) (x := z) (fun k _ => by
        have h := (hasDerivAt_pow (2 * k + 1) z).div_const (2 * (k : ℝ) + 1)
        have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
        have e : ((↑(2 * k + 1) : ℝ) * z ^ (2 * k + 1 - 1)) / (2 * (k : ℝ) + 1) = z ^ (2 * k) := by
          rw [Nat.add_sub_cancel]; push_cast; field_simp
        exact h.congr_deriv e)
    simpa using this
  have h := hA.sub hS
  have hz2 : z ^ 2 ≠ 1 := by
    intro h1
    have : |z| ^ 2 = 1 := by rw [sq_abs]; exact h1
    nlinarith [abs_nonneg z]
  have h1 : (1 - z ^ 2) ≠ 0 := by intro h'; apply hz2; linarith
  have e : 1 / (1 - z ^ 2) - ∑ k ∈ range K, z ^ (2 * k) = z ^ (2 * K) / (1 - z ^ 2) := by
    rw [sum_even_pow_eq z hz2 K]
    field_simp
    ring
  exact h.congr_deriv e

theorem geom_div_identity (x y : ℝ) (hxy : x ≠ y) (m : ℕ) :
    ∑ i ∈ range m, x ^ i * y ^ (m - 1 - i) = (y ^ m - x ^ m) / (y - x) := by
  have h := geom_sum₂_mul x y m
  have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  rw [eq_div_iff hne]
  have : (y ^ m - x ^ m) = -(x ^ m - y ^ m) := by ring
  rw [this, ← h]; ring

theorem dd_atanh_series {x y X : ℝ} (hxy : x ≠ y) (hx : |x| ≤ X) (hy : |y| ≤ X) (hX : X < 1) (K : ℕ) :
    |(atanhR y - atanhR x) / (y - x) -
        ∑ k ∈ range K, (1 / (2 * (k : ℝ) + 1)) * ∑ i ∈ range (2 * k + 1), x ^ i * y ^ (2 * k - i)| ≤
      X ^ (2 * K) / (1 - X ^ 2) := by
  have hX0 : 0 ≤ X := (abs_nonneg x).trans hx
  have hsum : ∑ k ∈ range K, (1 / (2 * (k : ℝ) + 1)) * ∑ i ∈ range (2 * k + 1), x ^ i * y ^ (2 * k - i) =
      ((∑ k ∈ range K, y ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) -
        (∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1))) / (y - x) := by
    rw [← sum_sub_distrib, sum_div]
    congr 1; ext k
    have hg : ∑ i ∈ range (2 * k + 1), x ^ i * y ^ (2 * k - i) = (y ^ (2 * k + 1) - x ^ (2 * k + 1)) / (y - x) := by
      have := geom_div_identity x y hxy (2 * k + 1)
      simpa using this
    rw [hg]
    have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hsum, ← sub_div]
  have hre : atanhR y - atanhR x - ((∑ k ∈ range K, y ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) -
      (∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1))) = atanhRem K y - atanhRem K x := by
    unfold atanhRem; ring
  rw [hre]
  -- mean value theorem on the segment between x and y
  have hderiv : ∀ z : ℝ, |z| ≤ X → HasDerivAt (atanhRem K) (z ^ (2 * K) / (1 - z ^ 2)) z :=
    fun z hz => hasDerivAt_atanhRem K (lt_of_le_of_lt hz hX)
  have hbound : ∀ z : ℝ, |z| ≤ X → 0 ≤ z ^ (2 * K) / (1 - z ^ 2) ∧
      z ^ (2 * K) / (1 - z ^ 2) ≤ X ^ (2 * K) / (1 - X ^ 2) := by
    intro z hz
    have hz2 : z ^ 2 ≤ X ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
    have hX2 : X ^ 2 < 1 := by nlinarith
    have hpos : 0 < 1 - z ^ 2 := by linarith
    have hposX : 0 < 1 - X ^ 2 := by linarith
    have hzk : z ^ (2 * K) ≤ X ^ (2 * K) := by
      rw [pow_mul, pow_mul]; exact pow_le_pow_left₀ (sq_nonneg _) hz2 K
    have hzk0 : 0 ≤ z ^ (2 * K) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) K
    refine ⟨div_nonneg hzk0 hpos.le, ?_⟩
    rw [div_le_div_iff₀ hpos hposX]
    nlinarith [mul_le_mul hzk (by linarith : 1 - X ^ 2 ≤ 1 - z ^ 2) hposX.le (by positivity)]
  have key : ∀ a b : ℝ, a < b → |a| ≤ X → |b| ≤ X →
      ∃ c, |c| ≤ X ∧ (atanhRem K b - atanhRem K a) / (b - a) = c ^ (2 * K) / (1 - c ^ 2) := by
    intro a b hab ha hb
    have hIcc : ∀ z ∈ Set.Icc a b, |z| ≤ X := by
      intro z hz
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [hz.1, hz.2, ha.1, ha.2, hb.1, hb.2]
    have hcont : ContinuousOn (atanhRem K) (Set.Icc a b) :=
      fun z hz => (hderiv z (hIcc z hz)).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (atanhRem K)
      (fun z => z ^ (2 * K) / (1 - z ^ 2)) hab hcont
      (fun z hz => hderiv z (hIcc z (Set.Ioo_subset_Icc_self hz)))
    exact ⟨c, hIcc c (Set.Ioo_subset_Icc_self hc), hcd.symm⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨c, hc, hce⟩ := key x y h hx hy
    rw [hce]
    obtain ⟨h0, h1⟩ := hbound c hc
    rw [abs_of_nonneg h0]; exact h1
  · obtain ⟨c, hc, hce⟩ := key y x h hy hx
    have : (atanhRem K y - atanhRem K x) / (y - x) = (atanhRem K x - atanhRem K y) / (x - y) := by
      rw [← neg_sub (atanhRem K x), ← neg_sub x, neg_div_neg_eq]
    rw [this, hce]
    obtain ⟨h0, h1⟩ := hbound c hc
    rw [abs_of_nonneg h0]; exact h1

end CKLaneA3V


