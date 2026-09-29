-- Prove2me | Definitions.Def_CK_CKLaneA1_Analysis
-- name    : CK_CKLaneA1_Analysis
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:04:57.53298+00:00
-- url     : https://prove2.me/theorems/f0fff6ab-bea8-4bca-93a8-bf436d1c2388
-- title:
--   Courtade–Kumar proof module `CKLaneA1.Analysis` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.Analysis` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.Analysis` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.Analysis (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/Analysis.lean)

import Definitions.Def_CK_CKLaneA1_Interval

/-!
# CKLaneA1.Analysis — real-analysis facts used by the lane A1 checkers

Monotonicity of the probability atoms, the `u → 0` tail bound for `qp u * jn u`,
monotonicity of `biasB`, the even-series bounds for `log((1+C)/(1-C))/C`, and the
contact-coordinate identities for `Fs`, `regularFsGap`, `regularWeight`, `weight`.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates.Reflection (biasE biasB)

/-! ## Probability atoms -/

theorem hn_eq_mul_jn {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Certificates.Mixed.hn x = x * jn x - Real.log (1 - x) := by
  unfold Certificates.Mixed.hn jn
  rw [Real.log_div (by linarith) hx.ne']
  ring

theorem jn_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) : jn y ≤ jn x := by
  unfold jn
  apply Real.log_le_log (div_pos (by linarith) (by linarith))
  rw [div_le_div_iff₀ (by linarith) hx]
  nlinarith

theorem jn_pos {x : ℝ} (hx : 0 < x) (hx2 : x < 1/2) : 0 < jn x := by
  unfold jn
  apply Real.log_pos
  rw [lt_div_iff₀ hx]
  linarith

theorem qp_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) : qp x ≤ qp y := by
  unfold qp; nlinarith

theorem hn_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    Certificates.Mixed.hn x ≤ Certificates.Mixed.hn y := by
  rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  exact H_strictMonoOn.monotoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy

theorem hn_zero : Certificates.Mixed.hn 0 = 0 := by
  simp [Certificates.Mixed.hn]

theorem hn_pos {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : 0 < Certificates.Mixed.hn x := by
  rw [Certificates.Mixed.hn_eq_H_mul_log]
  exact mul_pos (H_pos hx hx1) log_two_pos

theorem entropySum_pos' {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    0 < entropySum u w := by
  unfold entropySum
  exact add_pos (hn_pos hu (by linarith)) (hn_pos (hu.trans huw) (by linarith))

/-- `u·log(1/u)` is bounded by its value at a larger `u2` once `log(1/u2) ≥ 1`. -/
theorem mul_neglog_le {u u2 : ℝ} (hu : 0 < u) (huu : u ≤ u2) (h1 : 1 ≤ -Real.log u2) :
    u * (-Real.log u) ≤ u2 * (-Real.log u2) := by
  have hu2 : 0 < u2 := hu.trans_le huu
  have hb : Real.log (u2/u) ≤ u2/u - 1 := Real.log_le_sub_one_of_pos (div_pos hu2 hu)
  have hlog : -Real.log u = -Real.log u2 + Real.log (u2/u) := by
    rw [Real.log_div hu2.ne' hu.ne']; ring
  have hub : u * Real.log (u2/u) ≤ u2 - u := by
    have := mul_le_mul_of_nonneg_left hb hu.le
    have he : u * (u2/u - 1) = u2 - u := by field_simp
    linarith
  rw [hlog]
  nlinarith

/-- The `u → 0` tail bound for `ku = qp u * jn u`. -/
theorem ku_tail {u u2 : ℝ} (hu : 0 < u) (huu : u ≤ u2) (hu2 : u2 ≤ 1/4) :
    qp u * jn u ≤ u2 * (-Real.log u2) := by
  have hu1 : u < 1/2 := by linarith
  have hJ := jn_pos hu hu1
  have h1 : qp u * jn u ≤ u * jn u := by
    have h0 : 0 ≤ u*u*jn u := mul_nonneg (mul_nonneg hu.le hu.le) hJ.le
    have he : qp u * jn u = u * jn u - u*u*jn u := by unfold qp; ring
    linarith
  have h2 : jn u ≤ -Real.log u := by
    unfold jn
    rw [Real.log_div (by linarith) hu.ne']
    have := Real.log_nonpos (by linarith : (0:ℝ) ≤ 1 - u) (by linarith)
    linarith
  have h4 : 1 ≤ -Real.log u2 := by
    have hu2p : 0 < u2 := hu.trans_le huu
    have hl : Real.log u2 ≤ Real.log (1/4) := Real.log_le_log hu2p hu2
    have h4' : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1/4 : ℝ) = (2^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have h2 : 1 - (2:ℝ)⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
    linarith
  calc qp u * jn u ≤ u * jn u := h1
    _ ≤ u * (-Real.log u) := mul_le_mul_of_nonneg_left h2 hu.le
    _ ≤ u2 * (-Real.log u2) := mul_neglog_le hu huu h4

theorem neglog_eq {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : -Real.log x = jn x - Real.log (1 - x) := by
  unfold jn; rw [Real.log_div (by linarith) hx.ne']; ring

/-! ## Bias functions -/

theorem biasB_mono {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d < 1) : biasB c ≤ biasB d := by
  unfold biasB
  have h1 : 0 < 1 - d*d := by nlinarith
  have h2 : 1 - d*d ≤ 1 - c*c := by nlinarith
  have := Real.log_le_log h1 h2
  linarith

theorem biasB_pos' {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) : 0 < biasB c := by
  unfold biasB
  have h1 : 0 < 1 - c*c := by nlinarith
  have := Real.log_nonpos h1.le (by nlinarith)
  have := log_two_pos
  linarith

theorem biasE_eq_expl (c : ℝ) : biasE c =
    Real.log 2 - ((1 + c) * Real.log (1 + c) + (1 - c) * Real.log (1 - c)) * (2:ℝ)⁻¹ := by
  unfold biasE; ring

theorem biasB_eq_expl {c : ℝ} (hc : -1 < c) (hc1 : c < 1) : biasB c =
    Real.log 2 - (Real.log (1 - c) + Real.log (1 + c)) * (2:ℝ)⁻¹ := by
  unfold biasB
  rw [show 1 - c*c = (1 - c)*(1 + c) by ring, Real.log_mul (by linarith) (by linarith)]
  ring

/-! ## Even-series bounds for `L(C)/C` -/

theorem sum_mul_eq (C : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, C^(2*i+1)/(2*i+1) = C * ∑ i ∈ Finset.range n, C^(2*i)/(2*i+1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pow_succ]; ring

theorem sum_mono_even {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    ∑ i ∈ Finset.range n, a^(2*i)/(2*i+1) ≤ ∑ i ∈ Finset.range n, b^(2*i)/(2*i+1) := by
  apply Finset.sum_le_sum
  intro i _
  gcongr

theorem LoC_bounds {l C h : ℝ} (hl : 0 ≤ l) (hlC : l ≤ C) (hCh : C ≤ h) (h1 : h < 1)
    (hC : 0 < C) (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, l^(2*i)/(2*i+1) ≤ Real.log ((1+C)/(1-C)) / C ∧
    Real.log ((1+C)/(1-C)) / C ≤
      2 * ∑ i ∈ Finset.range n, h^(2*i)/(2*i+1) + 2 * h^(2*n) * (1 - h^2)⁻¹ := by
  have hC1 : C < 1 := lt_of_le_of_lt hCh h1
  have hlo := Real.sum_range_le_log_div hC.le hC1 n
  have hhi := Real.log_div_le_sum_range_add hC.le hC1 n
  rw [sum_mul_eq] at hlo hhi
  set L := Real.log ((1+C)/(1-C))
  set σ := ∑ i ∈ Finset.range n, C^(2*i)/(2*i+1)
  have hσl := sum_mono_even hl hlC n
  have hσh := sum_mono_even hC.le hCh n
  constructor
  · rw [le_div_iff₀ hC]
    nlinarith
  · rw [div_le_iff₀ hC]
    have hpow : C^(2*n+1) = C * C^(2*n) := by rw [pow_succ]; ring
    have hden : 0 < 1 - C^2 := by nlinarith
    have hden' : 0 < 1 - h^2 := by nlinarith
    have hp1 : C^(2*n) ≤ h^(2*n) := pow_le_pow_left₀ hC.le hCh _
    have hq : (1 - C^2)⁻¹ ≤ (1 - h^2)⁻¹ := by
      apply inv_anti₀ hden' ; nlinarith
    have hrem : C^(2*n) / (1 - C^2) ≤ h^(2*n) * (1 - h^2)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hp1 hq (inv_nonneg.mpr hden.le) (pow_nonneg (hC.le.trans hCh) _)
    have hhi' : L ≤ 2 * (C * σ) + 2 * (C * (C^(2*n) / (1 - C^2))) := by
      rw [hpow] at hhi
      have : C * C^(2*n) / (1 - C^2) = C * (C^(2*n) / (1 - C^2)) := by ring
      linarith
    nlinarith

/-! ## Contact coordinates -/

/-- `Fs(C)/C` in the checker's atoms. -/
noncomputable def foc (C : ℝ) : ℝ :=
  Real.log ((1+C)/(1-C)) / C + (2 * biasE C) * ((1 - C*C) * biasB C)⁻¹

/-- `S * weight` in the checker's atoms. -/
noncomputable def gW (C : ℝ) : ℝ :=
  (8 * ((biasE C * biasE C * biasE C) * (2 * biasB C - C*C))) *
    (((1 - C*C) * (1 - C*C)) * (biasB C * biasB C * biasB C))⁻¹

theorem Fs_eq_foc {C : ℝ} (hC : 0 < C) (hC1 : C < 1) : Fs C = C * foc C := by
  have hB := biasB_pos' hC.le hC1
  have hg : 1 - C*C ≠ 0 := by nlinarith
  have hg2 : 1 - C^2 ≠ 0 := by nlinarith
  unfold Fs foc SmallMean.A
  field_simp
  ring

theorem two_Fss_eq_gW (C S : ℝ) (hC : 0 ≤ C) (hC1 : C < 1) (hS : S ≠ 0) :
    2 * Fss C S = gW C * S⁻¹ := by
  have hB := biasB_pos' hC hC1
  have hg : 1 - C*C ≠ 0 := by nlinarith
  have hg2 : 1 - C^2 ≠ 0 := by nlinarith
  unfold Fss gW
  field_simp
  ring

/-- The contact at `(u,w)` and its defining equation. -/
theorem contact_facts {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    0 < contact u w ∧ contact u w < 1 ∧
      biasE (contact u w) = (entropySum u w / (2*(w-u))) * contact u w := by
  have hS := entropySum_pos' hu huw hw
  have hy : 0 < entropySum u w / (2*(w-u)) := div_pos hS (by linarith)
  have hc := Reflection.biasContact_mem hy
  have hr := Reflection.biasR_biasContact hy
  unfold Reflection.biasR at hr
  refine ⟨hc.1, hc.2, ?_⟩
  change biasE (Reflection.biasContact (entropySum u w / (2*(w-u)))) = _ * Reflection.biasContact _
  rw [div_eq_iff hc.1.ne'] at hr
  exact hr

theorem regularFsGap_eq_foc {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    regularFsGap u w = foc (contact u w) * ((2 * biasE (contact u w)) * (entropySum u w)⁻¹) := by
  obtain ⟨hC, hC1, heq⟩ := contact_facts hu huw hw
  have hS := entropySum_pos' hu huw hw
  have hd : 0 < w - u := by linarith
  have h := regularFsGap_mul_gap u w
  unfold regularBias at h
  rw [← contact_eq_regularContact hu huw hw, Fs_eq_foc hC hC1] at h
  have hR : regularFsGap u w = contact u w * foc (contact u w) / (w - u) := by
    field_simp; linarith
  rw [hR, heq]
  field_simp

theorem regularWeight_eq_gW {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    regularWeight u w = gW (contact u w) * (entropySum u w)⁻¹ := by
  obtain ⟨hC, hC1, _⟩ := contact_facts hu huw hw
  have hS := entropySum_pos' hu huw hw
  unfold regularWeight regularBias
  rw [← contact_eq_regularContact hu huw hw]
  exact two_Fss_eq_gW _ _ hC.le hC1 hS.ne'

theorem weight_eq_gW {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    weight u w = gW (contact u w) * (entropySum u w)⁻¹ := by
  obtain ⟨hC, hC1, _⟩ := contact_facts hu huw hw
  have hS := entropySum_pos' hu huw hw
  unfold weight
  exact two_Fss_eq_gW _ _ hC.le hC1 hS.ne'

#print axioms hn_eq_mul_jn
#print axioms ku_tail
#print axioms hn_mono
#print axioms biasB_mono
#print axioms LoC_bounds
#print axioms Fs_eq_foc
#print axioms contact_facts
#print axioms regularFsGap_eq_foc
#print axioms regularWeight_eq_gW
#print axioms weight_eq_gW

end CKLaneA1


