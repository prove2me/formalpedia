-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionHighBiasCases_v2
-- name    : CK_GeneralCK_ReflectionHighBiasCases_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:06:45.697285+00:00
-- url     : https://prove2.me/theorems/2f23f043-4f9b-436a-82af-7c05570a115b
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionHighBiasCases` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionHighBiasCases` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionHighBiasCases` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionHighBiasCases (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionHighBiasCases.lean)

import Definitions.Def_CK_GeneralCK_ReflectionHighBiasLog
import Definitions.Def_CK_GeneralCK_ReflectionRegularContact
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.GCongr

-- ===== source module GeneralCK.ReflectionHighBiasCases =====
section

namespace GeneralCK.Reflection.HighBiasCases
open SmallMean Certificates.Reflection
noncomputable section

def Qtail (a c : ℝ) : ℝ :=
  ((1-a)/(1-c))*(1+(A a-A c)/biasB c)

def tailUpper (a b c : ℝ) : ℝ :=
  2*(Qtail a c)^2/(a^3*b*(a+b)*(1+c)^2)+
    ((1-a)/(1-c))/(a^3*b*(1+a)*(1+c)*biasB c)

theorem A_mono {a c : ℝ} (hc : 0≤c) (hca : c≤a) (ha : a<1) : A c≤A a := by
  have hc1 : c<1 := hca.trans_lt ha
  have hq : (1+c)/(1-c)≤(1+a)/(1-a) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hl := Real.log_le_log (div_pos (by linarith : 0<1+c) (by linarith)) hq
  unfold A
  linarith

theorem biasB_ge_log_two {c : ℝ} (hc : 0≤c) (hc1 : c<1) : Real.log 2≤biasB c := by
  have hl := Real.log_nonpos (show 0≤1-c*c by nlinarith) (show 1-c*c≤1 by nlinarith)
  unfold biasB
  linarith

theorem A_sub_upper {a c : ℝ} (hc : 0≤c) (hca : c≤a) (ha : a<1) :
    A a-A c≤(a-c)/((1-a)*(1+c)) := by
  have hc1 : c<1 := hca.trans_lt ha
  have hup : 0<(1+a)/(1-a) := div_pos (by linarith) (by linarith)
  have hvp : 0<(1+c)/(1-c) := div_pos (by linarith) (by linarith)
  have h := Real.log_le_sub_one_of_pos (div_pos hup hvp)
  rw [Real.log_div hup.ne' hvp.ne'] at h
  have heq : (((1+a)/(1-a))/((1+c)/(1-c))-1)/2=(a-c)/((1-a)*(1+c)) := by
    have hm : 1-a≠0 := by linarith
    have hcm : 1-c≠0 := by linarith
    have hcp : 1+c≠0 := by linarith
    field_simp
    ring
  rw [← heq]
  unfold A
  linarith

theorem Qtail_nonneg {a c : ℝ} (hc : 0≤c) (hca : c≤a) (ha : a<1) : 0≤Qtail a c := by
  have hB := biasB_pos_wide (by linarith : -1<c) (hca.trans_lt ha)
  have hd := sub_nonneg.mpr (A_mono hc hca ha)
  have hr : 0<1-a := sub_pos.mpr ha
  have ht : 0<1-c := by linarith
  unfold Qtail
  positivity

/-- A coarse global Q bound suffices in the close-contact case. -/
theorem Qtail_le_one {a c : ℝ} (hc : (1/2:ℝ)≤c) (hca : c≤a) (ha : a<1) : Qtail a c≤1 := by
  have hc0 : 0≤c := by linarith
  have hc1 := hca.trans_lt ha
  have hr : 0<1-a := by linarith
  have ht : 0<1-c := by linarith
  have hp : 0<1+c := by linarith
  have hB := biasB_pos_wide (by linarith : -1<c) hc1
  have hBl := (Certificates.Mixed.log_two_gt_69.le).trans (biasB_ge_log_two hc0 hc1)
  have hprod : 1≤(1+c)*biasB c := by
    nlinarith [mul_nonneg (show 0≤c-1/2 by linarith) hB.le]
  have hratio : (a-c)/((1-a)*(1+c))≤(a-c)*biasB c/(1-a) := by
    apply (div_le_div_iff₀ (mul_pos hr hp) hr).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hprod)]
  have hd := (A_sub_upper hc0 hca ha).trans hratio
  have hd' : (A a-A c)/biasB c≤(a-c)/(1-a) := by
    apply (div_le_iff₀ hB).mpr
    convert! hd using 1; ring
  unfold Qtail
  calc
    _ ≤ ((1-a)/(1-c))*(1+(a-c)/(1-a)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hd') (div_nonneg hr.le ht.le)
    _ = 1 := by field_simp; ring

theorem mul_log_small_general {x d : ℝ} (hx : 0<x) (hd : x≤d)
    (hlog : Real.log (2/d)<8) : x*Real.log (2/x)<8*d := by
  have hd0 := hx.trans_le hd
  have hq : 0<d/x := div_pos hd0 hx
  have heq : (2:ℝ)/x=(2/d)*(d/x) := by field_simp
  have h := Real.log_le_sub_one_of_pos hq
  have hl : Real.log (2/x)<7+d/x := by
    rw [heq,Real.log_mul (div_pos (by norm_num) hd0).ne' hq.ne']
    linarith
  have hm := mul_lt_mul_of_pos_left hl hx
  have hs : x*(7+d/x)=7*x+d := by field_simp
  rw [hs] at hm
  linarith

theorem sqrt_A_bound {a : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1) :
    Real.sqrt (1-a)*A a≤32/125 := by
  have hr : 0<1-a := sub_pos.mpr ha1
  have hw : 0<Real.sqrt (1-a) := Real.sqrt_pos.mpr hr
  have hw2 := Real.sq_sqrt hr.le
  have hwu : Real.sqrt (1-a)≤(4/125:ℝ) := by nlinarith
  have hp : 0<(1+a)/(1-a) := div_pos (by linarith) hr
  have hq : (1+a)/(1-a)≤(2/Real.sqrt (1-a))^2 := by
    rw [div_pow,hw2]
    exact div_le_div_of_nonneg_right (by nlinarith) hr.le
  have hl := Real.log_le_log hp hq
  rw [Real.log_pow] at hl
  have hA : A a≤Real.log (2/Real.sqrt (1-a)) := by
    unfold A
    norm_num at hl
    linarith
  have hendpoint : Real.log ((2:ℝ)/(4/125))<8 := by
    exact (Real.log_lt_log (by norm_num) (by norm_num : (2:ℝ)/(4/125)<2000)).trans
      HighBiasLog.log_two_thousand_lt
  have hb := (mul_le_mul_of_nonneg_left hA hw.le).trans (mul_log_small_general hw hwu hendpoint).le
  norm_num at hb
  exact hb

theorem Qtail_le_half_of_sqrt {a c : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1)
    (hc : (1/2:ℝ)≤c) (hca : c≤a) (hcase : Real.sqrt (1-a)≤1-c) : Qtail a c≤1/2 := by
  have hr : 0<1-a := sub_pos.mpr ha1
  have ht : 0<1-c := by linarith
  have hw := Real.sqrt_pos.mpr hr
  have hw2 := Real.sq_sqrt hr.le
  have hwu : Real.sqrt (1-a)≤(4/125:ℝ) := by nlinarith
  have hc0 : 0≤c := by linarith
  have hc1 : c<1 := by linarith
  have hB := biasB_pos_wide (by linarith : -1<c) hc1
  have hBl := biasB_ge_log_two hc0 hc1
  have hA := HighBiasLog.A_nonneg ha ha1
  have hC : 0≤A c := hc0.trans (SmallMean.A_lower hc0 hc1)
  have hdiff : 0≤A a-A c := sub_nonneg.mpr (A_mono hc0 hca ha1)
  have hratio : (1-a)/(1-c)≤Real.sqrt (1-a) := by
    apply (div_le_iff₀ ht).mpr
    nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hcase)]
  have hf : (A a-A c)/biasB c≤A a/Real.log 2 :=
    (div_le_div_of_nonneg_right (by linarith) hB.le).trans
      (div_le_div_of_nonneg_left hA log_two_pos hBl)
  have hbound : Qtail a c≤Real.sqrt (1-a)*(1+A a/Real.log 2) := by
    exact mul_le_mul hratio (add_le_add le_rfl hf) (by positivity) hw.le
  have hlast : Real.sqrt (1-a)*(1+A a/Real.log 2)≤
      (4/125:ℝ)+(32/125)/Real.log 2 := by
    have h := div_le_div_of_nonneg_right (sqrt_A_bound ha ha1) log_two_pos.le
    rw [show Real.sqrt (1-a)*(1+A a/Real.log 2)=
      Real.sqrt (1-a)+Real.sqrt (1-a)*A a/Real.log 2 by ring]
    exact add_le_add hwu h
  have hsmall : (4/125:ℝ)+(32/125)/Real.log 2≤1/2 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤32/125)
      (by norm_num : (0:ℝ)<69/100) Certificates.Mixed.log_two_gt_69.le
    norm_num at h
    linarith
  exact hbound.trans (hlast.trans hsmall)

theorem ratio_le_small_of_sqrt {a c : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1)
    (hca : c≤a) (hcase : Real.sqrt (1-a)≤1-c) : (1-a)/(1-c)≤4/125 := by
  have hr : 0<1-a := sub_pos.mpr ha1
  have ht : 0<1-c := by linarith
  have hw := Real.sqrt_pos.mpr hr
  have hw2 := Real.sq_sqrt hr.le
  have hwu : Real.sqrt (1-a)≤(4/125:ℝ) := by nlinarith
  have hratio : (1-a)/(1-c)≤Real.sqrt (1-a) := by
    apply (div_le_iff₀ ht).mpr
    nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hcase)]
  exact hratio.trans hwu

theorem biasB_ge_half_log {c : ℝ} (hc : 0≤c) (hc1 : c<1) :
    Real.log (2/(1-c))/2≤biasB c := by
  have hm : 0<1-c := sub_pos.mpr hc1
  have hp : 0<1+c := by linarith
  have hlog := Real.log_le_log hp (show 1+c≤2 by linarith)
  unfold biasB
  rw [show 1-c*c=(1-c)*(1+c) by ring,Real.log_mul hm.ne' hp.ne',
    Real.log_div (by norm_num) hm.ne']
  linarith

theorem biasB_large_lower {c : ℝ} (hc : 0≤c) (hc1 : c<1) (ht : 1-c≤1/16) :
    (69/40:ℝ)≤biasB c := by
  have hm : 0<1-c := sub_pos.mpr hc1
  have hratio : (32:ℝ)≤2/(1-c) := by
    apply (le_div_iff₀ hm).mpr
    linarith
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<32) hratio
  rw [show (32:ℝ)=2^5 by norm_num,Real.log_pow] at hlog
  have hb := biasB_ge_half_log hc hc1
  have hl := Certificates.Mixed.log_two_gt_69
  norm_num at hlog
  linarith

end
end GeneralCK.Reflection.HighBiasCases

end


