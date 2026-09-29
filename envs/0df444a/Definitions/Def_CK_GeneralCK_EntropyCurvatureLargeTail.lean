-- Prove2me | Definitions.Def_CK_GeneralCK_EntropyCurvatureLargeTail
-- name    : CK_GeneralCK_EntropyCurvatureLargeTail
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:40:36.992994+00:00
-- url     : https://prove2.me/theorems/b4a62cdd-0ed0-4c9f-855e-ed10984fb4e2
-- title:
--   Courtade–Kumar proof module `GeneralCK.EntropyCurvatureLargeTail` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EntropyCurvatureLargeTail` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EntropyCurvatureLargeTail` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EntropyCurvatureLargeTail (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyCurvatureLargeTail.lean)

import Definitions.Def_CK_GeneralCK_EntropyCurvatureDefs

namespace GeneralCK.EntropyCurvature
open Certificates.Mixed

theorem xi_eq_log (v : ℝ) : xi v = Real.log ((1-v)/v)/2 := by
  unfold xi J
  field_simp

theorem kap_sub_xi {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    kap v-xi v = -Real.log (1-v) := by
  rw [xi_eq_log,kap,Real.log_mul hv.ne' (by linarith),
    Real.log_div (by linarith) hv.ne']
  ring

theorem hn_eq_kap_sub_xi {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    hn v = kap v-xi v*(1-2*v) := by
  have h := kap_identity hv hv'
  unfold xi
  linarith

theorem xi_large {v : ℝ} (hv : 0 < v) (hu : v ≤ 1/100) : 2 ≤ xi v := by
  have hratio : 84 ≤ (1-v)/v := (le_div_iff₀ hv).mpr (by linarith)
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 84) hratio
  have h84 : Real.log (84:ℝ) = 2*Real.log 2+Real.log 21 := by
    rw [show (84:ℝ) = 2^2*21 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [h84] at hl
  rw [xi_eq_log]
  linarith [log_twenty_one_gt_three,log_two_gt_69]

/-- The large-logit tail uses only log(1/(1-v)) <= v/(1-v).
No exponential evaluation or endpoint series certificate is required. -/
theorem large_tail {v : ℝ} (hv : 0 < v) (hu : v ≤ 1/100) :
    0 < P v ∧ 0 < R v := by
  let x := xi v
  let r := 1-2*v
  let K := kap v
  let c := K-x
  let N := x*(1+r^2)-r
  let C := 2*K-r^2
  let h := K-x*r
  have hv1 : v < 1 := by linarith
  have hvhalf : v < 1/2 := by linarith
  have hvc : 0 < 1-v := by linarith
  have hx : 2 ≤ x := xi_large hv hu
  have hx0 : 0 < x := by linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrlo : 49/50 ≤ r := by dsimp [r]; linarith
  have hnu : 0 < 1-r^2 := by nlinarith only [hr,hr1]
  have hc_eq : c = -Real.log (1-v) := kap_sub_xi hv hv1
  have hc : 0 < c := by
    rw [hc_eq]
    exact neg_pos.mpr (Real.log_neg hvc (by linarith))
  have hcupper : c*(1-v) ≤ v := by
    have ht := Real.log_le_sub_one_of_pos (inv_pos.mpr hvc)
    rw [Real.log_inv] at ht
    rw [← hc_eq] at ht
    have hm := mul_le_mul_of_nonneg_right ht hvc.le
    have heq : ((1-v)⁻¹-1)*(1-v) = v := by
      rw [sub_mul,inv_mul_cancel₀ hvc.ne',one_mul]
      ring
    rwa [heq] at hm
  have hKx : x ≤ K := by dsimp [c] at hc; linarith
  have hK : 2 ≤ K := hx.trans hKx
  have hK0 : 0 < K := by linarith
  have hN : 0 < N := by
    have hp := mul_nonneg hx0.le (sq_nonneg r)
    dsimp [N]; nlinarith only [hp,hx,hr1]
  have hC : 0 < C := by dsimp [C]; nlinarith only [hK,hnu]
  have hh : 0 < h := by
    rw [show h = hn v from (hn_eq_kap_sub_xi hv hv1).symm,hn_eq_H_mul_log]
    exact mul_pos (H_pos hv hv1) log_two_pos
  have hvcube : v^3 ≤ 1 := by
    have ht := pow_le_pow_left₀ hv.le hv1.le 3
    simpa using ht
  have hpoly : 0 < 11-28*v+24*v^2-8*v^3 := by
    nlinarith only [hvcube,hu,sq_nonneg v]
  have hM : 0 < N-r^2*C := by
    have h₁ : 0 ≤ (x-2)*(1-r^2)*(1-v) :=
      mul_nonneg (mul_nonneg (by linarith) hnu.le) hvc.le
    have h₂ : 0 ≤ 2*r^2*(v-c*(1-v)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hcupper)
    have h₃ : 0 < 2*v^2*(11-28*v+24*v^2-8*v^3) := by positivity
    have heq : (1-v)*(N-r^2*C) = 2*v^2*(11-28*v+24*v^2-8*v^3)
        +(x-2)*(1-r^2)*(1-v)+2*r^2*(v-c*(1-v)) := by
      dsimp [N,C,r,c]
      ring
    have hm : 0 < (1-v)*(N-r^2*C) := by rw [heq]; linarith
    exact pos_of_mul_pos_right hm hvc.le
  have hP : 0 < P v := by
    have hpow : 0 ≤ K^3-x^3 := sub_nonneg.mpr (pow_le_pow_left₀ hx0.le hKx 3)
    have h₁ := mul_nonneg hpow hN.le
    have h₂ : 0 < x^3*(N-r^2*C) := mul_pos (pow_pos hx0 3) hM
    have heq : P v = (K^3-x^3)*N+x^3*(N-r^2*C) := by
      dsimp [P,polyP,K,x,N,C,r]
      ring
    rw [heq]; linarith
  have hR : 0 < R v := by
    have hhnu : 0 < 2*h-x*(1-r^2) := by
      have heq : 2*h-x*(1-r^2) = 2*c+x*(1-r)^2 := by dsimp [h,c]; ring
      rw [heq]
      positivity
    have hcoef : 0 < K*(4*r-2)-3*r := by
      have hp := mul_nonneg (show 0 ≤ K-2 by linarith) (show 0 ≤ 4*r-2 by linarith)
      nlinarith only [hp,hrlo]
    have h₁ := mul_nonneg (mul_nonneg (mul_nonneg hhnu.le hK0.le) hr.le) hC.le
    have h₂ := mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ 2*(1-r^2) by linarith) hK0.le) hh.le) hC.le
    have h₃ : 0 ≤ 2*K*h*r^4 := by positivity
    have h₄ : 0 < h*r*C*(K*(4*r-2)-3*r) := by positivity
    have heq : R v = (2*h-x*(1-r^2))*K*r*C+2*(1-r^2)*K*h*C
        +2*K*h*r^4+h*r*C*(K*(4*r-2)-3*r) := by
      dsimp [R,polyR,h,C,r,K,x]
      ring
    rw [heq]; linarith
  exact ⟨hP,hR⟩

end GeneralCK.EntropyCurvature


