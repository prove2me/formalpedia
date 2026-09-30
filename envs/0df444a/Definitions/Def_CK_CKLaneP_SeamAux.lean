-- Prove2me | Definitions.Def_CK_CKLaneP_SeamAux
-- name    : CK_CKLaneP_SeamAux
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:08:40.049111+00:00
-- url     : https://prove2.me/theorems/cb5bcf6d-84da-4e1a-b619-e8f36bda4301
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamAux` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamAux` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamAux` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamAux (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamAux.lean)

import Definitions.Def_CK_CKLaneP_ProfileBounds

-- ===== source module CKLaneP.SeamAux =====
section
/-
Lane P — small analytic helpers for the seam certificate.

* `log_one_add_ge`  : 2u/(2+u) ≤ log(1+u)                 (u ≥ 0)
* `H_sub_le_J`      : H b − H a ≤ J a·(b − a)             (0 < a ≤ b ≤ 1/2)
* `dipK_eq`         : dipK E y = y·(radialSlope v − J v),  v = radialContact y (E/2)
* `slopeGap_le`     : radialSlope v − J v ≤ (1 + 1/L)/log 2,  L = −log v
* `log_ge_sub_div`  : (r − 1)/r ≤ log r                     (r > 0)
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

theorem log_one_add_ge {u : ℝ} (hu : 0 ≤ u) : 2 * u / (2 + u) ≤ Real.log (1 + u) := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t => Real.log (1 + t) - 2 * t / (2 + t))
      (1 / (1 + t) - 4 / (2 + t) ^ 2) t := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have h1 : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + t)) t := by
      have := ((hasDerivAt_id t).const_add 1).log (by simp; linarith)
      simpa [one_div] using this
    have h2 : HasDerivAt (fun t : ℝ => 2 * t / (2 + t)) (4 / (2 + t) ^ 2) t := by
      have := ((hasDerivAt_id t).const_mul 2).div ((hasDerivAt_id t).const_add 2) (by simp; linarith)
      refine this.congr_deriv ?_
      simp only [id_eq]
      field_simp
      ring
    exact h1.sub h2
  have hcont : ContinuousOn (fun t => Real.log (1 + t) - 2 * t / (2 + t)) (Ici 0) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun t => Real.log (1 + t) - 2 * t / (2 + t)) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
    · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : (0 : ℝ) ≤ t := interior_subset ht
      rw [(hd t (interior_subset ht)).deriv]
      have e : 1 / (1 + t) - 4 / (2 + t) ^ 2 = t ^ 2 / ((1 + t) * (2 + t) ^ 2) := by
        field_simp
        ring
      rw [e]
      positivity
  have h := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hu) hu
  simp only [add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at h
  linarith

theorem log_ge_sub_div {r : ℝ} (hr : 0 < r) : (r - 1) / r ≤ Real.log r := by
  have h := Real.one_sub_inv_le_log_of_pos hr
  have e : (r - 1) / r = 1 - r⁻¹ := by field_simp
  rw [e]; exact h

theorem H_sub_le_J {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    H b - H a ≤ J a * (b - a) := by
  have hanti : AntitoneOn (fun t => H t - J a * t) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · intro t ht
      exact ((Comparison.hasDerivAt_H (lt_of_lt_of_le ha ht.1) (by linarith [ht.2])).sub
        ((hasDerivAt_id t).const_mul (J a))).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact ((Comparison.hasDerivAt_H (lt_of_lt_of_le ha ht.1.le) (by linarith [ht.2])).sub
        ((hasDerivAt_id t).const_mul (J a))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1.le
      have hd : HasDerivAt (fun t => H t - J a * t) (J t - J a * 1) t :=
        (Comparison.hasDerivAt_H ht0 (by linarith [ht.2])).sub ((hasDerivAt_id t).const_mul (J a))
      have hderv : deriv (fun t => H t - J a * t) t = J t - J a * 1 := hd.deriv
      rw [hderv]
      have := J_antitone ha (by linarith [ht.2]) ht.1.le
      linarith
  have := hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only at this
  linarith

theorem dipK_eq {E y : ℝ} (hE : 0 < E) (hy : 0 < y) :
    dipK E y = y * (radialSlope (radialContact y (E / 2)) - J (radialContact y (E / 2))) := by
  unfold dipK
  have hyE : 0 < y / E := div_pos hy hE
  rw [theta_eq_radialSlope hyE]
  have hc : radialContact (2 * (y / E)) 1 = radialContact y (E / 2) := by
    rw [radialContact_normalize_entropy y (show E / 2 ≠ 0 by positivity)]
    congr 1
    field_simp
  rw [hc]
  have hF : F y (E / 2) = y * J (radialContact y (E / 2)) := by
    unfold F; rw [if_neg hy.ne']
  rw [hF]
  ring

theorem slopeGap_le {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 2) (hL : 0 < -Real.log v) :
    radialSlope v - J v ≤ (1 + 1 / (-Real.log v)) / Real.log 2 := by
  have hv1' : v < 1 := by linarith
  obtain ⟨L, hLd⟩ : ∃ L, L = -Real.log v := ⟨_, rfl⟩
  obtain ⟨m, hmd⟩ : ∃ m, m = -Real.log (1 - v) := ⟨_, rfl⟩
  rw [← hLd]
  rw [← hLd] at hL
  have hm1 : v ≤ m := by rw [hmd]; exact (neg_log_one_sub_bounds hv0.le hv1).1
  have hm3 : (1 - v) * m ≤ v := by rw [hmd]; exact one_sub_mul_neg_log_le hv0.le hv1'
  have hhn : hn v = v * L + (1 - v) * m := by unfold hn; rw [hLd, hmd]; ring
  have hkap : kap v = (L + m) / 2 := by
    unfold kap; rw [Real.log_mul hv0.ne' (by linarith), hLd, hmd]; ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : 0 ≤ m := le_trans hv0.le hm1
  unfold radialSlope
  rw [hhn, hkap]
  have h1v : 0 < 1 - v := by linarith
  have hden : 0 < 2 * Real.log 2 * v * (1 - v) * ((L + m) / 2) := by positivity
  rw [add_sub_cancel_left, div_le_div_iff₀ hden hlog2]
  -- (1-2v)(vL + (1-v)m) log2 ≤ (1 + 1/L) * (2 log2 v (1-v) (L+m)/2)
  have hnum : (1 - 2 * v) * (v * L + (1 - v) * m) ≤ (1 - v) * (v * (L + 1)) := by
    have h2 : v * L + (1 - v) * m ≤ v * (L + 1) := by nlinarith
    have h3 : 0 ≤ v * L + (1 - v) * m := by positivity
    have h4 : (1 - 2 * v) ≤ (1 - v) := by linarith
    nlinarith
  have hrhs : (1 - v) * (v * (L + 1)) * Real.log 2 ≤
      (1 + 1 / L) * (2 * Real.log 2 * v * (1 - v) * ((L + m) / 2)) := by
    have e : (1 + 1 / L) * (2 * Real.log 2 * v * (1 - v) * ((L + m) / 2)) =
        (1 - v) * v * Real.log 2 * ((L + 1) * (L + m) / L) := by
      field_simp
    rw [e]
    have hLm : L + 1 ≤ (L + 1) * (L + m) / L := by
      rw [le_div_iff₀ hL]; nlinarith
    have hpos : 0 ≤ (1 - v) * v * Real.log 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hLm hpos]
  nlinarith [mul_le_mul_of_nonneg_right hnum hlog2.le]

end CKLaneP

end


