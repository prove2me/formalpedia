-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Convex
-- name    : CK_CKLaneN4_LU_Convex
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:01:25.450658+00:00
-- url     : https://prove2.me/theorems/e422a2cd-c25c-4130-86b0-698ee65e51e3
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Convex` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Convex` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Convex` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Convex (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Convex.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperRadialReduction
import Definitions.Def_CK_GeneralCK_PerspectiveCurve
import Definitions.Def_CK_GeneralCK_RadialConvexity
import Definitions.Def_CK_GeneralCK_RadialContact
import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Definitions.Def_CK_GeneralCK_ProfileConvexity
import Definitions.Def_CK_GeneralCK_EtaMonotone
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Mathlib.Analysis.Convex.Deriv

-- ===== source module CKLaneN4.LU.Convex =====
section
/-
Lane N4b — convex/concave split of the left-upper cap value (analytic core).

  Gexpr a b = Cfun a b + Vfun a b,   h = hAvg a b = (H a + H b)/2,
  Cfun a b = interiorCost a b + 2 F(1/2 - a, h) + kfun b / 2      (convex along segments)
  Vfun a b = - F(b - a, h) - eta h                                 (concave along segments)
  kfun b   = (1 - 2b) J b                       (= eta (H b) for 0 < b ≤ 1/2).

Ingredients (all corpus): joint convexity of F (`F_convex_combination`), F antitone in the entropy
argument (`radialContact_mono_entropy`, `J_antitone`), concavity of H (`H_concaveOn_unit`),
convexity/antitonicity of eta (`Scalar.eta_convexOn_Ioc`, `eta_antitoneOn`), and the perspective of
`x log x` (Mathlib `Real.convexOn_mul_log`) for interiorCost = [ω(b,a) + ω(1-a,1-b)]/(2 log 2) and
kfun b = ω(1-b,b)/log 2 with ω(x,y) = (x-y)(log x - log y).
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK Set

noncomputable def hAvg (a b : ℝ) : ℝ := (H a + H b) / 2
noncomputable def kfun (b : ℝ) : ℝ := (1 - 2 * b) * J b
noncomputable def Cfun (a b : ℝ) : ℝ :=
  interiorCost a b + 2 * F (1 / 2 - a) (hAvg a b) + kfun b / 2
noncomputable def Vfun (a b : ℝ) : ℝ := -F (b - a) (hAvg a b) - eta (hAvg a b)
noncomputable def Gexpr (a b : ℝ) : ℝ := Cfun a b + Vfun a b

/-! ### Elementary helpers -/

theorem comb_pos {y0 y1 μ : ℝ} (hy0 : 0 < y0) (hy1 : 0 < y1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    0 < (1 - μ) * y0 + μ * y1 := by
  rcases lt_or_ge μ 1 with h | h
  · have := mul_pos (sub_pos.2 h) hy0
    nlinarith [mul_nonneg hμ0 hy1.le]
  · have : μ = 1 := le_antisymm hμ1 h
    subst this
    simp [hy1]

theorem comb_nonneg {y0 y1 μ : ℝ} (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    0 ≤ (1 - μ) * y0 + μ * y1 := by
  have := mul_nonneg (sub_nonneg.2 hμ1) hy0
  nlinarith [mul_nonneg hμ0 hy1]

theorem comb_le {y0 y1 m μ : ℝ} (hy0 : y0 ≤ m) (hy1 : y1 ≤ m) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (1 - μ) * y0 + μ * y1 ≤ m := by
  have h1 := mul_le_mul_of_nonneg_left hy0 (sub_nonneg.2 hμ1)
  have h2 := mul_le_mul_of_nonneg_left hy1 hμ0
  nlinarith

theorem comb_lt {y0 y1 m μ : ℝ} (hy0 : y0 < m) (hy1 : y1 < m) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (1 - μ) * y0 + μ * y1 < m := by
  have := comb_pos (sub_pos.2 hy0) (sub_pos.2 hy1) hμ0 hμ1
  nlinarith

/-! ### Perspective convexity -/

theorem persp_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Ici 0) φ) {x0 x1 y0 y1 μ : ℝ}
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hy0 : 0 < y0) (hy1 : 0 < y1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ((1 - μ) * y0 + μ * y1) * φ (((1 - μ) * x0 + μ * x1) / ((1 - μ) * y0 + μ * y1)) ≤
      (1 - μ) * (y0 * φ (x0 / y0)) + μ * (y1 * φ (x1 / y1)) := by
  set Y := (1 - μ) * y0 + μ * y1 with hY
  have hYpos : 0 < Y := comb_pos hy0 hy1 hμ0 hμ1
  have hw0 : 0 ≤ (1 - μ) * y0 / Y := div_nonneg (mul_nonneg (sub_nonneg.2 hμ1) hy0.le) hYpos.le
  have hw1 : 0 ≤ μ * y1 / Y := div_nonneg (mul_nonneg hμ0 hy1.le) hYpos.le
  have hsum : (1 - μ) * y0 / Y + μ * y1 / Y = 1 := by
    rw [← add_div, ← hY, div_self hYpos.ne']
  have hc := hφ.2 (show x0 / y0 ∈ Ici (0 : ℝ) from div_nonneg hx0 hy0.le)
    (show x1 / y1 ∈ Ici (0 : ℝ) from div_nonneg hx1 hy1.le) hw0 hw1 hsum
  simp only [smul_eq_mul] at hc
  have harg : (1 - μ) * y0 / Y * (x0 / y0) + μ * y1 / Y * (x1 / y1) =
      ((1 - μ) * x0 + μ * x1) / Y := by
    field_simp
  rw [harg] at hc
  have hm := mul_le_mul_of_nonneg_left hc hYpos.le
  calc Y * φ (((1 - μ) * x0 + μ * x1) / Y)
      ≤ Y * ((1 - μ) * y0 / Y * φ (x0 / y0) + μ * y1 / Y * φ (x1 / y1)) := hm
    _ = (1 - μ) * (y0 * φ (x0 / y0)) + μ * (y1 * φ (x1 / y1)) := by
        field_simp

/-- `ω(x,y) = (x - y)(log x - log y)`, the symmetrised Kullback–Leibler kernel. -/
noncomputable def omega (x y : ℝ) : ℝ := (x - y) * (Real.log x - Real.log y)

theorem omega_eq_persp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    omega x y = y * ((x / y) * Real.log (x / y)) + x * ((y / x) * Real.log (y / x)) := by
  unfold omega
  rw [Real.log_div hx.ne' hy.ne', Real.log_div hy.ne' hx.ne']
  field_simp
  ring

theorem omega_seg {x0 y0 x1 y1 μ : ℝ} (hx0 : 0 < x0) (hy0 : 0 < y0) (hx1 : 0 < x1)
    (hy1 : 0 < y1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    omega ((1 - μ) * x0 + μ * x1) ((1 - μ) * y0 + μ * y1) ≤
      (1 - μ) * omega x0 y0 + μ * omega x1 y1 := by
  have hX := comb_pos hx0 hx1 hμ0 hμ1
  have hY := comb_pos hy0 hy1 hμ0 hμ1
  rw [omega_eq_persp hX hY, omega_eq_persp hx0 hy0, omega_eq_persp hx1 hy1]
  have h1 := persp_le Real.convexOn_mul_log hx0.le hx1.le hy0 hy1 hμ0 hμ1
  have h2 := persp_le Real.convexOn_mul_log hy0.le hy1.le hx0 hx1 hμ0 hμ1
  nlinarith [h1, h2]

theorem interiorCost_eq_omega {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    interiorCost a b = (omega b a + omega (1 - a) (1 - b)) / (2 * Real.log 2) := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold interiorCost J omega
  rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) hb.ne']
  field_simp
  ring

theorem kfun_eq_omega {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    kfun b = omega (1 - b) b / Real.log 2 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold kfun J omega
  rw [Real.log_div (by linarith) hb.ne']
  field_simp
  ring

theorem interiorCost_seg {a0 b0 a1 b1 μ : ℝ} (ha0 : 0 < a0) (ha0' : a0 < 1) (hb0 : 0 < b0)
    (hb0' : b0 < 1) (ha1 : 0 < a1) (ha1' : a1 < 1) (hb1 : 0 < b1) (hb1' : b1 < 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    interiorCost ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) ≤
      (1 - μ) * interiorCost a0 b0 + μ * interiorCost a1 b1 := by
  have hA := comb_pos ha0 ha1 hμ0 hμ1
  have hA' := comb_lt ha0' ha1' hμ0 hμ1
  have hB := comb_pos hb0 hb1 hμ0 hμ1
  have hB' := comb_lt hb0' hb1' hμ0 hμ1
  rw [interiorCost_eq_omega hA hA' hB hB', interiorCost_eq_omega ha0 ha0' hb0 hb0',
    interiorCost_eq_omega ha1 ha1' hb1 hb1']
  have hL : 0 < 2 * Real.log 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have e1 := omega_seg hb0 ha0 hb1 ha1 hμ0 hμ1
  have e2 := omega_seg (sub_pos.2 ha0') (sub_pos.2 hb0') (sub_pos.2 ha1') (sub_pos.2 hb1') hμ0 hμ1
  have r1 : 1 - ((1 - μ) * a0 + μ * a1) = (1 - μ) * (1 - a0) + μ * (1 - a1) := by ring
  have r2 : 1 - ((1 - μ) * b0 + μ * b1) = (1 - μ) * (1 - b0) + μ * (1 - b1) := by ring
  rw [r1, r2]
  have key : omega ((1 - μ) * b0 + μ * b1) ((1 - μ) * a0 + μ * a1) +
      omega ((1 - μ) * (1 - a0) + μ * (1 - a1)) ((1 - μ) * (1 - b0) + μ * (1 - b1)) ≤
      (1 - μ) * (omega b0 a0 + omega (1 - a0) (1 - b0)) +
        μ * (omega b1 a1 + omega (1 - a1) (1 - b1)) := by nlinarith [e1, e2]
  calc (omega ((1 - μ) * b0 + μ * b1) ((1 - μ) * a0 + μ * a1) +
        omega ((1 - μ) * (1 - a0) + μ * (1 - a1)) ((1 - μ) * (1 - b0) + μ * (1 - b1))) /
          (2 * Real.log 2)
      ≤ ((1 - μ) * (omega b0 a0 + omega (1 - a0) (1 - b0)) +
          μ * (omega b1 a1 + omega (1 - a1) (1 - b1))) / (2 * Real.log 2) :=
        div_le_div_of_nonneg_right key hL.le
    _ = (1 - μ) * ((omega b0 a0 + omega (1 - a0) (1 - b0)) / (2 * Real.log 2)) +
          μ * ((omega b1 a1 + omega (1 - a1) (1 - b1)) / (2 * Real.log 2)) := by ring

theorem kfun_seg {b0 b1 μ : ℝ} (hb0 : 0 < b0) (hb0' : b0 < 1) (hb1 : 0 < b1) (hb1' : b1 < 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    kfun ((1 - μ) * b0 + μ * b1) ≤ (1 - μ) * kfun b0 + μ * kfun b1 := by
  have hB := comb_pos hb0 hb1 hμ0 hμ1
  have hB' := comb_lt hb0' hb1' hμ0 hμ1
  rw [kfun_eq_omega hB hB', kfun_eq_omega hb0 hb0', kfun_eq_omega hb1 hb1']
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e := omega_seg (sub_pos.2 hb0') hb0 (sub_pos.2 hb1') hb1 hμ0 hμ1
  have r : 1 - ((1 - μ) * b0 + μ * b1) = (1 - μ) * (1 - b0) + μ * (1 - b1) := by ring
  rw [r]
  calc omega ((1 - μ) * (1 - b0) + μ * (1 - b1)) ((1 - μ) * b0 + μ * b1) / Real.log 2
      ≤ ((1 - μ) * omega (1 - b0) b0 + μ * omega (1 - b1) b1) / Real.log 2 :=
        div_le_div_of_nonneg_right e hL.le
    _ = (1 - μ) * (omega (1 - b0) b0 / Real.log 2) + μ * (omega (1 - b1) b1 / Real.log 2) := by
        ring

/-! ### F, eta and the average entropy -/

theorem F_anti_h {z h h' : ℝ} (hz : 0 ≤ z) (hh : 0 < h) (hhh : h ≤ h') : F z h' ≤ F z h := by
  rcases eq_or_lt_of_le hz with hz0 | hz
  · subst hz0; simp [F]
  have hc := radialContact_mono_entropy hz hh hhh
  have hp := radialContact_pos hz hh
  have hl' := radialContact_lt_half hz (hh.trans_le hhh)
  have hJ := J_antitone hp hl'.le hc
  simp only [F, hz.ne', if_false]
  exact mul_le_mul_of_nonneg_left hJ hz.le

theorem F_seg {z0 z1 h0 h1 hmid μ : ℝ} (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1) (hh0 : 0 < h0)
    (hh1 : 0 < h1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hm : (1 - μ) * h0 + μ * h1 ≤ hmid) :
    F ((1 - μ) * z0 + μ * z1) hmid ≤ (1 - μ) * F z0 h0 + μ * F z1 h1 := by
  have hpos := comb_pos hh0 hh1 hμ0 hμ1
  have hz := comb_nonneg hz0 hz1 hμ0 hμ1
  calc F ((1 - μ) * z0 + μ * z1) hmid ≤ F ((1 - μ) * z0 + μ * z1) ((1 - μ) * h0 + μ * h1) :=
        F_anti_h hz hpos hm
    _ ≤ (1 - μ) * F z0 h0 + μ * F z1 h1 :=
        F_convex_combination (sub_nonneg.2 hμ1) hμ0 (by ring) hz0 hz1 hh0 hh1

theorem hAvg_seg {a0 b0 a1 b1 μ : ℝ} (ha0 : 0 ≤ a0) (ha0' : a0 ≤ 1) (hb0 : 0 ≤ b0)
    (hb0' : b0 ≤ 1) (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1) (hb1 : 0 ≤ b1) (hb1' : b1 ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (1 - μ) * hAvg a0 b0 + μ * hAvg a1 b1 ≤ hAvg ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) := by
  have hA := H_concaveOn_unit.2 (show a0 ∈ Icc (0 : ℝ) 1 from ⟨ha0, ha0'⟩)
    (show a1 ∈ Icc (0 : ℝ) 1 from ⟨ha1, ha1'⟩) (sub_nonneg.2 hμ1) hμ0 (by ring)
  have hB := H_concaveOn_unit.2 (show b0 ∈ Icc (0 : ℝ) 1 from ⟨hb0, hb0'⟩)
    (show b1 ∈ Icc (0 : ℝ) 1 from ⟨hb1, hb1'⟩) (sub_nonneg.2 hμ1) hμ0 (by ring)
  simp only [smul_eq_mul] at hA hB
  unfold hAvg
  linarith

theorem eta_seg {h0 h1 hmid μ : ℝ} (hh0 : 0 < h0) (hh0' : h0 ≤ 1) (hh1 : 0 < h1) (hh1' : h1 ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hm : (1 - μ) * h0 + μ * h1 ≤ hmid) (hm1 : hmid ≤ 1) :
    eta hmid ≤ (1 - μ) * eta h0 + μ * eta h1 := by
  have hpos := comb_pos hh0 hh1 hμ0 hμ1
  have hle1 : (1 - μ) * h0 + μ * h1 ≤ 1 := comb_le hh0' hh1' hμ0 hμ1
  have h1' := eta_antitoneOn ⟨hpos, hle1⟩ ⟨hpos.trans_le hm, hm1⟩ hm
  have h2' := Scalar.eta_convexOn_Ioc.2 (show h0 ∈ Ioc (0 : ℝ) 1 from ⟨hh0, hh0'⟩)
    (show h1 ∈ Ioc (0 : ℝ) 1 from ⟨hh1, hh1'⟩) (sub_nonneg.2 hμ1) hμ0 (by ring)
  simp only [smul_eq_mul] at h2'
  linarith

/-! ### Domains -/

/-- Domain of the concave part (vertices may have `a = 0`). -/
def VDom (a b : ℝ) : Prop := 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 / 2 ∧ a < 1 / 2 ∧ 0 < b

/-- Domain of the convex part. -/
def CDom (a b : ℝ) : Prop := 0 < a ∧ a ≤ b ∧ b ≤ 1 / 2 ∧ a < 1 / 2

theorem CDom.vdom {a b : ℝ} (h : CDom a b) : VDom a b :=
  ⟨h.1.le, h.2.1, h.2.2.1, h.2.2.2, h.1.trans_le h.2.1⟩

theorem VDom_seg {a0 b0 a1 b1 μ : ℝ} (h0 : VDom a0 b0) (h1 : VDom a1 b1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ ≤ 1) : VDom ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) := by
  obtain ⟨a0n, ab0, b0h, a0h, b0p⟩ := h0
  obtain ⟨a1n, ab1, b1h, a1h, b1p⟩ := h1
  refine ⟨comb_nonneg a0n a1n hμ0 hμ1, ?_, comb_le b0h b1h hμ0 hμ1, comb_lt a0h a1h hμ0 hμ1,
    comb_pos b0p b1p hμ0 hμ1⟩
  have := mul_le_mul_of_nonneg_left ab0 (sub_nonneg.2 hμ1)
  have := mul_le_mul_of_nonneg_left ab1 hμ0
  linarith

theorem CDom_seg {a0 b0 a1 b1 μ : ℝ} (h0 : CDom a0 b0) (h1 : CDom a1 b1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ ≤ 1) : CDom ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) := by
  obtain ⟨a0p, ab0, b0h, a0h⟩ := h0
  obtain ⟨a1p, ab1, b1h, a1h⟩ := h1
  refine ⟨comb_pos a0p a1p hμ0 hμ1, ?_, comb_le b0h b1h hμ0 hμ1, comb_lt a0h a1h hμ0 hμ1⟩
  have := mul_le_mul_of_nonneg_left ab0 (sub_nonneg.2 hμ1)
  have := mul_le_mul_of_nonneg_left ab1 hμ0
  linarith

theorem hAvg_pos {a b : ℝ} (h : VDom a b) : 0 < hAvg a b := by
  obtain ⟨an, ab, bh, _, bp⟩ := h
  have hb := H_pos bp (by linarith)
  have ha := H_nonneg an (by linarith)
  unfold hAvg; linarith

theorem hAvg_le_one (a b : ℝ) : hAvg a b ≤ 1 := by
  have := H_le_one a; have := H_le_one b
  unfold hAvg; linarith

/-! ### Concavity of V and convexity of C along segments -/

theorem V_seg {a0 b0 a1 b1 μ : ℝ} (h0 : VDom a0 b0) (h1 : VDom a1 b1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ ≤ 1) :
    (1 - μ) * Vfun a0 b0 + μ * Vfun a1 b1 ≤ Vfun ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) := by
  have hm := hAvg_seg h0.1 (by linarith [h0.2.1, h0.2.2.1]) (h0.1.trans h0.2.1)
    (by linarith [h0.2.2.1]) h1.1 (by linarith [h1.2.1, h1.2.2.1]) (h1.1.trans h1.2.1)
    (by linarith [h1.2.2.1]) hμ0 hμ1
  have hp0 := hAvg_pos h0
  have hp1 := hAvg_pos h1
  have hF := F_seg (sub_nonneg.2 h0.2.1) (sub_nonneg.2 h1.2.1) hp0 hp1 hμ0 hμ1 hm
  have he := eta_seg hp0 (hAvg_le_one _ _) hp1 (hAvg_le_one _ _) hμ0 hμ1 hm (hAvg_le_one _ _)
  have rz : (1 - μ) * b0 + μ * b1 - ((1 - μ) * a0 + μ * a1) =
      (1 - μ) * (b0 - a0) + μ * (b1 - a1) := by ring
  unfold Vfun
  rw [rz]
  linarith

theorem C_seg {a0 b0 a1 b1 μ : ℝ} (h0 : CDom a0 b0) (h1 : CDom a1 b1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ ≤ 1) :
    Cfun ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) ≤ (1 - μ) * Cfun a0 b0 + μ * Cfun a1 b1 := by
  obtain ⟨a0p, ab0, b0h, a0h⟩ := h0
  obtain ⟨a1p, ab1, b1h, a1h⟩ := h1
  have hi := interiorCost_seg a0p (by linarith) (a0p.trans_le ab0) (by linarith) a1p (by linarith)
    (a1p.trans_le ab1) (by linarith) hμ0 hμ1
  have hk := kfun_seg (a0p.trans_le ab0) (by linarith) (a1p.trans_le ab1) (by linarith) hμ0 hμ1
  have hm := hAvg_seg a0p.le (by linarith) (a0p.le.trans ab0) (by linarith) a1p.le (by linarith)
    (a1p.le.trans ab1) (by linarith) hμ0 hμ1
  have hp0 := hAvg_pos (CDom.vdom ⟨a0p, ab0, b0h, a0h⟩)
  have hp1 := hAvg_pos (CDom.vdom ⟨a1p, ab1, b1h, a1h⟩)
  have hF := F_seg (show 0 ≤ 1 / 2 - a0 by linarith) (show 0 ≤ 1 / 2 - a1 by linarith) hp0 hp1
    hμ0 hμ1 hm
  have rz : 1 / 2 - ((1 - μ) * a0 + μ * a1) = (1 - μ) * (1 / 2 - a0) + μ * (1 / 2 - a1) := by ring
  unfold Cfun
  rw [rz]
  nlinarith [hi, hk, hF]

end CKLaneN4.LU

end


