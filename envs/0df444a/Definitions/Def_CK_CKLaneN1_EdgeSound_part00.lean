-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeSound_part00
-- name    : CK_CKLaneN1_EdgeSound_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:23:40.260053+00:00
-- url     : https://prove2.me/theorems/b34b0c2e-d8ce-462e-aeed-7f975a72d937
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeSound (part 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeSound (part 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeSound (part 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeSound (part 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeSound (part 1 of 5).lean)

import Definitions.Def_CK_CKLaneN1_EdgeAlg
import Definitions.Def_CK_CKLaneN1_EdgeCheck
import Definitions.Def_CK_CKLaneN1_CapTail

set_option autoImplicit false

/-!
# Lane N1: soundness of the leftEdge box checker

`edgeOK_sound`: if `edgeOK B w = true` then for every `(t, z)` in the box with `0 < t < 1`,
`0 < z < 1`, the cutoff-edge value `cPG a (S - a) (H a) (H b)` at `a = m(1-t)`,
`b = m(1 + t(2z-1))` is positive.
-/

namespace CKLaneN1.Edge

open GeneralCK CKLaneE.FP CKLaneN1.Capital Set

/-! ## Elementary helpers -/

theorem rle {x y : ℚ} (h : x ≤ y) : (x : ℝ) ≤ y := by exact_mod_cast h
theorem rlt {x y : ℚ} (h : x < y) : (x : ℝ) < y := by exact_mod_cast h
theorem rpos {x : ℚ} (h : 0 < x) : (0 : ℝ) < (x : ℝ) := by exact_mod_cast h
theorem rnn {x : ℚ} (h : 0 ≤ x) : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h

/-- A bilinear function `α + β t + γ t z` is bounded below by any common lower bound of its
four corner values. -/
theorem bilin_ge {α β γ t0 t1 z0 z1 t z L : ℝ} (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (hz0 : z0 ≤ z) (hz1 : z ≤ z1)
    (h00 : L ≤ α + β * t0 + γ * t0 * z0) (h01 : L ≤ α + β * t0 + γ * t0 * z1)
    (h10 : L ≤ α + β * t1 + γ * t1 * z0) (h11 : L ≤ α + β * t1 + γ * t1 * z1) :
    L ≤ α + β * t + γ * t * z := by
  have hA : L ≤ α + β * t + γ * t * z0 := by
    rcases le_total 0 (β + γ * z0) with hq | hq
    · nlinarith [mul_nonneg hq (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hq) (sub_nonneg.mpr ht1)]
  have hB : L ≤ α + β * t + γ * t * z1 := by
    rcases le_total 0 (β + γ * z1) with hq | hq
    · nlinarith [mul_nonneg hq (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hq) (sub_nonneg.mpr ht1)]
  rcases le_total 0 (γ * t) with hq | hq
  · nlinarith [mul_nonneg hq (sub_nonneg.mpr hz0)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hq) (sub_nonneg.mpr hz1)]

theorem bilin_le {α β γ t0 t1 z0 z1 t z U : ℝ} (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (hz0 : z0 ≤ z) (hz1 : z ≤ z1)
    (h00 : α + β * t0 + γ * t0 * z0 ≤ U) (h01 : α + β * t0 + γ * t0 * z1 ≤ U)
    (h10 : α + β * t1 + γ * t1 * z0 ≤ U) (h11 : α + β * t1 + γ * t1 * z1 ≤ U) :
    α + β * t + γ * t * z ≤ U := by
  have := bilin_ge (α := -α) (β := -β) (γ := -γ) (L := -U) ht0 ht1 hz0 hz1
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

theorem H_sub_le_J {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    H b - H a ≤ J a * (b - a) := by
  have hd : ∀ x, 0 < x → x < 1 → HasDerivAt (fun x => J a * x - H x) (J a - J x) x := by
    intro x hx hx1
    have h1 := ((hasDerivAt_id x).const_mul (J a)).sub (Comparison.hasDerivAt_H hx hx1)
    refine (h1.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
    ring
  have hmono : MonotoneOn (fun x => J a * x - H x) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hd x (ha.trans_le hx.1) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (ha.trans hx.1) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (ha.trans hx.1) (by linarith [hx.2])).deriv]
      have := J_anti ha hx.1.le (by linarith [hx.2])
      linarith
  have hm := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only at hm
  nlinarith

/-! ## One-time constants -/


end CKLaneN1.Edge


