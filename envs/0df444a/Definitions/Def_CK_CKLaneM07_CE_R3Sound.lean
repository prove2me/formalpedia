-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Sound
-- name    : CK_CKLaneM07_CE_R3Sound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:24:24.412991+00:00
-- url     : https://prove2.me/theorems/d1600f67-3d6e-45bf-b622-4f30308a7a2d
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Sound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Sound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Sound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Sound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Sound.lean)

import Definitions.Def_CK_CKLaneM07_CE_R3Combine
import Definitions.Def_CK_CKLaneM07_CE_R3Check

-- ===== source module CKLaneM07.CE.R3Sound =====
section

/-!
# Lane M07 / CE-stat row 3: soundness of the box checker `r3BoxOK`

For every real point `(a, z, y)` of an accepted box with `0 < z < 1`, `0 < y`, writing
`b = a + z y`, `c = a + y`: if `y ≤ (H a + H b)/20` (i.e. `A ≤ 1/20`) then `0 ≤ gapLB (H a) (H b) c`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3

open GeneralCK GeneralCK.Certificates.Mixed Set CKLaneN1 CKLaneN1.Edge CKLaneN1.Capital CKLaneE.FP
  CKLaneM07.CE

/-! ## rational bounds at real points -/

theorem H_le_hi {x : ℝ} {q : ℚ} (hq : ptOk q = true) (hx0 : 0 ≤ x) (hxq : x ≤ q)
    (hq2 : (q : ℝ) ≤ 1 / 2) : H x ≤ ((Hhi q : ℚ) : ℝ) :=
  (H_mono hx0 hxq hq2).trans (H_bounds hq).2

theorem H_ge_lo {x : ℝ} {q : ℚ} (hq : ptOk q = true) (hqx : (q : ℝ) ≤ x) (hx2 : x ≤ 1 / 2) :
    ((Hlo q : ℚ) : ℝ) ≤ H x := by
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast (ptOk_pos hq).1.le
  exact (H_bounds hq).1.trans (H_mono hq0 hqx hx2)

/-- the real facts of a point in a geometrically valid box -/
structure PtBox (B : B3) (a z y : ℝ) : Prop where
  a0 : ((B.a0 : ℚ) : ℝ) ≤ a
  a1 : a ≤ ((B.a1 : ℚ) : ℝ)
  z0 : ((B.b0 : ℚ) : ℝ) ≤ z
  z1 : z ≤ ((B.b1 : ℚ) : ℝ)
  y0 : ((B.c0 : ℚ) : ℝ) ≤ y
  y1 : y ≤ ((B.c1 : ℚ) : ℝ)
  hz0 : 0 < z
  hz1 : z < 1
  hy : 0 < y
  pa0 : 0 < ((B.a0 : ℚ) : ℝ)
  pb0 : 0 ≤ ((B.b0 : ℚ) : ℝ)
  pc0 : 0 ≤ ((B.c0 : ℚ) : ℝ)
  hcHi : ((cHi B : ℚ) : ℝ) < 1 / 2
  b1le : ((B.b1 : ℚ) : ℝ) ≤ 1
  ok_a0 : ptOk B.a0 = true
  ok_a1 : ptOk B.a1 = true
  ok_bLo : ptOk (bLo B) = true
  ok_bHi : ptOk (bHi B) = true

theorem cHi_cast (B : B3) : ((cHi B : ℚ) : ℝ) = ((B.a1 : ℚ) : ℝ) + ((B.c1 : ℚ) : ℝ) := by
  unfold cHi; push_cast; ring

section pt

variable {B : B3} {a z y : ℝ} (P : PtBox B a z y)
include P

theorem PtBox.ha : 0 < a := lt_of_lt_of_le P.pa0 P.a0
theorem PtBox.zy_lo : ((B.b0 : ℚ) : ℝ) * ((B.c0 : ℚ) : ℝ) ≤ z * y :=
  mul_le_mul P.z0 P.y0 P.pc0 P.hz0.le
theorem PtBox.zy_hi : z * y ≤ ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) :=
  mul_le_mul P.z1 P.y1 P.hy.le (P.pb0.trans (P.z0.trans P.z1))
theorem PtBox.c_le : a + y ≤ ((cHi B : ℚ) : ℝ) := by rw [cHi_cast]; linarith [P.a1, P.y1]
theorem PtBox.c_half : a + y < 1 / 2 := lt_of_le_of_lt P.c_le P.hcHi
theorem PtBox.b_lo : ((bLo B : ℚ) : ℝ) ≤ a + z * y := by
  have : ((bLo B : ℚ) : ℝ) = ((B.a0 : ℚ) : ℝ) + ((B.b0 : ℚ) : ℝ) * ((B.c0 : ℚ) : ℝ) := by
    unfold bLo; push_cast; ring
  rw [this]; linarith [P.a0, P.zy_lo]
theorem PtBox.b_hi : a + z * y ≤ ((bHi B : ℚ) : ℝ) := by
  have : ((bHi B : ℚ) : ℝ) = ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) := by
    unfold bHi; push_cast; ring
  rw [this]; linarith [P.a1, P.zy_hi]
theorem PtBox.b_lt_c : a + z * y < a + y := by nlinarith [P.hz1, P.hy]
theorem PtBox.cfg : Cfg a (a + z * y) (a + y) :=
  ⟨P.ha, by nlinarith [P.hz0, P.hy], P.b_lt_c, P.c_half⟩
theorem PtBox.Ha_hi : H a ≤ ((Ha1 B : ℚ) : ℝ) := by
  unfold Ha1
  exact H_le_hi P.ok_a1 P.ha.le P.a1 (by linarith [P.hcHi, cHi_cast B, P.y1, P.hy, P.a1])
theorem PtBox.Ha_lo : ((Ha0 B : ℚ) : ℝ) ≤ H a := by
  unfold Ha0
  exact H_ge_lo P.ok_a0 P.a0 (by linarith [P.c_half, P.hy])
theorem PtBox.Hb_hi : H (a + z * y) ≤ ((Hb1 B : ℚ) : ℝ) := by
  unfold Hb1
  refine H_le_hi P.ok_bHi (by nlinarith [P.ha, P.hz0, P.hy]) P.b_hi ?_
  have : ((bHi B : ℚ) : ℝ) ≤ ((cHi B : ℚ) : ℝ) := by
    have e1 : ((bHi B : ℚ) : ℝ) = ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) := by
      unfold bHi; push_cast; ring
    rw [e1, cHi_cast B]
    have : ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) ≤ ((B.c1 : ℚ) : ℝ) := by
      have hc1 : 0 ≤ ((B.c1 : ℚ) : ℝ) := P.hy.le.trans P.y1
      nlinarith [P.b1le]
    linarith
  linarith [P.hcHi]
theorem PtBox.Hb_lo : ((Hb0 B : ℚ) : ℝ) ≤ H (a + z * y) := by
  unfold Hb0
  exact H_ge_lo P.ok_bLo P.b_lo (by linarith [P.b_lt_c, P.c_half])

end pt

end CKLaneM07.CE.R3

end


