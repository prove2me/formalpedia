-- Prove2me | Definitions.Def_CK_CKLaneP_SeamQBase
-- name    : CK_CKLaneP_SeamQBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:47:56.177051+00:00
-- url     : https://prove2.me/theorems/7e8778a0-c607-46e0-bb8a-c5fc27146d9f
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamQBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamQBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamQBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamQBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamQBase.lean)

import Definitions.Def_CK_CKLaneP_SeamNCore
import Definitions.Def_CK_CKLaneP_EvalDy
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction

-- ===== source module CKLaneP.SeamQBase =====
section
/-
Lane P — the normalized (N-mode) seam cell checker, case A (`t ≤ 1`, i.e. `q ≤ S/2`).

A cell is `p ∈ [p0, p1]`, `t = (q−p)/(S/2−p) ∈ [t0, t1] ⊆ [0, 1]` with dyadic witnesses
(`v = n/2^60`) for the log data.  `ncheckA c = true` (kernel-decided) implies, for every
stationary seam point `y*` of such `(p, q)`, `0 ≤ s(y*)` (`ncheckA_sound`).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-! ### Dyadic contact data -/

def dy (n : ℕ) : VD := VD.ofDy 60 64 20 l2c n

def dyq (n : ℕ) : ℚ := (n : ℚ) / ((2 ^ 60 : ℕ) : ℚ)

theorem dy_v (n : ℕ) : (dy n).v = dyq n := rfl

theorem dy_sound {n : ℕ} (h : VD.okDy 60 n = true) : (dy n).Sound :=
  VD.ofDy_sound l2c_sound h

def dhN : ℕ := 2 ^ 59

theorem dh_v : (dy dhN).v = 1 / 2 := by
  rw [dy_v]; unfold dyq dhN; norm_num

theorem dh_ok : VD.okDy 60 dhN = true := by
  unfold VD.okDy dhN; decide

/-! ### Bracket helpers -/

theorem contact_le_of_bracket {db : VD} (hdb : db.Sound) {x1 : ℚ} (hx1 : 0 < x1)
    (hB : 1 - 2 * db.v ≤ 2 * x1 * db.Hlo) {x : ℝ} (hx : (x1 : ℝ) ≤ x) :
    radialContact (2 * x) 1 ≤ (db.v : ℝ) := by
  have hx1R : (0 : ℝ) < x1 := by exact_mod_cast hx1
  have hx0 : 0 < x := lt_of_lt_of_le hx1R hx
  have hb0 : (0 : ℝ) < db.v := by exact_mod_cast hdb.1
  have hb1 : (db.v : ℝ) ≤ 1 / 2 := VD.cast_le_half hdb.2.1
  have hHlo := VD.Hlo_le hdb
  have hH0 : (0 : ℝ) ≤ ((db.Hlo : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ db.Hlo := by
      unfold VD.Hlo; apply div_nonneg (le_max_left _ _); unfold L2hiD; norm_num
    exact_mod_cast this
  have hBR : 1 - 2 * (db.v : ℝ) ≤ 2 * (x1 : ℝ) * ((db.Hlo : ℚ) : ℝ) := by exact_mod_cast hB
  have hres : 1 - 2 * (db.v : ℝ) ≤ 2 * x * ((db.Hlo : ℚ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right hx hH0
    linarith
  exact ZeroCapLeftStationaryThetaBracket.contact_upper_of_entropy_lower hx0 hb0.le hb1 hHlo hres

theorem contact_ge_of_bracket {da : VD} (hda : da.Sound) {x2 : ℚ}
    (hA : 2 * x2 * da.Hhi ≤ 1 - 2 * da.v) {x : ℝ} (hx0 : 0 < x) (hx : x ≤ (x2 : ℝ)) :
    (da.v : ℝ) ≤ radialContact (2 * x) 1 := by
  have ha0 : (0 : ℝ) < da.v := by exact_mod_cast hda.1
  have ha1 : (da.v : ℝ) ≤ 1 / 2 := VD.cast_le_half hda.2.1
  have hHhi := VD.le_Hhi hda
  have hH0 : 0 ≤ H (da.v : ℝ) := H_nonneg ha0.le (by linarith)
  have hAR : 2 * (x2 : ℝ) * ((da.Hhi : ℚ) : ℝ) ≤ 1 - 2 * (da.v : ℝ) := by exact_mod_cast hA
  have hres : 2 * x * ((da.Hhi : ℚ) : ℝ) ≤ 1 - 2 * (da.v : ℝ) := by
    have := mul_le_mul_of_nonneg_right hx (hH0.trans hHhi)
    linarith
  exact ZeroCapLeftStationaryThetaBracket.contact_lower_of_entropy_upper hx0 ha0.le ha1 hHhi hres

/-! ### Rational profile bounds -/

def PmaxQ (db : VD) : ℚ :=
  (1 + 1 / db.a1) ^ 2 * (1 - (1 - 2 * db.v) ^ 2 / db.a1) / (L2loD * (1 - db.v) ^ 2)

def PminQ (da db : VD) : ℚ :=
  (1 - 2 * db.v) * (1 + (1 - db.v) * (1 / da.b1)) ^ 2 * (1 - 1 / da.b1) /
    ((1 + db.v / 2) ^ 3 * L2hiD)

theorem PmaxQ_sound {db : VD} (hdb : db.Sound) (hvb : db.v ≤ 1 / 1000) (ha4 : 4 ≤ db.a1)
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ (db.v : ℝ)) : profile v ≤ ((PmaxQ db : ℚ) : ℝ) := by
  have hvbR : (db.v : ℝ) ≤ 1 / 1000 := by
    have : ((db.v : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := Rat.cast_le.mpr hvb
    simpa using this
  have ha4R : (4 : ℝ) ≤ (db.a1 : ℝ) := by exact_mod_cast ha4
  have hLb : (db.a1 : ℝ) ≤ -Real.log (db.v : ℝ) := hdb.2.2.1
  have h := profile_le_bracket hv0 hv hvbR ha4R hLb
  have hl2 := log2D_bounds
  have hvb0 : (0 : ℝ) < db.v := by exact_mod_cast hdb.1
  have hnum0 : 0 ≤ (1 + 1 / (db.a1 : ℝ)) ^ 2 * (1 - (1 - 2 * (db.v : ℝ)) ^ 2 / (db.a1 : ℝ)) := by
    apply mul_nonneg (sq_nonneg _)
    rw [sub_nonneg, div_le_one (by linarith)]
    nlinarith
  have hden : ((L2loD : ℚ) : ℝ) * (1 - (db.v : ℝ)) ^ 2 ≤ Real.log 2 * (1 - (db.v : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_right hl2.1 (sq_nonneg _)
  have hden0 : 0 < ((L2loD : ℚ) : ℝ) * (1 - (db.v : ℝ)) ^ 2 := by
    have : (0 : ℝ) < 1 - (db.v : ℝ) := by linarith
    have := VD.L2lo_pos
    positivity
  have h2 : (1 + 1 / (db.a1 : ℝ)) ^ 2 * (1 - (1 - 2 * (db.v : ℝ)) ^ 2 / (db.a1 : ℝ)) /
      (Real.log 2 * (1 - (db.v : ℝ)) ^ 2) ≤
      (1 + 1 / (db.a1 : ℝ)) ^ 2 * (1 - (1 - 2 * (db.v : ℝ)) ^ 2 / (db.a1 : ℝ)) /
      (((L2loD : ℚ) : ℝ) * (1 - (db.v : ℝ)) ^ 2) := div_le_div_of_nonneg_left hnum0 hden0 hden
  unfold PmaxQ
  push_cast
  linarith

theorem PminQ_sound {da db : VD} (hda : da.Sound) (hdb : db.Sound) (hvb : db.v ≤ 1 / 1000)
    (ha4 : 4 ≤ db.a1) (hb1 : 1 < da.b1)
    {v : ℝ} (hva : (da.v : ℝ) ≤ v) (hvb' : v ≤ (db.v : ℝ)) : ((PminQ da db : ℚ) : ℝ) ≤ profile v := by
  have hvbR : (db.v : ℝ) ≤ 1 / 1000 := by
    have : ((db.v : ℚ) : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := Rat.cast_le.mpr hvb
    simpa using this
  have ha4R : (4 : ℝ) ≤ (db.a1 : ℝ) := by exact_mod_cast ha4
  have hL4 : (4 : ℝ) ≤ -Real.log (db.v : ℝ) := le_trans ha4R hdb.2.2.1
  have hva0 : (0 : ℝ) < da.v := by exact_mod_cast hda.1
  have hLa : -Real.log (da.v : ℝ) ≤ (da.b1 : ℝ) := hda.2.2.2.1
  have h := profile_ge_bracket hva0 hva hvb' hvbR hLa hL4
  have hl2 := log2D_bounds
  have hb1R : (1 : ℝ) < (da.b1 : ℝ) := by exact_mod_cast hb1
  have hvb0 : (0 : ℝ) < db.v := by exact_mod_cast hdb.1
  have hnum0 : 0 ≤ (1 - 2 * (db.v : ℝ)) * (1 + (1 - (db.v : ℝ)) * (1 / (da.b1 : ℝ))) ^ 2 *
      (1 - 1 / (da.b1 : ℝ)) := by
    apply mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hden : (1 + (db.v : ℝ) / 2) ^ 3 * Real.log 2 ≤ (1 + (db.v : ℝ) / 2) ^ 3 * ((L2hiD : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hl2.2 (by positivity)
  have hden0 : 0 < (1 + (db.v : ℝ) / 2) ^ 3 * Real.log 2 := by
    have := log_two_pos; positivity
  have h2 := div_le_div_of_nonneg_left hnum0 hden0 hden
  unfold PminQ
  push_cast
  linarith

end CKLaneP

end


