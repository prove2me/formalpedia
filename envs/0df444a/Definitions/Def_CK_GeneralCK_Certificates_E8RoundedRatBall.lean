-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8RoundedRatBall
-- name    : CK_GeneralCK_Certificates_E8RoundedRatBall
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:37:17.330881+00:00
-- url     : https://prove2.me/theorems/d1d1f4b9-08b8-4b00-993a-8a967ce0f9f0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8RoundedRatBall` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8RoundedRatBall` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8RoundedRatBall` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8RoundedRatBall (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8RoundedRatBall.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8GaussianRatBall

-- ===== source module GeneralCK.Certificates.E8RoundedRatBall =====
section

/-! Sound fixed-denominator compression for E8 rational complex balls. -/

namespace GeneralCK.Certificates.E8RoundedRatBall

open E8GaussianRatBall

def floorGrid (D : ℕ) (q : ℚ) : ℚ := (q * D).floor / D
def ceilGrid (D : ℕ) (q : ℚ) : ℚ := (q * D).ceil / D

theorem floorGrid_le {D : ℕ} (hD : 0 < D) (q : ℚ) : floorGrid D q ≤ q := by
  rw [floorGrid, div_le_iff₀ (by exact_mod_cast hD)]
  exact_mod_cast Rat.floor_le (q * D)

theorem lt_floorGrid_add {D : ℕ} (hD : 0 < D) (q : ℚ) :
    q < floorGrid D q + 1 / D := by
  have h := Rat.lt_floor_add_one (q * D)
  unfold floorGrid
  calc
    q < ((q * D).floor + 1 : ℤ) / (D : ℚ) := by
      rw [lt_div_iff₀ (by exact_mod_cast hD)]
      exact_mod_cast h
    _ = (q * D).floor / D + 1 / D := by push_cast; ring

theorem le_ceilGrid {D : ℕ} (hD : 0 < D) (q : ℚ) : q ≤ ceilGrid D q := by
  rw [ceilGrid, le_div_iff₀ (by exact_mod_cast hD)]
  exact_mod_cast Rat.le_ceil (x := q * D)

def compress (D : ℕ) (a : RatBall) : RatBall :=
  ⟨⟨floorGrid D a.center.re, floorGrid D a.center.im⟩,
    ceilGrid D a.radius + 2 / D⟩

theorem compress_sound {D : ℕ} (hD : 0 < D) {a : RatBall} {z : ℂ}
    (hz : a.Holds z) : (compress D a).Holds z := by
  have hreL := floorGrid_le hD a.center.re
  have hreU := lt_floorGrid_add hD a.center.re
  have himL := floorGrid_le hD a.center.im
  have himU := lt_floorGrid_add hD a.center.im
  have hr := le_ceilGrid hD a.radius
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hreAbs : |a.center.re - floorGrid D a.center.re| ≤ (1 / D : ℚ) := by
    rw [abs_le]
    constructor <;> nlinarith
  have himAbs : |a.center.im - floorGrid D a.center.im| ≤ (1 / D : ℚ) := by
    rw [abs_le]
    constructor <;> nlinarith
  unfold RatBall.Holds E8ComplexBallKernel.InBall at hz ⊢
  have hid : z - (compress D a).center.val =
      (z - a.center.val) + (a.center.val - (compress D a).center.val) := by ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have hc : ‖a.center.val - (compress D a).center.val‖ ≤ (2 / D : ℚ) := by
    have hl1 := E8GaussianRatBall.norm_val_le_l1
      (a.center.add (compress D a).center.neg)
    rw [E8GaussianRatBall.val_add, E8GaussianRatBall.val_neg] at hl1
    refine hl1.trans ?_
    unfold compress GaussianRat.add GaussianRat.neg GaussianRat.l1
    push_cast
    have hq : |a.center.re - floorGrid D a.center.re| +
        |a.center.im - floorGrid D a.center.im| ≤ (2 / D : ℚ) := by
      calc
        _ ≤ (1 / D : ℚ) + 1 / D := add_le_add hreAbs himAbs
        _ = 2 / D := by ring
    have hqR : ((|a.center.re - floorGrid D a.center.re| +
        |a.center.im - floorGrid D a.center.im| : ℚ) : ℝ) ≤
        ((2 / D : ℚ) : ℝ) := by exact_mod_cast hq
    simpa [sub_eq_add_neg] using hqR
  have hrR : (a.radius : ℝ) ≤ (ceilGrid D a.radius : ℚ) := by exact_mod_cast hr
  have hsum := add_le_add hz hc
  dsimp [compress] at hsum ⊢
  push_cast at hsum ⊢
  linarith

def add (D : ℕ) (a b : RatBall) : RatBall := compress D (a.add b)
def sub (D : ℕ) (a b : RatBall) : RatBall := compress D (a.sub b)
def mul (D : ℕ) (a b : RatBall) : RatBall := compress D (a.mul b)
def scale (D : ℕ) (q : ℚ) (a : RatBall) : RatBall := compress D (a.scale q)
def invAuto (D : ℕ) (a : RatBall) : RatBall := compress D a.invAuto

theorem add_sound {D : ℕ} (hD : 0 < D) {a b : RatBall} {x y : ℂ}
    (hx : a.Holds x) (hy : b.Holds y) : (add D a b).Holds (x + y) :=
  compress_sound hD (E8GaussianRatBall.holds_add hx hy)

theorem mul_sound {D : ℕ} (hD : 0 < D) {a b : RatBall} {x y : ℂ}
    (hx : a.Holds x) (hy : b.Holds y) : (mul D a b).Holds (x * y) :=
  compress_sound hD (E8GaussianRatBall.holds_mul hx hy)

theorem invAuto_sound {D : ℕ} (hD : 0 < D) {a : RatBall} {z : ℂ}
    (hz : a.Holds z) (hok : a.invOK = true) : (invAuto D a).Holds z⁻¹ :=
  compress_sound hD (E8GaussianRatBall.holds_invAuto hz hok)

end GeneralCK.Certificates.E8RoundedRatBall

end


