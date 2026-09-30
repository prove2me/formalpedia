-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8GaussianRatBall
-- name    : CK_GeneralCK_Certificates_E8GaussianRatBall
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:32:56.450957+00:00
-- url     : https://prove2.me/theorems/679fb41f-0c0d-4f4d-b789-c311b5ed8c5e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8GaussianRatBall` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8GaussianRatBall` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8GaussianRatBall` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8GaussianRatBall (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8GaussianRatBall.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ComplexLogEnclosures

-- ===== source module GeneralCK.Certificates.E8GaussianRatBall =====
section

/-! Executable Gaussian-rational records for the E8 complex-ball kernel. -/

namespace GeneralCK.Certificates.E8GaussianRatBall

open E8ComplexBallKernel

structure GaussianRat where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

def GaussianRat.val (q : GaussianRat) : ℂ := (q.re : ℂ) + (q.im : ℂ) * Complex.I
def GaussianRat.l1 (q : GaussianRat) : ℚ := |q.re| + |q.im|
def GaussianRat.lower (q : GaussianRat) : ℚ := max |q.re| |q.im|

def GaussianRat.add (a b : GaussianRat) : GaussianRat := ⟨a.re + b.re, a.im + b.im⟩
def GaussianRat.neg (a : GaussianRat) : GaussianRat := ⟨-a.re, -a.im⟩
def GaussianRat.mul (a b : GaussianRat) : GaussianRat :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def GaussianRat.scale (s : ℚ) (a : GaussianRat) : GaussianRat :=
  ⟨s * a.re, s * a.im⟩
def GaussianRat.inv (a : GaussianRat) : GaussianRat :=
  let d := a.re ^ 2 + a.im ^ 2
  ⟨a.re / d, -a.im / d⟩

@[simp] theorem val_re (a : GaussianRat) : a.val.re = a.re := by
  simp [GaussianRat.val]

@[simp] theorem val_im (a : GaussianRat) : a.val.im = a.im := by
  simp [GaussianRat.val]

@[simp] theorem val_add (a b : GaussianRat) : (a.add b).val = a.val + b.val := by
  apply Complex.ext <;> simp [GaussianRat.add, GaussianRat.val] <;> ring

@[simp] theorem val_neg (a : GaussianRat) : a.neg.val = -a.val := by
  apply Complex.ext <;> simp [GaussianRat.neg, GaussianRat.val]

@[simp] theorem val_mul (a b : GaussianRat) : (a.mul b).val = a.val * b.val := by
  apply Complex.ext <;> simp [GaussianRat.mul, GaussianRat.val] <;> ring

@[simp] theorem val_scale (s : ℚ) (a : GaussianRat) :
    (a.scale s).val = (s : ℂ) * a.val := by
  apply Complex.ext <;> simp [GaussianRat.scale, GaussianRat.val] <;> ring

@[simp] theorem val_inv (a : GaussianRat) : a.inv.val = a.val⁻¹ := by
  apply Complex.ext
  · rw [val_re, Complex.inv_re]
    dsimp [GaussianRat.inv]
    rw [Complex.normSq_apply]
    simp only [val_re, val_im]
    change (((a.re / (a.re ^ 2 + a.im ^ 2) : ℚ) : ℝ)) =
      (a.re : ℝ) / ((a.re : ℝ) * a.re + (a.im : ℝ) * a.im)
    push_cast
    ring
  · rw [val_im, Complex.inv_im]
    dsimp [GaussianRat.inv]
    rw [Complex.normSq_apply]
    simp only [val_re, val_im]
    change (((-a.im / (a.re ^ 2 + a.im ^ 2) : ℚ) : ℝ)) =
      -(a.im : ℝ) / ((a.re : ℝ) * a.re + (a.im : ℝ) * a.im)
    push_cast
    ring

theorem norm_val_le_l1 (q : GaussianRat) : ‖q.val‖ ≤ (q.l1 : ℝ) := by
  unfold GaussianRat.val GaussianRat.l1
  calc
    ‖(q.re : ℂ) + (q.im : ℂ) * Complex.I‖ ≤
        ‖(q.re : ℂ)‖ + ‖(q.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ((|q.re| + |q.im| : ℚ) : ℝ) := by
      norm_num [Complex.norm_real]

theorem lower_le_norm_val (q : GaussianRat) : (q.lower : ℝ) ≤ ‖q.val‖ := by
  rw [GaussianRat.lower, Rat.cast_max]
  apply max_le
  · simpa using Complex.abs_re_le_norm q.val
  · simpa using Complex.abs_im_le_norm q.val

structure RatBall where
  center : GaussianRat
  radius : ℚ
  deriving DecidableEq, Repr

def RatBall.Holds (b : RatBall) (z : ℂ) : Prop :=
  InBall z b.center.val (b.radius : ℝ)

def RatBall.add (a b : RatBall) : RatBall :=
  ⟨a.center.add b.center, a.radius + b.radius⟩

def RatBall.neg (a : RatBall) : RatBall := ⟨a.center.neg, a.radius⟩
def RatBall.sub (a b : RatBall) : RatBall := a.add b.neg

def RatBall.point (re im : ℚ) : RatBall := ⟨⟨re, im⟩, 0⟩

def RatBall.mul (a b : RatBall) : RatBall :=
  ⟨a.center.mul b.center,
    a.center.l1 * b.radius + b.center.l1 * a.radius + a.radius * b.radius⟩

def RatBall.zero : RatBall := ⟨⟨0, 0⟩, 0⟩

def RatBall.scale (s : ℚ) (a : RatBall) : RatBall :=
  ⟨a.center.scale s, |s| * a.radius⟩

def RatBall.inv (lower : ℚ) (a : RatBall) : RatBall :=
  ⟨a.center.inv, a.radius / ((lower - a.radius) * lower)⟩

def RatBall.div (a b : RatBall) (lower : ℚ) : RatBall :=
  a.mul (b.inv lower)

def RatBall.invAuto (a : RatBall) : RatBall := a.inv a.center.lower
def RatBall.divAuto (a b : RatBall) : RatBall := a.mul b.invAuto
def RatBall.invOK (a : RatBall) : Bool := decide (a.radius < a.center.lower)

def RatBall.pow (a : RatBall) : ℕ → RatBall
  | 0 => ⟨⟨1, 0⟩, 0⟩
  | n + 1 => (a.pow n).mul a

/-- Exact rational-ball evaluation of `Complex.logTaylor n`. -/
def RatBall.logTaylor : ℕ → RatBall → RatBall
  | 0, _ => RatBall.zero
  | n + 1, a =>
      (RatBall.logTaylor n a).add
        ((a.pow n).scale (((-1 : ℚ) ^ (n + 1)) / n))

/-- Executable order-12 principal-log enclosure.  `rho` is a rational
upper bound for the norm of every input represented by `a`. -/
def RatBall.logOnePlus12 (rho : ℚ) (a : RatBall) : RatBall :=
  let p := a.logTaylor 13
  ⟨p.center, p.radius + rho ^ 13 / (13 * (1 - rho))⟩

theorem holds_add {a b : RatBall} {x y : ℂ}
    (hx : a.Holds x) (hy : b.Holds y) : (a.add b).Holds (x + y) := by
  simpa [RatBall.Holds, RatBall.add] using E8ComplexBallKernel.add hx hy

theorem holds_neg {a : RatBall} {x : ℂ} (hx : a.Holds x) :
    a.neg.Holds (-x) := by
  simpa [RatBall.Holds, RatBall.neg] using E8ComplexBallKernel.neg hx

theorem holds_sub {a b : RatBall} {x y : ℂ}
    (hx : a.Holds x) (hy : b.Holds y) : (a.sub b).Holds (x - y) := by
  simpa [RatBall.sub, sub_eq_add_neg] using holds_add hx (holds_neg hy)

theorem holds_point (re im : ℚ) :
    (RatBall.point re im).Holds (GaussianRat.val ⟨re, im⟩) := by
  simp [RatBall.point, RatBall.Holds, InBall]

theorem holds_mul {a b : RatBall} {x y : ℂ}
    (hx : a.Holds x) (hy : b.Holds y) : (a.mul b).Holds (x * y) := by
  simpa [RatBall.Holds, RatBall.mul] using E8ComplexBallKernel.mul hx hy
    (norm_val_le_l1 a.center) (norm_val_le_l1 b.center)

theorem holds_zero : RatBall.zero.Holds 0 := by
  simp [RatBall.zero, RatBall.Holds, InBall, GaussianRat.val]

theorem holds_scale {a : RatBall} {z : ℂ} (s : ℚ) (hz : a.Holds z) :
    (a.scale s).Holds ((s : ℂ) * z) := by
  unfold RatBall.Holds InBall RatBall.scale at *
  rw [val_scale]
  have hid : (s : ℂ) * z - (s : ℂ) * a.center.val =
      (s : ℂ) * (z - a.center.val) := by ring
  rw [hid, norm_mul]
  simpa using mul_le_mul_of_nonneg_left hz (norm_nonneg (s : ℂ))

theorem holds_inv {a : RatBall} {z : ℂ} {lower : ℚ}
    (hz : a.Holds z) (hlower : (lower : ℝ) ≤ ‖a.center.val‖)
    (hr : a.radius < lower) : (a.inv lower).Holds z⁻¹ := by
  have h := E8ComplexBallKernel.inv hz hlower (by exact_mod_cast hr)
  simpa [RatBall.Holds, RatBall.inv] using h

theorem holds_div {a b : RatBall} {x y : ℂ} {lower : ℚ}
    (hx : a.Holds x) (hy : b.Holds y)
    (hlower : (lower : ℝ) ≤ ‖b.center.val‖) (hr : b.radius < lower) :
    (a.div b lower).Holds (x / y) := by
  simpa [RatBall.div, div_eq_mul_inv] using holds_mul hx (holds_inv hy hlower hr)

theorem holds_invAuto {a : RatBall} {z : ℂ} (hz : a.Holds z)
    (hok : a.invOK = true) : a.invAuto.Holds z⁻¹ := by
  unfold RatBall.invOK at hok
  exact holds_inv hz (lower_le_norm_val a.center) (of_decide_eq_true hok)

theorem holds_divAuto {a b : RatBall} {x y : ℂ} (hx : a.Holds x) (hy : b.Holds y)
    (hok : b.invOK = true) : (a.divAuto b).Holds (x / y) := by
  simpa [RatBall.divAuto, div_eq_mul_inv] using holds_mul hx (holds_invAuto hy hok)

theorem holds_pow {a : RatBall} {z : ℂ} (hz : a.Holds z) :
    ∀ n, (a.pow n).Holds (z ^ n)
  | 0 => by simp [RatBall.pow, RatBall.Holds, InBall, GaussianRat.val]
  | n + 1 => by
      rw [pow_succ]
      exact holds_mul (holds_pow hz n) hz

theorem holds_logTaylor {a : RatBall} {z : ℂ} (hz : a.Holds z) :
    ∀ n, (a.logTaylor n).Holds (Complex.logTaylor n z)
  | 0 => by simpa [Complex.logTaylor_zero, RatBall.logTaylor] using holds_zero
  | n + 1 => by
      rw [Complex.logTaylor_succ]
      exact holds_add (holds_logTaylor hz n)
        (by
          convert holds_scale (((-1 : ℚ) ^ (n + 1)) / n) (holds_pow hz n) using 1
          push_cast
          ring)

theorem holds_logOnePlus12 {a : RatBall} {z : ℂ} {rho : ℚ}
    (hz : a.Holds z) (hnorm : ‖z‖ ≤ (rho : ℝ)) (hrho : rho < 1) :
    (a.logOnePlus12 rho).Holds (Complex.log (1 + z)) := by
  let remQ : ℚ := rho ^ 13 / (13 * (1 - rho))
  have hp := holds_logTaylor hz 13
  have hlog := E8ComplexBallKernel.log_one_add_taylor12 hnorm (by exact_mod_cast hrho)
  unfold RatBall.Holds InBall at hp hlog ⊢
  simp only [RatBall.logOnePlus12]
  change ‖Complex.log (1 + z) - (a.logTaylor 13).center.val‖ ≤
    (((a.logTaylor 13).radius + remQ : ℚ) : ℝ)
  have hid : Complex.log (1 + z) - (a.logTaylor 13).center.val =
      (Complex.log (1 + z) - Complex.logTaylor 13 z) +
        (Complex.logTaylor 13 z - (a.logTaylor 13).center.val) := by ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have hrem :
      (rho : ℝ) ^ 13 * (1 - (rho : ℝ))⁻¹ / 13 =
        (remQ : ℝ) := by
    dsimp [remQ]
    push_cast
    field_simp
    <;> ring
  rw [hrem] at hlog
  calc
    ‖Complex.log (1 + z) - Complex.logTaylor 13 z‖ +
        ‖Complex.logTaylor 13 z - (a.logTaylor 13).center.val‖ ≤
        (remQ : ℝ) +
          (↑(a.logTaylor 13).radius : ℝ) := add_le_add hlog hp
    _ = (((a.logTaylor 13).radius + remQ : ℚ) : ℝ) := by
      push_cast
      ring

/-- Executable acceptance test for proving that an output ball lies in the
unit ball.  The `l1` center norm is conservative and purely rational. -/
def RatBall.acceptsUnit (b : RatBall) : Bool :=
  decide (0 ≤ b.radius ∧ b.center.l1 + b.radius ≤ 1)

theorem acceptsUnit_sound {b : RatBall} (h : b.acceptsUnit = true) {z : ℂ}
    (hz : b.Holds z) : ‖z‖ ≤ 1 := by
  have hb : 0 ≤ b.radius ∧ b.center.l1 + b.radius ≤ 1 := of_decide_eq_true h
  unfold RatBall.Holds InBall at hz
  calc
    ‖z‖ ≤ ‖b.center.val‖ + ‖z - b.center.val‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ (b.center.l1 : ℝ) + b.radius :=
      add_le_add (norm_val_le_l1 b.center) hz
    _ ≤ 1 := by exact_mod_cast hb.2

/-- Executable conservative containment test between rational balls. -/
def RatBall.contains (outer inner : RatBall) : Bool :=
  decide ((inner.center.add outer.center.neg).l1 + inner.radius ≤ outer.radius)

theorem contains_sound {outer inner : RatBall} (h : outer.contains inner = true)
    {z : ℂ} (hz : inner.Holds z) : outer.Holds z := by
  unfold RatBall.contains at h
  have hq : (inner.center.add outer.center.neg).l1 + inner.radius ≤ outer.radius :=
    of_decide_eq_true h
  unfold RatBall.Holds InBall at *
  have hid : z - outer.center.val =
      (z - inner.center.val) + (inner.center.val - outer.center.val) := by ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have hc : ‖inner.center.val - outer.center.val‖ ≤
      ((inner.center.add outer.center.neg).l1 : ℝ) := by
    have ht := norm_val_le_l1 (inner.center.add outer.center.neg)
    rw [val_add, val_neg] at ht
    simpa [sub_eq_add_neg] using ht
  have hqr : ((inner.center.add outer.center.neg).l1 : ℝ) + inner.radius ≤
      outer.radius := by exact_mod_cast hq
  linarith

end GeneralCK.Certificates.E8GaussianRatBall

end


