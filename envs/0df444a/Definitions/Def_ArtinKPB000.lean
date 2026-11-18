-- Prove2me | Definitions.Def_ArtinKPB000
-- name    : ArtinKPB000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:15:04.557573+00:00
-- url     : https://prove2.me/theorems/91744569-e4b3-4328-a698-2c5b0ae00219
-- title:
--   Definitions bundle ArtinKPB000 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 112 declarations of that development: 20 definitions, 3 inductive types or structures and 89 theorems. The definitions and types are `ArtinKP.A.CubicPkg`, `ArtinKP.A.CubicPkg.HS`, `ArtinKP.A.CubicPkg.IsDeepLevel`, `ArtinKP.A.CubicPkg.extSupp`, `ArtinKP.A.CubicPkg.sFin`, `ArtinKP.A.Gamma`, `ArtinKP.A.Good`, `ArtinKP.A.IsRad`, `ArtinKP.A.IsTameSymbol`, `ArtinKP.A.X`, `ArtinKP.A.Xs`, `ArtinKP.A.Xu`, `ArtinKP.A.cubicExt`, `ArtinKP.A.iota3`, `ArtinKP.A.kappa`, `ArtinKP.A.ordv`, `ArtinKP.A.sL`, `ArtinKP.A.sLoc`, `ArtinKP.A.sM`, `ArtinKP.A.sigmaLoc`, `ArtinKP.A.sigmaS`, `ArtinKP.A.toF`, `ArtinKP.A.tz`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `C0.C0R_Tr`, `KP.A_Kubota`, `KP.A_Local`, `KP.A_Pkg`, `KP.A_Residue`.
--
--   **Imports.** It imports the published bundles `Def_ArtinHeckeProbe` and `Def_ArtinHeckeTheta`.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB001`; the statements `ArtinKP.A.kappa_mul_of_mem_Gamma`, `ArtinKP.C5.quotVol_lt_top`, `ArtinKP.N2.integrable_lift_pou`, `ArtinKP.N2.lintegral_lift_pou_ne_top` and `ArtinKP.S2.cubicExt_eq_zero_iff`; the proofs of `ArtinKP.A.kappa_mul_of_mem_Gamma` and `ArtinKP.S2.cubicExt_eq_zero_iff`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

section
-- module Solutions.Artin.C0.C0R_Tr
/-!
# Transport of `AllowedGen` along a field isomorphism

Used to move from `F : Type u` to the universe-0 copy `CyclotomicField n ℚ`.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

namespace C0R

/-! ### Generic facts on ideals along a ring equivalence -/

/-! ### The equivalences -/

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

/-! ### Uniqueness of the sixth root of unity modulo `P` -/

theorem eq_of_pow_six {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) (h6 : (6 : R) ∉ Q)
    {a b : R} (ha : a ^ 6 = 1) (hb : b ^ 6 = 1) (hab : a - b ∈ Q) : a = b := by
  set η := b * a ^ 5 with hη
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ 5 * (a - b) := by rw [hη]; linear_combination (-1 : R) * ha
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · have : b = a := calc
        b = b * a ^ 6 := by rw [ha, mul_one]
        _ = (b * a ^ 5) * a := by ring
        _ = a := by rw [← hη, hη1, one_mul]
    exact this.symm
  · exfalso
    have hη6 : η ^ 6 = 1 := by
      rw [hη]
      calc (b * a ^ 5) ^ 6 = b ^ 6 * (a ^ 6) ^ 5 := by ring
        _ = 1 := by rw [ha, hb]; ring
    have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5 = 0 := by
      have : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) = 0 := by
        linear_combination hη6
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hη1
      · exact h
    apply h6
    have : (6 : R) = (1 - η) * (5 + 4 * η + 3 * η ^ 2 + 2 * η ^ 3 + η ^ 4) +
        (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) := by ring
    rw [this, hsum, add_zero]
    exact Q.mul_mem_right _ h1

/-! ### The residue symbol transports -/

/-! ### `AllowedGen` transports -/

end C0R

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.A_Local
/-!
# WP-A, local part: Kubota's lemma for a tame symbol

`F` is any field with a valuation `v`, and `t : Fˣ → Fˣ → A` is a bi-additive symbol with values in
an additive commutative group which is *tame* at `v` (`IsTameSymbol`): units pair trivially,
`t a (-a) = 0`, `t (-1) a = 0`, and `t a b = 0` for `b ≡ 1`.

Main statement (`kubota_local`): for `g₁ g₂ ∈ SL₂(F)` with `v`-integral entries,

  `t (X(g₁g₂)/X(g₁)) (X(g₁g₂)/X(g₂)) + s(g₁) + s(g₂) = s(g₁g₂)`,

where `X(g) = c` if `c ≠ 0`, else `d`, and `s(g) = t c d` if `c ≠ 0`, `v c < 1`, else `0`.

**Orientation.**  This is `σ = s(g₁g₂)/(s(g₁)s(g₂))`; the opposite orientation
`σ = s(g₁)s(g₂)/s(g₁g₂)` (as written in MATH.md §1.3) is false for symbols of order `3`:
for `g₁ = diag(d₁⁻¹, d₁)` and `0 < ord c₂` one gets `σ = t c₂ d₁` and
`s(g₁g₂) - s(g₂) = t c₂ d₁`.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {A : Type*} [AddCommGroup A]

/-- A bi-additive symbol on `Fˣ` which is tame with respect to the valuation `v`. -/
structure IsTameSymbol (v : Valuation F Γ₀) (t : Fˣ → Fˣ → A) : Prop where
  mul_left : ∀ a b c : Fˣ, t (a * b) c = t a c + t b c
  mul_right : ∀ a b c : Fˣ, t a (b * c) = t a b + t a c
  unit_unit : ∀ a b : Fˣ, v (a : F) = 1 → v (b : F) = 1 → t a b = 0
  steinberg : ∀ a : Fˣ, t a (-a) = 0
  neg_one_left : ∀ a : Fˣ, t (-1) a = 0
  one_add : ∀ a b : Fˣ, v ((b : F) - 1) < 1 → t a b = 0

namespace IsTameSymbol

variable {v : Valuation F Γ₀} {t : Fˣ → Fˣ → A} (h : IsTameSymbol v t)
include h

theorem one_left (c : Fˣ) : t 1 c = 0 := by
  have := h.mul_left 1 1 c
  rw [mul_one] at this
  simpa using this

theorem one_right (c : Fˣ) : t c 1 = 0 := by
  have := h.mul_right c 1 1
  rw [mul_one] at this
  simpa using this

theorem inv_left (a c : Fˣ) : t a⁻¹ c = -t a c := by
  have := h.mul_left a a⁻¹ c
  rw [mul_inv_cancel, h.one_left] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem inv_right (a c : Fˣ) : t a c⁻¹ = -t a c := by
  have := h.mul_right a c c⁻¹
  rw [mul_inv_cancel, h.one_right] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem div_left (a b c : Fˣ) : t (a / b) c = t a c - t b c := by
  rw [div_eq_mul_inv, h.mul_left, h.inv_left, sub_eq_add_neg]

theorem div_right (a b c : Fˣ) : t a (b / c) = t a b - t a c := by
  rw [div_eq_mul_inv, h.mul_right, h.inv_right, sub_eq_add_neg]

theorem neg_left (a b : Fˣ) : t (-a) b = t a b := by
  rw [← neg_one_mul, h.mul_left, h.neg_one_left, zero_add]

theorem self (b : Fˣ) : t b b = 0 := by
  have := h.steinberg (-b)
  rwa [neg_neg, h.neg_left] at this

theorem neg_one_right (b : Fˣ) : t b (-1) = 0 := by
  have := h.steinberg b
  rwa [← neg_one_mul, h.mul_right, h.self, add_zero] at this

theorem neg_right (a b : Fˣ) : t a (-b) = t a b := by
  rw [← neg_one_mul, h.mul_right, h.neg_one_right, zero_add]

theorem skew (a b : Fˣ) : t a b + t b a = 0 := by
  have := h.self (a * b)
  rw [h.mul_left, h.mul_right, h.mul_right, h.self, h.self] at this
  linear_combination (norm := module) this

theorem one_add_left (a b : Fˣ) (ha : v ((a : F) - 1) < 1) : t a b = 0 := by
  have := h.skew a b
  rwa [h.one_add b a ha, add_zero] at this

/-- Steinberg relation `t a (1 - a) = 0`. -/
theorem add_eq_one (a b : Fˣ) (hab : (a : F) + b = 1) : t a b = 0 := by
  have hb1 : (b : F) - 1 = -a := by linear_combination hab
  have ha1 : (a : F) - 1 = -b := by linear_combination hab
  rcases lt_trichotomy (v (a : F)) 1 with hlt | heq | hgt
  · exact h.one_add a b (by rw [hb1, Valuation.map_neg]; exact hlt)
  · have hble : v (b : F) ≤ 1 := by
      have : (b : F) = 1 + -a := by linear_combination hab
      rw [this]
      refine (v.map_add _ _).trans (max_le (by rw [map_one]) ?_)
      rw [Valuation.map_neg, heq]
    rcases lt_or_eq_of_le hble with hlt | heq'
    · have := h.skew a b
      rwa [h.one_add b a (by rw [ha1, Valuation.map_neg]; exact hlt), add_zero] at this
    · exact h.unit_unit a b heq heq'
  · set w : Fˣ := b / (-a) with hw
    have hbw : b = -a * w := by rw [hw, mul_div_cancel]
    have hw1 : (w : F) - 1 = -(a : F)⁻¹ := by
      rw [hw]
      push_cast
      have : (a : F) ≠ 0 := a.ne_zero
      field_simp
      linear_combination -hab
    have hlt : v ((w : F) - 1) < 1 := by
      rw [hw1, Valuation.map_neg, map_inv₀]
      exact inv_lt_one_of_one_lt₀ hgt
    rw [hbw, h.mul_right, h.steinberg, h.one_add a w hlt, add_zero]

/-- Steinberg relation in homogeneous form. -/
theorem add_eq (x y z : Fˣ) (hxyz : (x : F) + y = z) : t (x / z) (y / z) = 0 := by
  apply h.add_eq_one
  push_cast
  have : (z : F) ≠ 0 := z.ne_zero
  field_simp
  exact hxyz

theorem right_close (x d d' : Fˣ) (hd : v ((d : F) / d' - 1) < 1) : t x d = t x d' := by
  have := h.one_add x (d / d') (by push_cast; exact hd)
  rw [h.div_right] at this
  exact sub_eq_zero.mp this

theorem left_close (d d' x : Fˣ) (hd : v ((d : F) / d' - 1) < 1) : t d x = t d' x := by
  have := h.one_add_left (d / d') x (by push_cast; exact hd)
  rw [h.div_left] at this
  exact sub_eq_zero.mp this

/-- If `a d ≡ 1` then `t a x = t x d`. -/
theorem eq_of_mul_close (a d x : Fˣ) (had : v ((a : F) * d - 1) < 1) : t a x = t x d := by
  have h1 := h.one_add_left (a * d) x (by push_cast; exact had)
  rw [h.mul_left] at h1
  linear_combination (norm := module) h1 - h.skew d x

end IsTameSymbol

/-! ### Extension by zero to `F × F` -/

open Classical in
/-- The symbol extended by `0` to all of `F × F`. -/
def tz (t : Fˣ → Fˣ → A) (x y : F) : A :=
  if h : x ≠ 0 ∧ y ≠ 0 then t (Units.mk0 x h.1) (Units.mk0 y h.2) else 0

@[simp] theorem tz_coe (t : Fˣ → Fˣ → A) (a b : Fˣ) : tz t (a : F) (b : F) = t a b := by
  simp [tz]

@[simp] theorem tz_zero_left (t : Fˣ → Fˣ → A) (y : F) : tz t 0 y = 0 := by
  simp [tz]

@[simp] theorem tz_zero_right (t : Fˣ → Fˣ → A) (x : F) : tz t x 0 = 0 := by
  simp [tz]

theorem ne_zero_of_val_eq_one (v : Valuation F Γ₀) {x : F} (hx : v x = 1) : x ≠ 0 := by
  rintro rfl
  rw [map_zero] at hx
  exact zero_ne_one hx

section Cases

variable {v : Valuation F Γ₀} {t : Fˣ → Fˣ → A} (h : IsTameSymbol v t)
include h

theorem tz_units {x y : F} (hx : v x = 1) (hy : v y = 1) : tz t x y = 0 := by
  have hx0 := ne_zero_of_val_eq_one v hx
  have hy0 := ne_zero_of_val_eq_one v hy
  lift x to Fˣ using hx0.isUnit
  lift y to Fˣ using hy0.isUnit
  rw [tz_coe]
  exact h.unit_unit x y hx hy

theorem case_Ib {c2 d1 d2 : F} (hc2 : c2 ≠ 0) (hd1 : v d1 = 1) (hd2 : v d2 = 1) :
    tz t (d1 * c2 / d1) (d1 * c2 / c2) + tz t c2 d2 = tz t (d1 * c2) (d1 * d2) := by
  have hd10 := ne_zero_of_val_eq_one v hd1
  have hd20 := ne_zero_of_val_eq_one v hd2
  lift c2 to Fˣ using hc2.isUnit
  lift d1 to Fˣ using hd10.isUnit
  lift d2 to Fˣ using hd20.isUnit
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right]
  linear_combination (norm := module) -(h.self d1) - h.unit_unit d1 d2 hd1 hd2

theorem case_Ic {c1 a2 d1 d2 d3 : F} (hc1 : c1 ≠ 0) (ha2 : v a2 = 1) (hd1 : v d1 = 1)
    (hd2 : v d2 = 1) (hd3 : v d3 = 1) (had : v (a2 * d2 - 1) < 1)
    (hd3c : v (d3 / (d1 * d2) - 1) < 1) :
    tz t (c1 * a2 / c1) (c1 * a2 / d2) + tz t c1 d1 = tz t (c1 * a2) d3 := by
  have ha20 := ne_zero_of_val_eq_one v ha2
  have hd10 := ne_zero_of_val_eq_one v hd1
  have hd20 := ne_zero_of_val_eq_one v hd2
  have hd30 := ne_zero_of_val_eq_one v hd3
  lift c1 to Fˣ using hc1.isUnit
  lift a2 to Fˣ using ha20.isUnit
  lift d1 to Fˣ using hd10.isUnit
  lift d2 to Fˣ using hd20.isUnit
  lift d3 to Fˣ using hd30.isUnit
  have D := h.right_close c1 d3 (d1 * d2) (by push_cast; exact hd3c)
  have E := h.eq_of_mul_close a2 d2 c1 had
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right] at D ⊢
  linear_combination (norm := module) E + h.self a2 - h.unit_unit a2 d2 ha2 hd2
    - h.unit_unit a2 d3 ha2 hd3 - D

theorem case_Id {c1 c2 c3 a2 d1 d2 d3 : F} (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) (hc3 : c3 ≠ 0)
    (ha2 : v a2 = 1) (hd1 : v d1 = 1) (hd2 : v d2 = 1) (hd3 : v d3 = 1)
    (had : v (a2 * d2 - 1) < 1) (hd3c : v (d3 / (d1 * d2) - 1) < 1)
    (hc : c3 = c1 * a2 + d1 * c2) :
    tz t (c3 / c1) (c3 / c2) + tz t c1 d1 + tz t c2 d2 = tz t c3 d3 := by
  have ha20 := ne_zero_of_val_eq_one v ha2
  have hd10 := ne_zero_of_val_eq_one v hd1
  have hd20 := ne_zero_of_val_eq_one v hd2
  have hd30 := ne_zero_of_val_eq_one v hd3
  lift c1 to Fˣ using hc1.isUnit
  lift c2 to Fˣ using hc2.isUnit
  lift c3 to Fˣ using hc3.isUnit
  lift a2 to Fˣ using ha20.isUnit
  lift d1 to Fˣ using hd10.isUnit
  lift d2 to Fˣ using hd20.isUnit
  lift d3 to Fˣ using hd30.isUnit
  have e1 := h.add_eq (c1 * a2) (d1 * c2) c3 (by push_cast; exact hc.symm)
  have e2 := h.unit_unit a2 d1 ha2 hd1
  have e3 := h.eq_of_mul_close a2 d2 c2 had
  have e4 := h.eq_of_mul_close a2 d2 c3 had
  have e5 := h.right_close c3 d3 (d1 * d2) (by push_cast; exact hd3c)
  simp only [← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right] at e1 e5 ⊢
  linear_combination (norm := module) e1 - e2 - e3 + e4 - e5

theorem case_Ie {c1 c2 a2 d1 d2 d3 : F} (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0)
    (ha2 : v a2 = 1) (hd1 : v d1 = 1) (hd2 : v d2 = 1) (hd3 : v d3 = 1)
    (had : v (a2 * d2 - 1) < 1) (hd3c : v (d3 / (d1 * d2) - 1) < 1)
    (hc : c1 * a2 + d1 * c2 = 0) :
    tz t (d3 / c1) (d3 / c2) + tz t c1 d1 + tz t c2 d2 = 0 := by
  have ha20 := ne_zero_of_val_eq_one v ha2
  have hd10 := ne_zero_of_val_eq_one v hd1
  have hd20 := ne_zero_of_val_eq_one v hd2
  have hd30 := ne_zero_of_val_eq_one v hd3
  lift c1 to Fˣ using hc1.isUnit
  lift c2 to Fˣ using hc2.isUnit
  lift a2 to Fˣ using ha20.isUnit
  lift d1 to Fˣ using hd10.isUnit
  lift d2 to Fˣ using hd20.isUnit
  lift d3 to Fˣ using hd30.isUnit
  have hu : c1 = -(d1 * c2 / a2) := by
    apply Units.ext
    push_cast
    field_simp
    linear_combination hc
  have e6 : t c1 c2 = t (-(d1 * c2 / a2)) c2 := by rw [← hu]
  have e7 : t c1 d2 = t (-(d1 * c2 / a2)) d2 := by rw [← hu]
  have e3 := h.eq_of_mul_close a2 d2 c2 had
  have f2 := h.right_close c2 d3 (d1 * d2) (by push_cast; exact hd3c)
  have f3 := h.right_close c1 d3 (d1 * d2) (by push_cast; exact hd3c)
  simp only [← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right, h.neg_left] at e6 e7 f2 f3 ⊢
  -- goal: t d3 d3 - t d3 c2 - (t c1 d3 - t c1 c2) + t c1 d1 + t c2 d2 = 0
  linear_combination (norm := module) h.self d3 - h.skew d3 c2 + f2 - f3 + e6 - e7
    - h.unit_unit d1 d2 hd1 hd2 + h.unit_unit a2 d2 ha2 hd2 + h.self c2 - e3 + h.skew d1 c2

theorem case_IIb {c1 c2 c3 a2 d1 : F} (hc1 : c1 ≠ 0) (hc1v : v c1 < 1) (hc2 : v c2 = 1)
    (hd1 : v d1 = 1) (ha2 : v a2 ≤ 1) (hc : c3 = c1 * a2 + d1 * c2) :
    tz t (c3 / c1) (c3 / c2) + tz t c1 d1 = 0 := by
  have hc20 := ne_zero_of_val_eq_one v hc2
  have hd10 := ne_zero_of_val_eq_one v hd1
  have hclose : v (c3 / c2 / d1 - 1) < 1 := by
    have : c3 / c2 / d1 - 1 = c1 * a2 / (c2 * d1) := by
      rw [hc]; field_simp; ring
    rw [this, map_div₀, map_mul, map_mul, hc2, hd1, mul_one, div_one]
    exact mul_lt_one_of_lt_of_le hc1v ha2
  have hc3v : v c3 = 1 := by
    have h1 : v (c3 / c2 / d1) = 1 := by
      have := v.map_one_add_of_lt hclose
      rwa [add_sub_cancel] at this
    rwa [map_div₀, map_div₀, hc2, hd1, div_one, div_one] at h1
  have hc30 := ne_zero_of_val_eq_one v hc3v
  lift c1 to Fˣ using hc1.isUnit
  lift c2 to Fˣ using hc20.isUnit
  lift c3 to Fˣ using hc30.isUnit
  lift d1 to Fˣ using hd10.isUnit
  have R := h.right_close (c3 / c1) (c3 / c2) d1 (by push_cast; exact hclose)
  simp only [← Units.val_div_eq_div_val, tz_coe]
  rw [R]
  simp only [h.div_left]
  linear_combination (norm := module) h.unit_unit c3 d1 hc3v hd1

theorem case_IIIb {c1 c2 c3 a2 d1 d2 : F} (hc2 : c2 ≠ 0) (hc2v : v c2 < 1) (hc1 : v c1 = 1)
    (ha2 : v a2 = 1) (hd2 : v d2 = 1) (hd1 : v d1 ≤ 1) (had : v (a2 * d2 - 1) < 1)
    (hc : c3 = c1 * a2 + d1 * c2) :
    tz t (c3 / c1) (c3 / c2) + tz t c2 d2 = 0 := by
  have hc10 := ne_zero_of_val_eq_one v hc1
  have ha20 := ne_zero_of_val_eq_one v ha2
  have hd20 := ne_zero_of_val_eq_one v hd2
  have hclose : v (c3 / c1 / a2 - 1) < 1 := by
    have : c3 / c1 / a2 - 1 = d1 * c2 / (c1 * a2) := by
      rw [hc]; field_simp; ring
    rw [this, map_div₀, map_mul, map_mul, hc1, ha2, mul_one, div_one, mul_comm]
    exact mul_lt_one_of_lt_of_le hc2v hd1
  have hc3v : v c3 = 1 := by
    have h1 : v (c3 / c1 / a2) = 1 := by
      have := v.map_one_add_of_lt hclose
      rwa [add_sub_cancel] at this
    rwa [map_div₀, map_div₀, hc1, ha2, div_one, div_one] at h1
  have hc30 := ne_zero_of_val_eq_one v hc3v
  lift c1 to Fˣ using hc10.isUnit
  lift c2 to Fˣ using hc2.isUnit
  lift c3 to Fˣ using hc30.isUnit
  lift a2 to Fˣ using ha20.isUnit
  lift d2 to Fˣ using hd20.isUnit
  have L := h.left_close (c3 / c1) a2 (c3 / c2) (by push_cast; exact hclose)
  have e3 := h.eq_of_mul_close a2 d2 c2 had
  simp only [← Units.val_div_eq_div_val, tz_coe]
  rw [L]
  simp only [h.div_right]
  linear_combination (norm := module) h.unit_unit a2 c3 ha2 hc3v - e3

theorem case_IVc {c1 c2 c3 d2 d3 : F} (hc3 : c3 ≠ 0) (hc3v : v c3 < 1) (hc1 : v c1 = 1)
    (hc2 : v c2 = 1) (hd3 : v d3 = 1) (hd2 : v d2 ≤ 1) (hk : c1 = c3 * d2 - d3 * c2) :
    tz t (c3 / c1) (c3 / c2) = tz t c3 d3 := by
  have hc10 := ne_zero_of_val_eq_one v hc1
  have hc20 := ne_zero_of_val_eq_one v hc2
  have hd30 := ne_zero_of_val_eq_one v hd3
  have hclose : v (-(d3 * c2 / c1) - 1) < 1 := by
    have : -(d3 * c2 / c1) - 1 = -(c3 * d2 / c1) := by
      field_simp; linear_combination -hk
    rw [this, Valuation.map_neg, map_div₀, map_mul, hc1, div_one]
    exact mul_lt_one_of_lt_of_le hc3v hd2
  lift c1 to Fˣ using hc10.isUnit
  lift c2 to Fˣ using hc20.isUnit
  lift c3 to Fˣ using hc3.isUnit
  lift d3 to Fˣ using hd30.isUnit
  have W := h.one_add c3 (-(d3 * c2 / c1)) (by push_cast; exact hclose)
  simp only [← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_right, h.neg_right] at W ⊢
  linear_combination (norm := module) h.self c3 + h.unit_unit c1 c2 hc1 hc2 - W - h.skew c1 c3

end Cases

/-! ### The scalar form of Kubota's local lemma -/

open Classical in
/-- `X(c, d) = c` if `c ≠ 0`, else `d`. -/
def Xs (c d : F) : F := if c = 0 then d else c

/-- `s(c, d) = t c d` if `v c < 1` (and `c ≠ 0`), else `0`. -/
def sL (v : Valuation F Γ₀) (t : Fˣ → Fˣ → A) (c d : F) : A :=
  if v c < 1 then tz t c d else 0

theorem val_eq_one_of_mul (v : Valuation F Γ₀) {x y : F} (hx : v x ≤ 1) (hy : v y ≤ 1)
    (hxy : v (x * y) = 1) : v x = 1 ∧ v y = 1 := by
  rw [map_mul] at hxy
  constructor
  · refine le_antisymm hx ?_
    calc (1 : Γ₀) = v x * v y := hxy.symm
      _ ≤ v x * 1 := by gcongr
      _ = v x := mul_one _
  · refine le_antisymm hy ?_
    calc (1 : Γ₀) = v x * v y := hxy.symm
      _ ≤ 1 * v y := by gcongr
      _ = v y := one_mul _

theorem kubota_scalar {v : Valuation F Γ₀} {t : Fˣ → Fˣ → A} (h : IsTameSymbol v t)
    {a2 b2 c1 c2 d1 d2 c3 d3 : F}
    (hr1 : v c1 = 1 ∨ v d1 = 1) (ic1 : v c1 ≤ 1) (id1 : v d1 ≤ 1)
    (ia2 : v a2 ≤ 1) (ib2 : v b2 ≤ 1) (ic2 : v c2 ≤ 1) (id2 : v d2 ≤ 1)
    (det2 : a2 * d2 - b2 * c2 = 1)
    (hc3 : c3 = c1 * a2 + d1 * c2) (hd3 : d3 = c1 * b2 + d1 * d2) :
    tz t (Xs c3 d3 / Xs c1 d1) (Xs c3 d3 / Xs c2 d2) + sL v t c1 d1 + sL v t c2 d2
      = sL v t c3 d3 := by
  have hk : c1 = c3 * d2 - d3 * c2 := by rw [hc3, hd3]; linear_combination -c1 * det2
  have hk' : d1 = d3 * a2 - c3 * b2 := by rw [hc3, hd3]; linear_combination -d1 * det2
  have ic3 : v c3 ≤ 1 := by
    rw [hc3]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;>
      exact mul_le_one' (by assumption) (by assumption)
  have id3 : v d3 ≤ 1 := by
    rw [hd3]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;>
      exact mul_le_one' (by assumption) (by assumption)
  by_cases h1 : v c1 < 1
  · have hd1 : v d1 = 1 := hr1.resolve_left h1.ne
    by_cases h2 : v c2 < 1
    · -- Case I
      have hbc : v (b2 * c2) < 1 := by
        rw [map_mul, mul_comm]; exact mul_lt_one_of_lt_of_le h2 ib2
      have had : v (a2 * d2 - 1) < 1 := by
        rwa [show a2 * d2 - 1 = b2 * c2 by linear_combination det2]
      have hada : v (a2 * d2) = 1 := by
        have := v.map_one_add_of_lt had
        rwa [add_sub_cancel] at this
      obtain ⟨ha2, hd2⟩ := val_eq_one_of_mul v ia2 id2 hada
      have hd10 := ne_zero_of_val_eq_one v hd1
      have hd20 := ne_zero_of_val_eq_one v hd2
      have hd3c : v (d3 / (d1 * d2) - 1) < 1 := by
        have : d3 / (d1 * d2) - 1 = c1 * b2 / (d1 * d2) := by
          rw [hd3]; field_simp; ring
        rw [this, map_div₀, map_mul, map_mul, hd1, hd2, mul_one, div_one]
        exact mul_lt_one_of_lt_of_le h1 ib2
      have hd3u : v d3 = 1 := by
        have h1' : v (d3 / (d1 * d2)) = 1 := by
          have := v.map_one_add_of_lt hd3c
          rwa [add_sub_cancel] at this
        rwa [map_div₀, map_mul, hd1, hd2, mul_one, div_one] at h1'
      have hc3v : v c3 < 1 := by
        rw [hc3]
        refine v.map_add_lt ?_ ?_ <;> rw [map_mul]
        · exact mul_lt_one_of_lt_of_le h1 ia2
        · rw [mul_comm]; exact mul_lt_one_of_lt_of_le h2 id1
      simp only [sL, if_pos h1, if_pos h2, if_pos hc3v]
      by_cases z1 : c1 = 0
      · by_cases z2 : c2 = 0
        · have z3 : c3 = 0 := by rw [hc3, z1, z2]; ring
          simp only [Xs, z1, z2, z3, if_true, tz_zero_left, add_zero]
          exact tz_units h (by rw [map_div₀, hd3u, hd1, div_one])
            (by rw [map_div₀, hd3u, hd2, div_one])
        · have e3 : c3 = d1 * c2 := by rw [hc3, z1]; ring
          have e3' : d3 = d1 * d2 := by rw [hd3, z1]; ring
          have n3 : d1 * c2 ≠ 0 := mul_ne_zero hd10 z2
          rw [e3, e3']
          simp only [Xs, z1, if_true, if_neg z2, if_neg n3, tz_zero_left, add_zero]
          exact case_Ib h z2 hd1 hd2
      · by_cases z2 : c2 = 0
        · have e3 : c3 = c1 * a2 := by rw [hc3, z2]; ring
          have n3 : c1 * a2 ≠ 0 := mul_ne_zero z1 (ne_zero_of_val_eq_one v ha2)
          rw [e3]
          simp only [Xs, z2, if_true, if_neg z1, if_neg n3, tz_zero_left, add_zero]
          exact case_Ic h z1 ha2 hd1 hd2 hd3u had hd3c
        · by_cases z3 : c3 = 0
          · simp only [Xs, z3, if_true, if_neg z1, if_neg z2, tz_zero_left]
            exact case_Ie h z1 z2 ha2 hd1 hd2 hd3u had hd3c (by rw [← hc3, z3])
          · simp only [Xs, if_neg z1, if_neg z2, if_neg z3]
            exact case_Id h z1 z2 z3 ha2 hd1 hd2 hd3u had hd3c hc3
    · -- Case II
      have hc2 : v c2 = 1 := le_antisymm ic2 (not_lt.mp h2)
      have hc20 := ne_zero_of_val_eq_one v hc2
      have hd10 := ne_zero_of_val_eq_one v hd1
      have hc3v : v c3 = 1 := by
        have : c3 = d1 * c2 + c1 * a2 := by rw [hc3]; ring
        rw [this, v.map_add_eq_of_lt_left]
        · rw [map_mul, hd1, hc2, mul_one]
        · rw [map_mul, map_mul, hd1, hc2, mul_one]
          exact mul_lt_one_of_lt_of_le h1 ia2
      have hc30 := ne_zero_of_val_eq_one v hc3v
      simp only [sL, if_pos h1, if_neg h2, if_neg hc3v.not_lt, add_zero]
      by_cases z1 : c1 = 0
      · simp only [Xs, z1, if_true, if_neg hc20, if_neg hc30, tz_zero_left, add_zero]
        exact tz_units h (by rw [map_div₀, hc3v, hd1, div_one])
          (by rw [map_div₀, hc3v, hc2, div_one])
      · simp only [Xs, if_neg z1, if_neg hc20, if_neg hc30]
        exact case_IIb h z1 h1 hc2 hd1 ia2 hc3
  · have hc1 : v c1 = 1 := le_antisymm ic1 (not_lt.mp h1)
    have hc10 := ne_zero_of_val_eq_one v hc1
    by_cases h2 : v c2 < 1
    · -- Case III
      have hbc : v (b2 * c2) < 1 := by
        rw [map_mul, mul_comm]; exact mul_lt_one_of_lt_of_le h2 ib2
      have had : v (a2 * d2 - 1) < 1 := by
        rwa [show a2 * d2 - 1 = b2 * c2 by linear_combination det2]
      have hada : v (a2 * d2) = 1 := by
        have := v.map_one_add_of_lt had
        rwa [add_sub_cancel] at this
      obtain ⟨ha2, hd2⟩ := val_eq_one_of_mul v ia2 id2 hada
      have hd20 := ne_zero_of_val_eq_one v hd2
      have hc3v : v c3 = 1 := by
        rw [hc3, v.map_add_eq_of_lt_left]
        · rw [map_mul, hc1, ha2, mul_one]
        · rw [map_mul, map_mul, hc1, ha2, mul_one, mul_comm]
          exact mul_lt_one_of_lt_of_le h2 id1
      have hc30 := ne_zero_of_val_eq_one v hc3v
      simp only [sL, if_neg h1, if_pos h2, if_neg hc3v.not_lt, add_zero]
      by_cases z2 : c2 = 0
      · simp only [Xs, z2, if_true, if_neg hc10, if_neg hc30, tz_zero_left, add_zero]
        exact tz_units h (by rw [map_div₀, hc3v, hc1, div_one])
          (by rw [map_div₀, hc3v, hd2, div_one])
      · simp only [Xs, if_neg z2, if_neg hc10, if_neg hc30]
        exact case_IIIb h z2 h2 hc1 ha2 hd2 id1 had hc3
    · -- Case IV
      have hc2 : v c2 = 1 := le_antisymm ic2 (not_lt.mp h2)
      have hc20 := ne_zero_of_val_eq_one v hc2
      simp only [sL, if_neg h1, if_neg h2, add_zero]
      have hr3 : v c3 < 1 → v d3 = 1 := by
        intro h3
        by_contra hne
        have hd3lt : v d3 < 1 := lt_of_le_of_ne id3 hne
        have : v c1 < 1 := by
          rw [hk]
          refine v.map_sub_lt ?_ ?_ <;> rw [map_mul]
          · exact mul_lt_one_of_lt_of_le h3 id2
          · exact mul_lt_one_of_lt_of_le hd3lt ic2
        exact h1 this
      by_cases z3 : c3 = 0
      · have hd3u : v d3 = 1 := hr3 (by rw [z3, map_zero]; exact zero_lt_one)
        simp only [Xs, z3, if_true, if_neg hc10, if_neg hc20, tz_zero_left, ite_self]
        exact tz_units h (by rw [map_div₀, hd3u, hc1, div_one])
          (by rw [map_div₀, hd3u, hc2, div_one])
      · simp only [Xs, if_neg z3, if_neg hc10, if_neg hc20]
        by_cases h3 : v c3 < 1
        · rw [if_pos h3]
          exact case_IVc h z3 h3 hc1 hc2 (hr3 h3) id2 hk
        · have hc3v : v c3 = 1 := le_antisymm ic3 (not_lt.mp h3)
          rw [if_neg h3]
          exact tz_units h (by rw [map_div₀, hc3v, hc1, div_one])
            (by rw [map_div₀, hc3v, hc2, div_one])

/-! ### Matrix form -/

open Matrix

/-- `X(g)`: the lower-left entry if it is non-zero, else the lower-right entry. -/
def X (g : Matrix.SpecialLinearGroup (Fin 2) F) : F := Xs (g.1 1 0) (g.1 1 1)

theorem X_ne_zero (g : Matrix.SpecialLinearGroup (Fin 2) F) : X g ≠ 0 := by
  unfold X Xs
  split_ifs with hc
  · intro hd
    have := g.2
    rw [Matrix.det_fin_two, hc, hd] at this
    simp at this
  · exact hc

/-- `X(g)` as a unit. -/
def Xu (g : Matrix.SpecialLinearGroup (Fin 2) F) : Fˣ := Units.mk0 (X g) (X_ne_zero g)

@[simp] theorem coe_Xu (g : Matrix.SpecialLinearGroup (Fin 2) F) : (Xu g : F) = X g := rfl

/-- Kubota's local cocycle formula on rational matrices, for the symbol `t`. -/
def sigmaLoc (t : Fˣ → Fˣ → A) (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) F) : A :=
  t (Xu (g₁ * g₂) / Xu g₁) (Xu (g₁ * g₂) / Xu g₂)

/-- Kubota's local splitting function on integral matrices. -/
def sLoc (v : Valuation F Γ₀) (t : Fˣ → Fˣ → A) (g : Matrix.SpecialLinearGroup (Fin 2) F) : A :=
  sL v t (g.1 1 0) (g.1 1 1)

/-- **Kubota's local lemma** for a tame symbol: on `v`-integral matrices of determinant one,
`σ_v(g₁, g₂) = s_v(g₁ g₂) - s_v(g₁) - s_v(g₂)`. -/
theorem kubota_local {v : Valuation F Γ₀} {t : Fˣ → Fˣ → A} (h : IsTameSymbol v t)
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) F)
    (hg₁ : ∀ i j, v (g₁.1 i j) ≤ 1) (hg₂ : ∀ i j, v (g₂.1 i j) ≤ 1) :
    sigmaLoc t g₁ g₂ + sLoc v t g₁ + sLoc v t g₂ = sLoc v t (g₁ * g₂) := by
  have hσ : sigmaLoc t g₁ g₂ = tz t (X (g₁ * g₂) / X g₁) (X (g₁ * g₂) / X g₂) := by
    unfold sigmaLoc
    rw [← tz_coe t]
    push_cast
    rfl
  rw [hσ]
  have det1 := g₁.2
  have det2 := g₂.2
  rw [Matrix.det_fin_two] at det1 det2
  have hr1 : v (g₁.1 1 0) = 1 ∨ v (g₁.1 1 1) = 1 := by
    by_contra hcon
    push Not at hcon
    have hc : v (g₁.1 1 0) < 1 := lt_of_le_of_ne (hg₁ 1 0) hcon.1
    have hd : v (g₁.1 1 1) < 1 := lt_of_le_of_ne (hg₁ 1 1) hcon.2
    have : v (1 : F) < 1 := by
      rw [← det1]
      refine v.map_sub_lt ?_ ?_ <;> rw [map_mul]
      · rw [mul_comm]; exact mul_lt_one_of_lt_of_le hd (hg₁ 0 0)
      · rw [mul_comm]; exact mul_lt_one_of_lt_of_le hc (hg₁ 0 1)
    rw [map_one] at this
    exact lt_irrefl _ this
  have hc3 : (g₁ * g₂).1 1 0 = g₁.1 1 0 * g₂.1 0 0 + g₁.1 1 1 * g₂.1 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hd3 : (g₁ * g₂).1 1 1 = g₁.1 1 0 * g₂.1 0 1 + g₁.1 1 1 * g₂.1 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact kubota_scalar h hr1 (hg₁ 1 0) (hg₁ 1 1) (hg₂ 0 0) (hg₂ 0 1) (hg₂ 1 0) (hg₂ 1 1)
    det2 hc3 hd3

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Pkg
/-!
# WP-A: the global cubic symbol package and the `S`-Hilbert pairing

`CubicPkg F` is a universe-polymorphic, completion-free form of `C0Y.SymbolPkg F 3`: local cubic
Hilbert symbols `hv v : Fˣ →* Fˣ →* μ₃(F)` evaluated on *global* elements, with Steinberg, the
product formula, triviality on units and the tame formula at places prime to `3`, and local
constancy (`deep`).  Everything in WP-A is derived from a `CubicPkg`.

The orientation is pinned by the field `tame`: `hv v a π ≡ a^{(Nv-1)/3} (mod v)` for a `v`-unit
`a` and a uniformizer `π`.

Main results: `CubicPkg.skew`, `CubicPkg.self`, `CubicPkg.isTame` (the bridge to `A_Local`),
`CubicPkg.tame_zpow` (A1 for a unit against any element), `CubicPkg.tame_formula` (A1),
`CubicPkg.HS` (the pairing `(a,b)_S`), `CubicPkg.HS_mul_prod` (A2, product formula),
`CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`, `CubicPkg.exists_isDeepLevel`,
`CubicPkg.HS_deep_right/left` (A4).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable (F : Type*) [Field F] [NumberField F]

/-- Cubic Hilbert symbols at the finite places, on global elements. -/
structure CubicPkg where
  /-- the local symbol at `v` on global elements -/
  hv : HeightOneSpectrum (𝓞 F) → Fˣ →* Fˣ →* rootsOfUnity 3 F
  steinberg : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ), hv v a (-a) = 1
  prod_eq_one : ∀ (a b : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ v ∉ T, hv v a b = 1) → ∏ v ∈ T, hv v a b = 1
  unit_unit : ∀ v : HeightOneSpectrum (𝓞 F), (3 : 𝓞 F) ∉ v.asIdeal → ∀ a b : Fˣ,
    v.valuation F (a : F) = 1 → v.valuation F (b : F) = 1 → hv v a b = 1
  tame : ∀ v : HeightOneSpectrum (𝓞 F), (3 : 𝓞 F) ∉ v.asIdeal → ∀ (a π : Fˣ) (ω : F),
    v.valuation F (a : F) = 1 → v.valuation F (π : F) = WithZero.exp (-1 : ℤ) → ω ^ 3 = 1 →
    v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 3) - ω) < 1 →
    (((hv v a π : Fˣ)) : F) = ω
  deep : ∀ v : HeightOneSpectrum (𝓞 F), ∃ N : ℕ, ∀ a b : Fˣ,
    v.valuation F ((b : F) - 1) ≤ WithZero.exp (-(N : ℤ)) → hv v a b = 1

variable {F}

theorem root_pow_three {M : Type*} [CommMonoid M] (z : rootsOfUnity 3 M) : z ^ 3 = 1 := by
  have := z.2
  rw [mem_rootsOfUnity] at this
  exact Subtype.ext (by simpa using this)

/-- Only finitely many finite places see a given non-zero element as a non-unit. -/
theorem finite_val_ne_one (x : F) (hx : x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F x ≠ 1}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hfa := Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)
  have hfb := Ideal.finite_factors (I := Ideal.span {b}) (by simpa using hb0)
  refine (hfa.union hfb).subset fun v hv => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Ideal.dvd_span_singleton] at hcon
  apply hv
  rw [map_div₀, (v.valuation_eq_one_iff_notMem (K := F)).mpr hcon.1,
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hcon.2, div_one]

theorem val_pow_sub_pow_lt_one (v : HeightOneSpectrum (𝓞 F)) {a b : F}
    (ha : v.valuation F a ≤ 1) (hb : v.valuation F b ≤ 1) (hab : v.valuation F (a - b) < 1)
    (m : ℕ) : v.valuation F (a ^ m - b ^ m) < 1 := by
  rw [← Commute.geom_sum₂_mul (Commute.all a b) m, map_mul]
  have hG : v.valuation F (∑ i ∈ Finset.range m, a ^ i * b ^ (m - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' ha _) (pow_le_one' hb _)
  calc _ ≤ 1 * v.valuation F (a - b) := mul_le_mul_left hG _
    _ < 1 := by rw [one_mul]; exact hab

/-- Every non-zero value of the valuation is `exp (-n)`. -/
theorem exists_val_eq_exp (v : HeightOneSpectrum (𝓞 F)) (b : Fˣ) :
    ∃ n : ℤ, v.valuation F (b : F) = WithZero.exp (-n) := by
  have h0 : v.valuation F (b : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr b.ne_zero
  exact ⟨-WithZero.log (v.valuation F (b : F)), by rw [neg_neg, WithZero.exp_log h0]⟩

theorem exists_uniformizer_unit (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fˣ, v.valuation F (π : F) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  exact ⟨Units.mk0 π h0, hπ⟩

namespace CubicPkg

variable (P : CubicPkg F)

theorem neg_one_left (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) : P.hv v (-1) a = 1 := by
  have h : (-1 : Fˣ) = (-1) ^ 3 := by norm_num
  rw [h, map_pow, MonoidHom.pow_apply, root_pow_three]

theorem neg_one_right (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) : P.hv v a (-1) = 1 := by
  have h : (-1 : Fˣ) = (-1) ^ 3 := by norm_num
  rw [h, map_pow, root_pow_three]

/-- (A4) local alternation. -/
theorem self (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) : P.hv v a a = 1 := by
  have h := P.steinberg v a
  rwa [← neg_one_mul, map_mul, P.neg_one_right, one_mul] at h

/-- Local skew-symmetry. -/
theorem skew (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) : P.hv v a b * P.hv v b a = 1 := by
  have h := P.self v (a * b)
  simp only [map_mul, MonoidHom.mul_apply, P.self] at h
  simpa [mul_comm] using h

theorem skew' (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) : P.hv v a b = (P.hv v b a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (P.skew v a b)

/-- A unit against an element of valuation `exp (-n)`. -/
theorem hv_unit_zpow (v : HeightOneSpectrum (𝓞 F)) (h3 : (3 : 𝓞 F) ∉ v.asIdeal) (u b π : Fˣ)
    (hu : v.valuation F (u : F) = 1) (hπ : v.valuation F (π : F) = WithZero.exp (-1 : ℤ))
    (n : ℤ) (hb : v.valuation F (b : F) = WithZero.exp (-n)) :
    P.hv v u b = (P.hv v u π) ^ n := by
  have hw : v.valuation F ((b / π ^ n : Fˣ) : F) = 1 := by
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, map_div₀, map_zpow₀, hb, hπ,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, div_self WithZero.exp_ne_zero]
  have hbw : b = π ^ n * (b / π ^ n) := by rw [mul_div_cancel]
  rw [hbw, map_mul, map_zpow, P.unit_unit v h3 u _ hu hw, mul_one]

/-- An element `≡ 1` at a tame place pairs trivially with everything (left slot). -/
theorem one_add_left (v : HeightOneSpectrum (𝓞 F)) (h3 : (3 : 𝓞 F) ∉ v.asIdeal) (b a : Fˣ)
    (hb : v.valuation F ((b : F) - 1) < 1) : P.hv v b a = 1 := by
  have hb1 : v.valuation F (b : F) = 1 := by
    have := (v.valuation F).map_one_add_of_lt hb
    rwa [add_sub_cancel] at this
  obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
  obtain ⟨n, hn⟩ := exists_val_eq_exp v a
  have h1 : ((P.hv v b π : Fˣ) : F) = 1 := by
    apply P.tame v h3 b π 1 hb1 hπ (one_pow 3)
    have := val_pow_sub_pow_lt_one v hb1.le (by rw [map_one]) hb
      ((Ideal.absNorm v.asIdeal - 1) / 3)
    rwa [one_pow] at this
  have h1' : P.hv v b π = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa using h1
  rw [P.hv_unit_zpow v h3 b a π hb1 hπ n hn, h1', one_zpow]

theorem one_add_right (v : HeightOneSpectrum (𝓞 F)) (h3 : (3 : 𝓞 F) ∉ v.asIdeal) (a b : Fˣ)
    (hb : v.valuation F ((b : F) - 1) < 1) : P.hv v a b = 1 := by
  rw [P.skew', P.one_add_left v h3 b a hb, inv_one]

/-- The symbol at a place prime to `3` is a tame symbol in the sense of `A_Local`. -/
theorem isTame (v : HeightOneSpectrum (𝓞 F)) (h3 : (3 : 𝓞 F) ∉ v.asIdeal) :
    IsTameSymbol (v.valuation F) (fun a b : Fˣ => Additive.ofMul (P.hv v a b)) where
  mul_left a b c := by simp [map_mul]
  mul_right a b c := by simp [map_mul]
  unit_unit a b ha hb := by simp [P.unit_unit v h3 a b ha hb]
  steinberg a := by simp [P.steinberg v a]
  neg_one_left a := by simp [P.neg_one_left v a]
  one_add a b hb := by simp [P.one_add_right v h3 a b hb]

/-- (A1), unit against arbitrary: `(a, b)_v = ω^{ord_v b}` with `ω ≡ a^{(Nv-1)/3}`. -/
theorem tame_zpow (v : HeightOneSpectrum (𝓞 F)) (h3 : (3 : 𝓞 F) ∉ v.asIdeal) (a b : Fˣ) (ω : F)
    (ha : v.valuation F (a : F) = 1) (n : ℤ) (hb : v.valuation F (b : F) = WithZero.exp (-n))
    (hω : ω ^ 3 = 1)
    (hc : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 3) - ω) < 1) :
    (((P.hv v a b : Fˣ)) : F) = ω ^ n := by
  obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
  rw [P.hv_unit_zpow v h3 a b π ha hπ n hb, Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val,
    P.tame v h3 a π ω ha hπ hω hc]

/-! ### The `S`-part -/

open Classical in
/-- The finite places dividing `𝔪`, as a finset (empty if `𝔪 = ⊥`). -/
def sFin (𝔪 : Ideal (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 F)) :=
  if h : (placesOf 𝔪).Finite then h.toFinset else ∅

theorem mem_sFin {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ sFin 𝔪 ↔ 𝔪 ≤ v.asIdeal := by
  have hfin : (placesOf 𝔪).Finite := by
    have := Ideal.finite_factors (I := 𝔪) h𝔪
    refine this.subset fun v hv => ?_
    rw [Set.mem_ofPred_eq, Ideal.dvd_iff_le]
    exact hv
  rw [sFin, dif_pos hfin, Set.Finite.mem_toFinset]
  rfl

/-- The cubic `S`-Hilbert pairing `(a, b)_S = ∏_{v ∣ 𝔪} (a, b)_v`. -/
def HS (𝔪 : Ideal (𝓞 F)) : Fˣ →* Fˣ →* rootsOfUnity 3 F :=
  ∏ v ∈ sFin 𝔪, P.hv v

theorem HS_apply (𝔪 : Ideal (𝓞 F)) (a b : Fˣ) : P.HS 𝔪 a b = ∏ v ∈ sFin 𝔪, P.hv v a b := by
  simp [HS]

/-- (A4) alternation. -/
theorem HS_self (𝔪 : Ideal (𝓞 F)) (a : Fˣ) : P.HS 𝔪 a a = 1 := by
  rw [P.HS_apply]
  exact Finset.prod_eq_one fun v _ => P.self v a

theorem HS_skew (𝔪 : Ideal (𝓞 F)) (a b : Fˣ) : P.HS 𝔪 a b * P.HS 𝔪 b a = 1 := by
  rw [P.HS_apply, P.HS_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun v _ => P.skew v a b

theorem HS_skew' (𝔪 : Ideal (𝓞 F)) (a b : Fˣ) : P.HS 𝔪 a b = (P.HS 𝔪 b a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (P.HS_skew 𝔪 a b)

theorem HS_neg_one_left (𝔪 : Ideal (𝓞 F)) (a : Fˣ) : P.HS 𝔪 (-1) a = 1 := by
  rw [P.HS_apply]
  exact Finset.prod_eq_one fun v _ => P.neg_one_left v a

theorem HS_neg_left (𝔪 : Ideal (𝓞 F)) (a b : Fˣ) : P.HS 𝔪 (-a) b = P.HS 𝔪 a b := by
  rw [← neg_one_mul, map_mul, MonoidHom.mul_apply, P.HS_neg_one_left, one_mul]

/-- (A2) **product formula**, finset form: if `T` is a finite set of exterior places outside of
which `(a, b)_v = 1`, then `(a, b)_S · ∏_{v ∈ T} (a, b)_v = 1`. -/
theorem HS_mul_prod {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (a b : Fˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ∀ v ∈ T, ¬ 𝔪 ≤ v.asIdeal)
    (hcov : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v ∉ T → P.hv v a b = 1) :
    P.HS 𝔪 a b * ∏ v ∈ T, P.hv v a b = 1 := by
  classical
  have hdisj : Disjoint (sFin 𝔪) T := by
    rw [Finset.disjoint_left]
    intro v hv hvT
    exact hT v hvT ((mem_sFin h𝔪 v).mp hv)
  rw [P.HS_apply, ← Finset.prod_union hdisj]
  apply P.prod_eq_one
  intro v hv
  rw [Finset.mem_union, not_or] at hv
  exact hcov v (fun h => hv.1 ((mem_sFin h𝔪 v).mpr h)) hv.2

/-- (A2), with the covering hypothesis in terms of valuations. -/
theorem HS_mul_prod' {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 F), (3 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal) (a b : Fˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ∀ v ∈ T, ¬ 𝔪 ≤ v.asIdeal)
    (hcov : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v ∉ T →
      v.valuation F (a : F) = 1 ∧ v.valuation F (b : F) = 1) :
    P.HS 𝔪 a b * ∏ v ∈ T, P.hv v a b = 1 :=
  P.HS_mul_prod h𝔪 a b T hT fun v hv hvT =>
    P.unit_unit v (fun h => hv (h3 v h)) a b (hcov v hv hvT).1 (hcov v hv hvT).2

open Classical in
/-- The exterior places at which `x` is not a unit (empty for `x = 0`). -/
def extSupp (𝔪 : Ideal (𝓞 F)) (x : F) : Finset (HeightOneSpectrum (𝓞 F)) :=
  if hx : x ≠ 0 then (finite_val_ne_one x hx).toFinset.filter fun v => ¬ 𝔪 ≤ v.asIdeal else ∅

open Classical in
theorem mem_extSupp {𝔪 : Ideal (𝓞 F)} {x : F} (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ extSupp 𝔪 x ↔ ¬ 𝔪 ≤ v.asIdeal ∧ v.valuation F x ≠ 1 := by
  rw [extSupp, dif_pos hx, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, and_comm]

theorem not_le_of_mem_extSupp {𝔪 : Ideal (𝓞 F)} {x : F} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∈ extSupp 𝔪 x) : ¬ 𝔪 ≤ v.asIdeal := by
  by_cases hx : x ≠ 0
  · exact ((mem_extSupp hx v).mp hv).1
  · rw [extSupp, dif_neg hx] at hv
    simp at hv

/-! ### Deep units -/

/-- `N` is a *deep level* for `𝔪`: elements `≡ 1 mod v^N` at all `v ∣ 𝔪` pair trivially at
those places. -/
def IsDeepLevel (𝔪 : Ideal (𝓞 F)) (N : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → ∀ a b : Fˣ,
    v.valuation F ((b : F) - 1) ≤ WithZero.exp (-(N : ℤ)) → P.hv v a b = 1

/-- (A4) the `S`-pairing is trivial on deep units (right slot). -/
theorem HS_deep_right {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {N : ℕ} (hN : P.IsDeepLevel 𝔪 N)
    (a b : Fˣ)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
      v.valuation F ((b : F) - 1) ≤ WithZero.exp (-(N : ℤ))) :
    P.HS 𝔪 a b = 1 := by
  rw [P.HS_apply]
  exact Finset.prod_eq_one fun v hv => hN v ((mem_sFin h𝔪 v).mp hv) a b (hb v ((mem_sFin h𝔪 v).mp hv))

/-- (A4) the `S`-pairing is trivial on deep units (left slot). -/
theorem HS_deep_left {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {N : ℕ} (hN : P.IsDeepLevel 𝔪 N)
    (b a : Fˣ)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
      v.valuation F ((b : F) - 1) ≤ WithZero.exp (-(N : ℤ))) :
    P.HS 𝔪 b a = 1 := by
  rw [P.HS_skew', P.HS_deep_right h𝔪 hN a b hb, inv_one]

end CubicPkg

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Residue
/-!
# WP-A: the exterior cubic residue symbol and reciprocity

* `Good 𝔪`: the standing hypotheses on the modulus (`𝔪 ≠ ⊥`, every prime over `6` divides `𝔪`,
  `R = SInt 𝔪` is a PID in the form "every extended ideal is principal");
  `exists_cutoff_good` gives it from `SmallPrimesDvd N₀ 𝔪`.
* `cubicExt ι 𝔪 d c = ∏_{P ∉ S, P ∣ c} χ_P(d)^{2 v_P(c)}` in terms of the goal's
  `sexticResidueSymbol`.
* `cubicExt_eq_prod`: `(d/c) = ι ∏_v (d, c)_v` over the exterior places dividing `c`.
* `cubicExt_reciprocity` (A3): `(d/c) = (c/d) · (c, d)_S` — with the orientation of `CubicPkg`
  the sign in MATH.md (A3) is `+1`.
* unit laws, multiplicativity, dependence on `d mod c` only.

The first section is a universe-polymorphic copy of `C0Y.val_generator`, `C0Y.sextic_spec`
(`Solutions/Artin/C0/C0YR.lean`, stated there for `F : Type`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

section Copy

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem sInt_val_le_one (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

theorem coe_algebraMap_sInt (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

/-- Elements of `P · SInt` have `v_P < 1`. -/
theorem val_lt_one_of_mem_map (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    {z : SInt 𝔪} (hz : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (z : F) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_algebraMap_sInt]
    exact (v.valuation_lt_one_iff_mem (K := F) a).mpr ha
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Subalgebra.coe_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul a x _ hx =>
    simp only [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * v.valuation F (x : F) :=
          mul_le_mul_left (sInt_val_le_one a v hv) _
      _ < 1 := by rw [one_mul]; exact hx

/-- Valuations of a generator of `P · SInt`. -/
theorem val_generator (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ w.asIdeal → w ≠ v → w.valuation F (p : F) = 1 := by
  have hpmem : p ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hp]; exact Ideal.subset_span rfl
  have hlt := val_lt_one_of_mem_map v hv hpmem
  -- every `a ∈ P` is a multiple of `p` in `SInt`
  have hdiv : ∀ a ∈ v.asIdeal, ∃ s : SInt 𝔪, algebraMap (𝓞 F) F a = (p : F) * (s : F) := by
    intro a ha
    have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ Ideal.span {p} := by
      rw [hp]; exact Ideal.mem_map_of_mem _ ha
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp this
    refine ⟨s, ?_⟩
    rw [← coe_algebraMap_sInt (𝔪 := 𝔪), ← hs, Subalgebra.coe_mul, mul_comm]
  refine ⟨?_, fun w hw hwv => ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer' F
    have hπmem : π ∈ v.asIdeal := by
      rw [← v.valuation_lt_one_iff_mem (K := F), hπ]; exact by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    obtain ⟨s, hs⟩ := hdiv π hπmem
    have h1 : v.valuation F (p : F) * v.valuation F (s : F) = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← hs, hπ]
    have hs1 := sInt_val_le_one s v hv
    have hp0 : v.valuation F (p : F) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact WithZero.exp_ne_zero h1.symm
    have hge : WithZero.exp (-1 : ℤ) ≤ v.valuation F (p : F) := by
      rw [← h1]; exact mul_le_of_le_one_right' hs1
    have hle : v.valuation F (p : F) ≤ WithZero.exp (-1 : ℤ) := by
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hp0
      rw [← hk] at hlt ⊢
      rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl] at hlt
      have : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [this, WithZero.exp_lt_exp] at hlt
      rw [this, WithZero.exp_le_exp]
      omega
    exact le_antisymm hle hge
  · -- `P ⊄ w`
    have hnle : ¬ v.asIdeal ≤ w.asIdeal := by
      intro hle
      have := v.isMaximal.eq_of_le w.isPrime.ne_top hle
      exact hwv (HeightOneSpectrum.ext this.symm)
    obtain ⟨a, ha, haw⟩ := Set.not_subset.mp hnle
    obtain ⟨s, hs⟩ := hdiv a ha
    have h1 : w.valuation F (p : F) * w.valuation F (s : F) = 1 := by
      rw [← map_mul, ← hs]; exact (w.valuation_eq_one_iff_notMem (K := F)).mpr haw
    have hp1 := sInt_val_le_one p w hw
    have hs1 := sInt_val_le_one s w hw
    by_contra hne
    have hlt : w.valuation F (p : F) < 1 := lt_of_le_of_ne hp1 hne
    have : w.valuation F (p : F) * w.valuation F (s : F) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt hs1) le_rfl
    rw [h1] at this
    exact lt_irrefl _ this

/-- Elements of `SInt` with `v_P < 1` lie in `P · SInt` (given a generator). -/
theorem mem_map_of_val_lt_one (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (z : SInt 𝔪)
    (hz : v.valuation F (z : F) < 1) : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨hpv, hpw⟩ := val_generator v hv p hp
  have hp0 : (p : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hpv; exact WithZero.exp_ne_zero hpv.symm
  have hq : (z : F) / (p : F) ∈ (placesOf 𝔪).integer F := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      rw [map_div₀, hpv]
      by_cases hz0 : w.valuation F (z : F) = 0
      · rw [hz0, zero_div]; exact zero_le
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hz0
      rw [← hk] at hz ⊢
      have e : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [e, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [e, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [map_div₀, hpw w hw hwv, div_one]
      exact sInt_val_le_one z w hw
  have : z = p * ⟨(z : F) / (p : F), hq⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    field_simp
  rw [← hp, this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- The sextic residue symbol at an exterior prime with generator: `6 ∣ N P − 1`, and
`χ_P(y) = ι ξ` for the sixth root of unity `ξ ≡ y^{(N P − 1)/6} (mod P)`. -/
theorem sextic_spec (ι : F →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    (p : SInt 𝔪) (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (y : SInt 𝔪)
    (hy : v.valuation F (y : F) = 1) :
    6 ∣ Ideal.absNorm v.asIdeal - 1 ∧ ∃ ξ : 𝓞 F, ξ ^ 6 = 1 ∧
      v.valuation F ((y : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - algebraMap (𝓞 F) F ξ) < 1 ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal y = ι (algebraMap (𝓞 F) F ξ) := by
  classical
  set P := v.asIdeal with hPdef
  let : Field (𝓞 F ⧸ P) := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P v.ne_bot
  let : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hinj : ∀ a b : 𝓞 F, a ^ 6 = 1 → b ^ 6 = 1 →
      Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → a = b := fun a b ha hb h =>
    C0R.eq_of_pow_six P h6 ha hb (Ideal.Quotient.eq.mp h)
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk P z6) 6 := by
    refine ⟨by rw [← map_pow, hz6.pow_eq_one, map_one], fun l hl => ?_⟩
    have : z6 ^ l = 1 := hinj _ _ (by rw [← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow])
      (one_pow 6) (by rw [map_pow, hl, map_one])
    exact hz6.dvd_of_pow_eq_one l this
  have h6N : 6 ∣ Ideal.absNorm P - 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk P z6) (hη.ne_zero (by norm_num))
    rw [hcard] at this
    exact hη.dvd_of_pow_eq_one _ this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (y : F) hy.le
  have hd : (d : 𝓞 F) ∉ P := d.2
  have hdv : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    intro h0; rw [h0, map_zero] at hdv; exact zero_ne_one hdv
  have hn : (n : 𝓞 F) ∉ P := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, hy, hdv, one_mul]
  set k := (Ideal.absNorm P - 1) / 6 with hk
  set u : 𝓞 F ⧸ P := Ideal.Quotient.mk P n * (Ideal.Quotient.mk P d)⁻¹ with hu
  have hmd : Ideal.Quotient.mk P (d : 𝓞 F) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmn : Ideal.Quotient.mk P n ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hu0 : u ≠ 0 := mul_ne_zero hmn (inv_ne_zero hmd)
  have hu6 : (u ^ k) ^ 6 = 1 := by
    rw [← pow_mul, hk, Nat.div_mul_cancel h6N, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one u hu0
  obtain ⟨i, -, hi⟩ := hη.eq_pow_of_pow_eq_one hu6
  set ξ := z6 ^ i with hξ
  have hξ6 : ξ ^ 6 = 1 := by rw [hξ, ← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow]
  have hcong : n ^ k - ξ * (d : 𝓞 F) ^ k ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, map_pow, map_pow, hi,
      hu, mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hmd), mul_one, sub_self]
  have hval : v.valuation F ((y : F) ^ k - algebraMap (𝓞 F) F ξ) < 1 := by
    have hyd : (y : F) = algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F d := by
      rw [← hnd, mul_div_cancel_right₀ _ hdF]
    have : (y : F) ^ k - algebraMap (𝓞 F) F ξ =
        algebraMap (𝓞 F) F (n ^ k - ξ * (d : 𝓞 F) ^ k) / (algebraMap (𝓞 F) F d) ^ k := by
      rw [hyd, eq_div_iff (pow_ne_zero _ hdF)]
      simp only [map_sub, map_mul, map_pow]
      rw [sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdF)]
    rw [this, map_div₀, map_pow, hdv, one_pow, div_one]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr hcong
  refine ⟨h6N, ξ, hξ6, hval, ?_⟩
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set Q := P.map f
  have hyQ : y ∉ Q := fun h => by
    have := val_lt_one_of_mem_map v hv h; rw [hy] at this; exact lt_irrefl _ this
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h
    have := val_lt_one_of_mem_map v hv h
    have e : ((6 : SInt 𝔪) : F) = algebraMap (𝓞 F) F 6 := by rw [map_ofNat]; rfl
    rw [e, (v.valuation_eq_one_iff_notMem (K := F)).mpr h6] at this
    exact lt_irrefl _ this
  have hex : f ξ - y ^ k ∈ Q := by
    apply mem_map_of_val_lt_one v hv p hp
    have e : ((f ξ - y ^ k : SInt 𝔪) : F) = -((y : F) ^ k - algebraMap (𝓞 F) F ξ) := by
      simp [f, coe_algebraMap_sInt]
    rw [e, Valuation.map_neg]; exact hval
  unfold sexticResidueSymbol
  rw [if_neg (by rwa [Ideal.Quotient.eq_zero_iff_mem])]
  have hE : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q y ^ k :=
    ⟨ξ, hξ6, by rw [← map_pow, Ideal.Quotient.eq]; exact hex⟩
  rw [dif_pos hE]
  have hch := hE.choose_spec
  have hsub : f hE.choose - f ξ ∈ Q := by
    rw [← Ideal.Quotient.eq, hch.2, ← map_pow, Ideal.Quotient.eq]
    have : y ^ k - f ξ = -(f ξ - y ^ k) := by ring
    rw [this]; exact Q.neg_mem hex
  have heq := C0R.eq_of_pow_six Q h6Q (by rw [← map_pow, hch.1, map_one])
    (by rw [← map_pow, hξ6, map_one]) hsub
  have : hE.choose = ξ := by
    have h' := congrArg (fun z : SInt 𝔪 => (z : F)) heq
    simp only [f, coe_algebraMap_sInt] at h'
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F h'
  rw [this]

end Copy

variable {F : Type*} [Field F] [NumberField F]

/-- The standing hypotheses on the modulus `𝔪` (all follow from `SmallPrimesDvd N₀ 𝔪` for a
suitable `N₀`, see `exists_cutoff_good`). -/
structure Good (𝔪 : Ideal (𝓞 F)) : Prop where
  ne_bot : 𝔪 ≠ ⊥
  six : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal
  principal : ∀ I : Ideal (𝓞 F), (I.map (algebraMap (𝓞 F) (SInt 𝔪))).IsPrincipal

namespace Good

variable {𝔪 : Ideal (𝓞 F)} (h : Good 𝔪)
include h

theorem three (v : HeightOneSpectrum (𝓞 F)) (h3 : (3 : 𝓞 F) ∈ v.asIdeal) : 𝔪 ≤ v.asIdeal := by
  apply h.six v
  have : (6 : 𝓞 F) = 3 * 2 := by norm_num
  rw [this]
  exact v.asIdeal.mul_mem_right _ h3

theorem six_notMem (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) :
    (6 : 𝓞 F) ∉ v.asIdeal := fun h6 => hv (h.six v h6)

theorem three_notMem (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) :
    (3 : 𝓞 F) ∉ v.asIdeal := fun h3 => hv (h.three v h3)

end Good

/-- Cube roots of unity of `F`, read in `ℂ` through `ι`. -/
def iota3 (ι : F →+* ℂ) : rootsOfUnity 3 F →* ℂ :=
  (ι : F →* ℂ).comp ((Units.coeHom F).comp (rootsOfUnity 3 F).subtype)

@[simp] theorem iota3_apply (ι : F →+* ℂ) (z : rootsOfUnity 3 F) :
    iota3 ι z = ι ((z : Fˣ) : F) := rfl

theorem iota3_inv (ι : F →+* ℂ) (z : rootsOfUnity 3 F) : iota3 ι z⁻¹ = (iota3 ι z)⁻¹ := by
  have h : iota3 ι z⁻¹ * iota3 ι z = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  exact eq_inv_of_mul_eq_one_left h

/-- The (additive) order of `x` at `v`. -/
def ordv (v : HeightOneSpectrum (𝓞 F)) (x : F) : ℤ := -WithZero.log (v.valuation F x)

theorem val_eq_exp_ordv (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F x = WithZero.exp (-ordv v x) := by
  rw [ordv, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)]

theorem ordv_nonneg (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0)
    (h : v.valuation F x ≤ 1) : 0 ≤ ordv v x := by
  rw [val_eq_exp_ordv v hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

variable (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)}

/-- At an exterior place, the cubic Hilbert symbol of a `v`-unit `d` against `b` is the square of
the goal's sextic residue symbol, to the power `ord_v b`. -/
theorem iota3_hv_eq (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (d : SInt 𝔪) (du b : Fˣ)
    (hdu : (du : F) = d) (hd : v.valuation F (d : F) = 1) (n : ℤ)
    (hb : v.valuation F (b : F) = WithZero.exp (-n)) :
    iota3 ι (P.hv v du b) = (sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2) ^ n := by
  obtain ⟨p, hp⟩ := (hG.principal v.asIdeal).principal
  have hp' : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := hp.symm
  obtain ⟨h6N, ξ, hξ6, hval, hsym⟩ :=
    sextic_spec ι v hv p hp' hz6 (hG.six_notMem v hv) d hd
  have hω : (algebraMap (𝓞 F) F ξ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, ← map_pow, hξ6, map_one]
  have hexp : (Ideal.absNorm v.asIdeal - 1) / 3 = (Ideal.absNorm v.asIdeal - 1) / 6 * 2 := by
    obtain ⟨t, ht⟩ := h6N
    rw [ht]
    omega
  have hc : v.valuation F ((du : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 3)
      - algebraMap (𝓞 F) F ξ ^ 2) < 1 := by
    rw [hexp, pow_mul, hdu]
    exact val_pow_sub_pow_lt_one v (by rw [map_pow, hd, one_pow]) (v.valuation_le_one ξ) hval 2
  have := P.tame_zpow v (hG.three_notMem v hv) du b _ (by rw [hdu]; exact hd) n hb hω hc
  rw [iota3_apply, this, map_zpow₀, map_pow, hsym]

/-- The **exterior cubic residue symbol** `(d/c) = ∏_{P ∉ S, P ∣ c} χ_P(d)^{2 v_P(c)}` for
`c, d ∈ R`, with `χ_P` the goal's `sexticResidueSymbol` (value `1` for `c = 0`). -/
def cubicExt (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (d c : SInt 𝔪) : ℂ :=
  ∏ v ∈ CubicPkg.extSupp 𝔪 (c : F),
    sexticResidueSymbol ι 𝔪 v.asIdeal d ^ (2 * (ordv v (c : F)).toNat)

open CubicPkg in
/-- `(d/c) = ι ∏_{v ∈ T} (d, c)_v` for any finite set `T` of exterior places containing the
exterior support of `c` and on which `d` is a unit. -/
theorem cubicExt_eq_prod (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (c d : SInt 𝔪) (cu du : Fˣ) (hcu : (cu : F) = c) (hdu : (du : F) = d)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v ∈ T, ¬ 𝔪 ≤ v.asIdeal ∧ v.valuation F (d : F) = 1)
    (hsupp : extSupp 𝔪 (c : F) ⊆ T) :
    cubicExt ι 𝔪 d c = iota3 ι (∏ v ∈ T, P.hv v du cu) := by
  have hc0 : (c : F) ≠ 0 := hcu ▸ cu.ne_zero
  rw [map_prod, cubicExt, ← Finset.prod_subset hsupp]
  · refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨hext, hne⟩ := (mem_extSupp hc0 v).mp hv
    have hd := (hT v (hsupp hv)).2
    have hb : v.valuation F (cu : F) = WithZero.exp (-ordv v (c : F)) := by
      rw [hcu]; exact val_eq_exp_ordv v hc0
    have hnn : 0 ≤ ordv v (c : F) := ordv_nonneg v hc0 (sInt_val_le_one c v hext)
    rw [iota3_hv_eq ι P hG hz6 v hext d du cu hdu hd _ hb, pow_mul]
    conv_rhs => rw [← Int.toNat_of_nonneg hnn, zpow_natCast]
  · intro v hvT hvn
    have hext := (hT v hvT).1
    have hc1 : v.valuation F (c : F) = 1 := by
      by_contra hne
      exact hvn ((mem_extSupp hc0 v).mpr ⟨hext, hne⟩)
    have : P.hv v du cu = 1 :=
      P.unit_unit v (hG.three_notMem v hext) du cu (hdu ▸ (hT v hvT).2) (hcu ▸ hc1)
    rw [this, map_one]

theorem extSupp_eq_empty {x : F}
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F x = 1) :
    CubicPkg.extSupp 𝔪 x = ∅ := by
  by_cases h0 : x ≠ 0
  · ext v
    rw [CubicPkg.mem_extSupp h0]
    simp only [Finset.notMem_empty, iff_false, not_and, not_not]
    exact hx v
  · rw [CubicPkg.extSupp, dif_neg h0]

/-- `(d/c) = 1` if `c` is an `S`-unit. -/
theorem cubicExt_of_unit_right (d c : SInt 𝔪)
    (hc : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (c : F) = 1) :
    cubicExt ι 𝔪 d c = 1 := by
  rw [cubicExt, extSupp_eq_empty hc, Finset.prod_empty]

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Kubota
/-!
# WP-A: the Kubota symbol on `SL₂(R)`, `R = SInt 𝔪`

* `kappa ι 𝔪 γ = (d/c)⁻¹` (`1` if `c = 0`), with `(d/c) = cubicExt`.
* `sigmaS P 𝔪 g₁ g₂ = (X(g₁g₂)/X(g₁), X(g₁g₂)/X(g₂))_S` on rational matrices.
* `kappa_mul` (Lemma A5): `κ(γ₁γ₂) = κ(γ₁) κ(γ₂) σ_S(γ₁,γ₂)⁻¹`.

  **Orientation.**  With the symbols oriented by `CubicPkg.tame` the exponent is `ε = -1`
  (equivalently `ε = +1` for the opposite pairing `(b,a)_S`).  It is forced: for
  `γ₁ = diag(ε₁⁻¹, ε₁)` with an `S`-unit `ε₁`, and `c₂ ≠ 0`,
  `κ(γ₁γ₂)/κ(γ₂) = (ε₁/c₂)⁻¹ = (c₂, ε₁)_S⁻¹ = σ_S(γ₁, γ₂)⁻¹` by the unit law.
* `sigmaS_eq_one`: `σ_S(g₁, g₂) = 1` as soon as `a₂`, `d₁` and `d₃` lie in the radical of `(·,·)_S`.
* `Gamma 𝔪 𝔫`: the image in `SL₂(R)` of the principal congruence subgroup of `SL₂(𝓞 F)` of level
  `𝔫`; `kappa_mul_of_mem_Gamma` (Corollary A6): `κ` is multiplicative on `Γ(𝔫)` for `𝔫 ≤ 𝔪^N`,
  `N ≥ 1` any deep level of the package (`CubicPkg.IsDeepLevel`); `kappaHom`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots Matrix

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-- `SL₂(R) → SL₂(F)`. -/
def toF (𝔪 : Ideal (𝓞 F)) :
    Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪) →* Matrix.SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.map ((placesOf 𝔪).integer F).val.toRingHom

@[simp] theorem toF_apply (𝔪 : Ideal (𝓞 F)) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (i j : Fin 2) : (toF 𝔪 γ).1 i j = ((γ.1 i j : SInt 𝔪) : F) := rfl

open Classical in
/-- The **Kubota symbol** `κ(γ) = (d/c)⁻¹` on `SL₂(R)` (`1` if `c = 0`). -/
def kappa (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) : ℂ :=
  if γ.1 1 0 = 0 then 1 else (cubicExt ι 𝔪 (γ.1 1 1) (γ.1 1 0))⁻¹

/-- The `S`-part of Kubota's cocycle on rational matrices:
`σ_S(g₁, g₂) = (X(g₁g₂)/X(g₁), X(g₁g₂)/X(g₂))_S`. -/
def sigmaS (P : CubicPkg F) (𝔪 : Ideal (𝓞 F)) (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) F) :
    rootsOfUnity 3 F :=
  P.HS 𝔪 (Xu (g₁ * g₂) / Xu g₁) (Xu (g₁ * g₂) / Xu g₂)

/-- Kubota's local splitting function at `v`, multiplicatively. -/
def sM (P : CubicPkg F) (v : HeightOneSpectrum (𝓞 F)) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    rootsOfUnity 3 F :=
  Additive.toMul (sLoc (v.valuation F) (fun a b : Fˣ => Additive.ofMul (P.hv v a b)) g)

variable {𝔪 : Ideal (𝓞 F)}

theorem entry_val_le_one (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (i j : Fin 2) :
    v.valuation F ((toF 𝔪 γ).1 i j) ≤ 1 :=
  sInt_val_le_one (γ.1 i j) v hv

theorem det_coe (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    ((γ.1 0 0 : SInt 𝔪) : F) * (γ.1 1 1 : SInt 𝔪) - (γ.1 0 1 : SInt 𝔪) * (γ.1 1 0 : SInt 𝔪)
      = 1 := by
  have := γ.2
  rw [Matrix.det_fin_two] at this
  have h := congrArg (fun x : SInt 𝔪 => (x : F)) this
  simpa using h

/-- The bottom row of `γ ∈ SL₂(R)` is primitive at every exterior place. -/
theorem row_coprime (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) :
    v.valuation F ((γ.1 1 0 : SInt 𝔪) : F) = 1 ∨ v.valuation F ((γ.1 1 1 : SInt 𝔪) : F) = 1 := by
  by_contra hcon
  rw [not_or] at hcon
  have hc : v.valuation F ((γ.1 1 0 : SInt 𝔪) : F) < 1 :=
    lt_of_le_of_ne (sInt_val_le_one _ v hv) hcon.1
  have hd : v.valuation F ((γ.1 1 1 : SInt 𝔪) : F) < 1 :=
    lt_of_le_of_ne (sInt_val_le_one _ v hv) hcon.2
  have : v.valuation F (1 : F) < 1 := by
    rw [← det_coe γ]
    refine (v.valuation F).map_sub_lt ?_ ?_ <;> rw [map_mul]
    · rw [mul_comm]; exact mul_lt_one_of_lt_of_le hd (sInt_val_le_one _ v hv)
    · rw [mul_comm]; exact mul_lt_one_of_lt_of_le hc (sInt_val_le_one _ v hv)
  rw [map_one] at this
  exact lt_irrefl _ this

/-- Kubota's local lemma at an exterior place, multiplicatively. -/
theorem hv_mul_sM (P : CubicPkg F) (hG : Good 𝔪) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ 𝔪 ≤ v.asIdeal) (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    P.hv v (Xu (toF 𝔪 γ₁ * toF 𝔪 γ₂) / Xu (toF 𝔪 γ₁)) (Xu (toF 𝔪 γ₁ * toF 𝔪 γ₂) / Xu (toF 𝔪 γ₂))
      * sM P v (toF 𝔪 γ₁) * sM P v (toF 𝔪 γ₂) = sM P v (toF 𝔪 (γ₁ * γ₂)) := by
  have h := kubota_local (P.isTame v (hG.three_notMem v hv)) (toF 𝔪 γ₁) (toF 𝔪 γ₂)
    (entry_val_le_one γ₁ v hv) (entry_val_le_one γ₂ v hv)
  have h' := congrArg Additive.toMul h
  rw [map_mul]
  simpa [sM, sigmaLoc] using h'

open CubicPkg in
/-- `κ(γ) = ι ∏_{v ∈ T} s_v(γ)` for every finite set `T` of exterior places containing the
exterior support of `c`. -/
theorem kappa_eq_prod (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ∀ v ∈ T, ¬ 𝔪 ≤ v.asIdeal)
    (hsupp : extSupp 𝔪 ((γ.1 1 0 : SInt 𝔪) : F) ⊆ T) :
    kappa ι 𝔪 γ = iota3 ι (∏ v ∈ T, sM P v (toF 𝔪 γ)) := by
  classical
  set c : SInt 𝔪 := γ.1 1 0 with hcdef
  set d : SInt 𝔪 := γ.1 1 1 with hddef
  have hsM : ∀ v, sM P v (toF 𝔪 γ) = Additive.toMul
      (sL (v.valuation F) (fun a b : Fˣ => Additive.ofMul (P.hv v a b)) (c : F) (d : F)) :=
    fun v => rfl
  by_cases hc : c = 0
  · have h1 : ∀ v ∈ T, sM P v (toF 𝔪 γ) = 1 := by
      intro v _
      rw [hsM, hc]
      simp [sL]
    rw [kappa, if_pos hc, Finset.prod_eq_one h1, map_one]
  have hc0 : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  rw [kappa, if_neg hc]
  by_cases hd : d = 0
  · -- then `c` is an `S`-unit
    have hcu : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (c : F) = 1 := by
      intro v hv
      rcases row_coprime γ v hv with h | h
      · exact h
      · rw [← hddef, hd] at h
        simp at h
    have h1 : ∀ v ∈ T, sM P v (toF 𝔪 γ) = 1 := by
      intro v hv
      rw [hsM, sL, if_neg (by rw [hcu v (hT v hv)]; exact lt_irrefl _)]
      rfl
    rw [Finset.prod_eq_one h1, map_one, cubicExt_of_unit_right ι d c hcu, inv_one]
  have hd0 : (d : F) ≠ 0 := fun h => hd (Subtype.ext h)
  set cu : Fˣ := Units.mk0 (c : F) hc0 with hcu
  set du : Fˣ := Units.mk0 (d : F) hd0 with hdu
  have hval : ∀ v ∈ extSupp 𝔪 (c : F), ¬ 𝔪 ≤ v.asIdeal ∧ v.valuation F (d : F) = 1 := by
    intro v hv
    obtain ⟨hext, hne⟩ := (mem_extSupp hc0 v).mp hv
    exact ⟨hext, (row_coprime γ v hext).resolve_left hne⟩
  rw [cubicExt_eq_prod ι P hG hz6 c d cu du rfl rfl (extSupp 𝔪 (c : F)) hval subset_rfl,
    ← iota3_inv, ← Finset.prod_inv_distrib, ← Finset.prod_subset hsupp]
  · congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨hext, hne⟩ := (mem_extSupp hc0 v).mp hv
    have hlt : v.valuation F (c : F) < 1 := lt_of_le_of_ne (sInt_val_le_one c v hext) hne
    rw [hsM, sL, if_pos hlt, ← P.skew' v cu du]
    have : tz (fun a b : Fˣ => Additive.ofMul (P.hv v a b)) (c : F) (d : F)
        = Additive.ofMul (P.hv v cu du) := tz_coe _ cu du
    rw [this]
    rfl
  · intro v hvT hvn
    have hc1 : v.valuation F (c : F) = 1 := by
      by_contra hne
      exact hvn ((mem_extSupp hc0 v).mpr ⟨hT v hvT, hne⟩)
    rw [hsM, sL, if_neg (by rw [hc1]; exact lt_irrefl _)]
    rfl

open CubicPkg in
/-- **Lemma A5 (Kubota's relation on `SL₂(R)`).**
`κ(γ₁γ₂) = κ(γ₁) κ(γ₂) σ_S(γ₁, γ₂)⁻¹`. -/
theorem kappa_mul (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    kappa ι 𝔪 (γ₁ * γ₂) = kappa ι 𝔪 γ₁ * kappa ι 𝔪 γ₂ *
      (iota3 ι (sigmaS P 𝔪 (toF 𝔪 γ₁) (toF 𝔪 γ₂)))⁻¹ := by
  classical
  set r1 : Fˣ := Xu (toF 𝔪 γ₁ * toF 𝔪 γ₂) / Xu (toF 𝔪 γ₁) with hr1
  set r2 : Fˣ := Xu (toF 𝔪 γ₁ * toF 𝔪 γ₂) / Xu (toF 𝔪 γ₂) with hr2
  set T : Finset (HeightOneSpectrum (𝓞 F)) :=
    extSupp 𝔪 ((γ₁.1 1 0 : SInt 𝔪) : F) ∪ extSupp 𝔪 ((γ₂.1 1 0 : SInt 𝔪) : F) ∪
      extSupp 𝔪 (((γ₁ * γ₂).1 1 0 : SInt 𝔪) : F) ∪ extSupp 𝔪 (r1 : F) ∪ extSupp 𝔪 (r2 : F)
    with hTdef
  have hT : ∀ v ∈ T, ¬ 𝔪 ≤ v.asIdeal := by
    intro v hv
    simp only [hTdef, Finset.mem_union] at hv
    rcases hv with (((h | h) | h) | h) | h <;> exact not_le_of_mem_extSupp h
  have k1 := kappa_eq_prod ι P hG hz6 γ₁ T hT (by
    intro v hv; simp only [hTdef, Finset.mem_union]; tauto)
  have k2 := kappa_eq_prod ι P hG hz6 γ₂ T hT (by
    intro v hv; simp only [hTdef, Finset.mem_union]; tauto)
  have k3 := kappa_eq_prod ι P hG hz6 (γ₁ * γ₂) T hT (by
    intro v hv; simp only [hTdef, Finset.mem_union]; tauto)
  have hloc : ∏ v ∈ T, sM P v (toF 𝔪 (γ₁ * γ₂))
      = (∏ v ∈ T, P.hv v r1 r2) * (∏ v ∈ T, sM P v (toF 𝔪 γ₁))
        * ∏ v ∈ T, sM P v (toF 𝔪 γ₂) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v hv => (hv_mul_sM P hG v (hT v hv) γ₁ γ₂).symm
  have hprod := P.HS_mul_prod' hG.ne_bot hG.three r1 r2 T hT (by
    intro v hv hvT
    simp only [hTdef, Finset.mem_union, not_or] at hvT
    obtain ⟨⟨-, h1⟩, h2⟩ := hvT
    rw [mem_extSupp r1.ne_zero] at h1
    rw [mem_extSupp r2.ne_zero] at h2
    exact ⟨by_contra fun h => h1 ⟨hv, h⟩, by_contra fun h => h2 ⟨hv, h⟩⟩)
  have hσ : ∏ v ∈ T, P.hv v r1 r2 = (sigmaS P 𝔪 (toF 𝔪 γ₁) (toF 𝔪 γ₂))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, mul_comm]
    exact hprod
  rw [k3, hloc, hσ, map_mul, map_mul, iota3_inv, ← k1, ← k2]
  ring

/-! ### Triviality of `σ_S` on deep matrices -/

/-- `x` lies in the radical of the `S`-pairing (for instance a cube, or a deep unit). -/
def IsRad (P : CubicPkg F) (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ u : Fˣ, (u : F) = x ∧ ∀ y : Fˣ, P.HS 𝔪 u y = 1

/-! ### The principal congruence subgroup and Corollary A6 -/

/-- `Γ(𝔫)`: the image in `SL₂(R)` of the principal congruence subgroup of `SL₂(𝓞 F)` of level
`𝔫`. -/
def Gamma (𝔪 𝔫 : Ideal (𝓞 F)) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :=
  Subgroup.map (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk 𝔫)).ker

theorem mem_Gamma_iff {𝔫 : Ideal (𝓞 F)} (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    γ ∈ Gamma 𝔪 𝔫 ↔ ∃ γ₀ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F),
      (∀ i j, γ₀.1 i j - (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i j ∈ 𝔫) ∧
      Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) (SInt 𝔪)) γ₀ = γ := by
  rw [Gamma, Subgroup.mem_map]
  refine exists_congr fun γ₀ => and_congr_left fun _ => ?_
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F ⧸ 𝔫) => g.1 i j) h
    simp only [Matrix.SpecialLinearGroup.coe_one] at this
    rw [← Ideal.Quotient.eq]
    rw [show (Ideal.Quotient.mk 𝔫) ((1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i j)
      = (1 : Matrix (Fin 2) (Fin 2) (𝓞 F ⧸ 𝔫)) i j by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]]
    exact this
  · intro h
    ext i j
    have := Ideal.Quotient.eq.mpr (h i j)
    rw [show (Ideal.Quotient.mk 𝔫) ((1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i j)
      = (1 : Matrix (Fin 2) (Fin 2) (𝓞 F ⧸ 𝔫)) i j by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]] at this
    simpa using this

/-- `6` lies in some prime of `𝓞 F`; hence a good modulus has a place. -/
theorem Good.exists_place (hG : Good 𝔪) : ∃ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal := by
  have h6 : ¬ IsUnit (6 : 𝓞 F) := by
    intro hu
    have h1 := (NumberField.isUnit_iff_norm (K := F)).mp hu
    have h2 : (RingOfIntegers.norm ℚ (6 : 𝓞 F) : ℚ) = 6 ^ Module.finrank ℚ F := by
      rw [RingOfIntegers.coe_norm]
      have : ((6 : 𝓞 F) : F) = algebraMap ℚ F 6 :=
        (map_ofNat (algebraMap (𝓞 F) F) 6).trans (map_ofNat (algebraMap ℚ F) 6).symm
      rw [this, Algebra.norm_algebraMap]
    rw [h2, abs_pow] at h1
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    have : (1 : ℚ) < |6| ^ Module.finrank ℚ F :=
      one_lt_pow₀ (by norm_num) hpos.ne'
    linarith
  have hne : Ideal.span {(6 : 𝓞 F)} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hMbot : M ≠ ⊥ := by
    intro h
    rw [h] at hle
    have h6' : (6 : 𝓞 F) = 0 := by
      have := hle (Ideal.subset_span rfl)
      simpa using this
    have := congrArg (algebraMap (𝓞 F) F) h6'
    simp at this
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hMbot⟩
  exact ⟨v, hG.six v (hle (Ideal.subset_span rfl))⟩

end ArtinKP.A
end
end


