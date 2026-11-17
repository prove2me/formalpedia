-- Prove2me | Definitions.Def_TateZ2xZ10Reduction
-- name    : TateZ2xZ10Reduction
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:31.603804+00:00
-- url     : https://prove2.me/theorems/dcf487fe-9b70-4722-b2fe-d1989fd795f0
-- title:
--   Coordinate-change reduction for $ℤ/2ℤ × ℤ/10ℤ$ torsion
-- statement:
--   This technical file defines the Tate normal-form curve, its order-$10$ condition and two-torsion cubic, the recovered parameter $u$, tangent translation and scaling variable changes, formulas for the resulting Tate coefficients, and reverse rational functions. It also defines forward and inverse maps on affine points and packages them as equivalences and additive equivalences. These carriers implement the explicit reduction from a general marked torsion configuration to the parameterized Tate family.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
/-!
# Tate-normal-form reduction layer for `ZMod 2 × ZMod 10`

This file builds the forward-direction reduction up to the current formal wall.

API survey, from the local tree and Mathlib as used here:

* Nonzero affine coordinates.  `WeierstrassCurve.Affine.Point W` is the
  inductive type `zero | some x y h`.  Mathlib provides `Point.mk`,
  `Point.some_ne_zero`, and `Point.xRep`; there is no `Point.pointEquiv` in the
  local Mathlib checkout.  No extra abstraction is needed to extract `(x,y)`
  from a proof `P ≠ 0`: case-splitting on `P` gives the affine coordinates.

* Variable changes.  `WeierstrassCurve.VariableChange R` exists and acts on
  Weierstrass curves by `(X,Y) ↦ (u^2 X + r, u^3 Y + u^2 s X + t)`.  The hard
  Mathlib survey for this file found the following.

  * `Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean` provides the
    curve-level group action, coefficient formulas `variableChange_a₁` through
    `variableChange_a₆`, preservation of `IsElliptic`, base-change compatibility
    for variable changes, and `variableChange_j`.
  * `Affine.Basic` provides ring-hom/base-change transport for equations and
    nonsingularity, plus only a specialized
    `equation_iff_variableChange`/`nonsingular_iff_variableChange` for translating
    a point to `(0,0)`.  It does not provide a general point map for
    `(u,r,s,t)`.
  * `Affine.Point` provides `Point.map` only for base change along algebra
    homomorphisms; its `map_add'` proof uses the affine addition formulas under
    ring homs.  There is no `Point.mapEquiv`, `Affine.map`, or `≃+` for
    variable changes.
  * `Jacobian.Point` provides `toAffineAddEquiv` between Jacobian and affine
    point groups and base-change lemmas for Jacobian formulas, but no
    `VariableChange` action on Jacobian/projective point classes.
  * `IsomOfJ.lean` constructs curve-level variable changes from equal
    `j`-invariants; it does not construct point-group isomorphisms.

  Consequently the point-level transport below is built directly.  The forward
  map sends an old affine point `(x,y)` on `W` to the new coordinates
  `X = u^{-2}(x-r)`, `Y = u^{-3}(y-s(x-r)-t)` on `C • W`; the inverse map uses
  the defining coordinate formulas.  The additive proof reduces to the affine
  slope identity `ℓ' = u^{-1}(ℓ-s)` and ring-checked equivariance of `addX` and
  `addY`.

* Computing `n • P`.  The affine point file has explicit group-law lemmas:
  `Point.add_of_X_ne`, `Point.add_of_Y_eq`, `Point.add_self_of_Y_eq`,
  `Point.add_self_of_Y_ne`, and the underlying formulas `slope`, `addX`,
  `addY`.  This supports direct coordinate calculations, as in the existing
  obstruction files.  Mathlib does not provide Tate normal form, Kubert's
  order-10 table, or a canned theorem that a point of order `10` can be
  normalized to `(0,0)` with the roadmap's `b,c` formulas.

* Division polynomials.  `DivisionPolynomial/Basic.lean` defines
  `ψ₂`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ`, `ΨSq`, `Ψ`, `ψ`, `Φ`, and `φ`, with
  map/base-change lemmas; `DivisionPolynomial/Degree.lean` proves degree and
  leading-coefficient facts.  The only direct bridge to the 2-torsion cubic is
  `Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly`.  The survey found no
  theorem connecting `P` satisfying `n • P = 0` or `addOrderOf P = n` to
  evaluating `ψ n`, `Ψ n`, `preΨ n`, or `Φ n` at the coordinates of `P`.
  Thus division polynomials do not currently avoid the explicit `5P`
  group-law computation needed for order `10`.

The proven content below is split accordingly:

* the pure finite-group extraction from an injective `ZMod 2 × ZMod 10`;
* raw Tate-normal-form and change-of-variable algebra;
* one precisely named helper marking the missing point-level group-law
  preservation/normalization theorem.
-/

open scoped WeierstrassCurve.Affine

namespace Scratch.TateZ2xZ10Reduction

noncomputable section

/-- The Tate normal form `y^2 + (1-c)xy - by = x^3 - bx^2`. -/
def tateNormalFormCurve (b c : ℚ) : WeierstrassCurve ℚ where
  a₁ := 1 - c
  a₂ := -b
  a₃ := -b
  a₄ := 0
  a₆ := 0

/-- The order-10 Tate condition from the roadmap. -/
def Phi10 (b c : ℚ) : ℚ :=
  b ^ 3 - 3 * b ^ 2 * c ^ 2 - 2 * b ^ 2 * c
    + b * c ^ 4 + 3 * b * c ^ 3 + b * c ^ 2 + c ^ 5

/-- The two-torsion cubic specialized to Tate normal form. -/
def tateTwoTorsionCubic (b c X : ℚ) : ℚ :=
  4 * X ^ 3 + ((1 - c) ^ 2 - 4 * b) * X ^ 2 + 2 * b * (c - 1) * X + b ^ 2

/-- The rational `u` parameter recovered from Tate parameters `b,c`. -/
def uOfTateParameters (b c : ℚ) : ℚ :=
  (5 * b ^ 2 - 2 * b * c ^ 2 - 6 * b * c - 2 * c ^ 3 + c ^ 2) / (b - c) ^ 2

/-- Tangent slope at `(x₀,y₀)` in a general Weierstrass equation. -/
def tangentSlope (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) : ℚ :=
  (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
    / (2 * y₀ + W.a₁ * x₀ + W.a₃)

/-- The translation/shear sending `(x₀,y₀)` to `(0,0)` with tangent `Y=0`. -/
def translateToOriginTangent (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := x₀
  s := tangentSlope W x₀ y₀
  t := y₀

/-- Scaling `X = ρ^2 X'`, `Y = ρ^3 Y'`. -/
def scaleByRho (ρ : ℚ) (hρ : ρ ≠ 0) : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 ρ hρ
  r := 0
  s := 0
  t := 0

/-- Tate `b` after the roadmap's scaling step. -/
def tateBFromCoefficients (a₂' a₃' : ℚ) : ℚ :=
  -a₂' ^ 3 / a₃' ^ 2

/-- Tate `c` after the roadmap's scaling step. -/
def tateCFromCoefficients (a₁' a₂' a₃' : ℚ) : ℚ :=
  1 - a₁' * a₂' / a₃'

/-- The transformed `x`-coordinate of an auxiliary point under the scaling step. -/
def scaledAuxiliaryX (xTold x₀ ρ : ℚ) : ℚ :=
  (xTold - x₀) / ρ ^ 2

def reverseUNum (b c : ℚ) : ℚ :=
  5 * b ^ 2 - 2 * b * c ^ 2 - 6 * b * c - 2 * c ^ 3 + c ^ 2

def reverseUDen (b c : ℚ) : ℚ :=
  (b - c) ^ 2

def reverseDNum (b c : ℚ) : ℚ :=
  reverseUNum b c ^ 2 - 4 * reverseUNum b c * reverseUDen b c - reverseUDen b c ^ 2

def uNumBezoutA (b c : ℚ) : ℚ :=
  -4 * c ^ 3 + 11 * c ^ 4 - 13 * c ^ 5 - 2 * c ^ 6
    + b * (20 * c ^ 2 + 5 * c ^ 3 + 5 * c ^ 4)

def uNumBezoutB (b c : ℚ) : ℚ :=
  4 * c ^ 6 - 7 * c ^ 7 - c ^ 8
    + b * (4 * c ^ 3 + 9 * c ^ 4 + 6 * c ^ 5 + 3 * c ^ 6)
    + b ^ 2 * (-4 * c ^ 2 - c ^ 3 - c ^ 4)

def reverseBQuotient (b c : ℚ) : ℚ :=
  128 * b ^ 2 * c ^ 5 - 896 * b ^ 3 * c ^ 4 + 2304 * b ^ 4 * c ^ 3
    - 2816 * b ^ 5 * c ^ 2 + 1664 * b ^ 6 * c - 384 * b ^ 7
    + 16 * c ^ 8 - 64 * b * c ^ 7 + 64 * b ^ 2 * c ^ 6
    - 512 * b ^ 3 * c ^ 5 + 928 * b ^ 4 * c ^ 4 + 192 * b ^ 5 * c ^ 3
    - 1088 * b ^ 6 * c ^ 2 + 384 * b ^ 7 * c + 80 * b ^ 8
    - 16 * c ^ 9 + 48 * b * c ^ 8 - 304 * b ^ 2 * c ^ 7
    - 368 * b ^ 3 * c ^ 6 + 656 * b ^ 4 * c ^ 5 + 592 * b ^ 5 * c ^ 4
    - 336 * b ^ 6 * c ^ 3 - 272 * b ^ 7 * c ^ 2 - 48 * b * c ^ 9
    - 272 * b ^ 2 * c ^ 8 - 352 * b ^ 3 * c ^ 7 + 96 * b ^ 4 * c ^ 6
    + 400 * b ^ 5 * c ^ 5 + 176 * b ^ 6 * c ^ 4 - 32 * b * c ^ 10
    - 128 * b ^ 2 * c ^ 9 - 192 * b ^ 3 * c ^ 8 - 128 * b ^ 4 * c ^ 7
    - 32 * b ^ 5 * c ^ 6

def reverseCQuotient (b c : ℚ) : ℚ :=
  8 * c ^ 3 - 40 * b * c ^ 2 + 56 * b ^ 2 * c - 24 * b ^ 3
    - 4 * c ^ 4 - 20 * b * c ^ 3 + 4 * b ^ 2 * c ^ 2 + 20 * b ^ 3 * c
    - 8 * c ^ 5 - 16 * b * c ^ 4 - 8 * b ^ 2 * c ^ 3

def tateX5 (b c : ℚ) : ℚ :=
  -b * c * (b - c ^ 2 - c) / (b - c) ^ 2

def tateY5 (b c : ℚ) : ℚ :=
  b * c ^ 2 * (b ^ 2 - b * c - c ^ 3) / (b - c) ^ 3

lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

def tateOriginPoint (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

/--
The transformed `X`-coordinate under a Weierstrass variable change.  This is
the inverse coordinate map from old coordinates on `W` to new coordinates on
`C • W`.
-/
def variableChangePointX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) : ℚ :=
  (C.u⁻¹ : ℚ) ^ 2 * (x - C.r)

/-- The transformed `Y`-coordinate under a Weierstrass variable change. -/
def variableChangePointY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) : ℚ :=
  (C.u⁻¹ : ℚ) ^ 3 * (y - C.s * (x - C.r) - C.t)

/-- The old `x`-coordinate recovered from new coordinates. -/
def variableChangePointInvX (C : WeierstrassCurve.VariableChange ℚ) (X : ℚ) : ℚ :=
  (C.u : ℚ) ^ 2 * X + C.r

/-- The old `y`-coordinate recovered from new coordinates. -/
def variableChangePointInvY (C : WeierstrassCurve.VariableChange ℚ) (X Y : ℚ) : ℚ :=
  (C.u : ℚ) ^ 3 * Y + (C.u : ℚ) ^ 2 * C.s * X + C.t

lemma variableChangePoint_equation
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) {x y : ℚ}
    (h : WeierstrassCurve.Affine.Equation W x y) :
    WeierstrassCurve.Affine.Equation (C • W)
      (variableChangePointX C x) (variableChangePointY C x y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  unfold variableChangePointX variableChangePointY
  rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  simp only [Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  linear_combination h

lemma variableChangePointInv_equation
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) {X Y : ℚ}
    (h : WeierstrassCurve.Affine.Equation (C • W) X Y) :
    WeierstrassCurve.Affine.Equation W
      (variableChangePointInvX C X) (variableChangePointInvY C X Y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  unfold variableChangePointInvX variableChangePointInvY
  rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆] at h
  simp only [Units.val_inv_eq_inv_val] at h
  field_simp [C.u.ne_zero] at h
  linear_combination h

lemma variableChangePointInvX_pointX
    (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) :
    variableChangePointInvX C (variableChangePointX C x) = x := by
  simp [variableChangePointInvX, variableChangePointX]

lemma variableChangePointInvY_pointY
    (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) :
    variableChangePointInvY C (variableChangePointX C x) (variableChangePointY C x y) = y := by
  simp [variableChangePointInvY, variableChangePointX, variableChangePointY]
  field_simp [C.u.ne_zero]
  ring

lemma variableChangePointX_invX
    (C : WeierstrassCurve.VariableChange ℚ) (X : ℚ) :
    variableChangePointX C (variableChangePointInvX C X) = X := by
  simp [variableChangePointInvX, variableChangePointX]

lemma variableChangePointY_invY
    (C : WeierstrassCurve.VariableChange ℚ) (X Y : ℚ) :
    variableChangePointY C (variableChangePointInvX C X)
      (variableChangePointInvY C X Y) = Y := by
  simp [variableChangePointInvX, variableChangePointInvY, variableChangePointY]
  field_simp [C.u.ne_zero]
  ring

lemma variableChangePointX_eq_iff
    (C : WeierstrassCurve.VariableChange ℚ) {x₁ x₂ : ℚ} :
    variableChangePointX C x₁ = variableChangePointX C x₂ ↔ x₁ = x₂ := by
  unfold variableChangePointX
  constructor
  · intro h
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero] at h
    linarith
  · intro h
    simp [h]

lemma variableChangePointY_eq_iff
    (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) {y₁ y₂ : ℚ} :
    variableChangePointY C x y₁ = variableChangePointY C x y₂ ↔ y₁ = y₂ := by
  unfold variableChangePointY
  constructor
  · intro h
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero] at h
    linarith
  · intro h
    simp [h]

lemma variableChangePointY_negY
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) :
    variableChangePointY C x (WeierstrassCurve.Affine.negY W x y) =
      WeierstrassCurve.Affine.negY (C • W)
        (variableChangePointX C x) (variableChangePointY C x y) := by
  simp [variableChangePointX, variableChangePointY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₃]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

lemma variableChange_slope_of_X_ne
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rw [WeierstrassCurve.Affine.slope_of_X_ne]
  · unfold variableChangePointX variableChangePointY
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero, sub_ne_zero.mpr hx]
    ring
  · exact fun h => hx ((variableChangePointX_eq_iff C).mp h)

lemma variableChange_slope_of_Y_ne
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ ≠ WeierstrassCurve.Affine.negY W x₂ y₂) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  have hy_eq : y₁ = y₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
  have hy_self : y₁ ≠ WeierstrassCurve.Affine.negY W x₁ y₁ := by
    intro h
    apply hy
    rw [← hx, ← hy_eq]
    exact h
  have hden : x₁ * W.a₁ + W.a₃ + y₁ * 2 ≠ 0 := by
    intro hden
    apply hy_self
    rw [WeierstrassCurve.Affine.negY]
    linarith
  have hmul :
      (x₁ * W.a₁ + W.a₃ + y₁ * 2) *
          (x₁ * W.a₁ + W.a₃ + y₁ * 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  have htarget_hx :
      variableChangePointX C x₁ = variableChangePointX C x₂ := by
    simp [hx]
  have htarget_hy :
      variableChangePointY C x₁ y₁ ≠
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂) := by
    intro h
    apply hy
    rw [← hx]
    apply (variableChangePointY_eq_iff C x₁).mp
    rw [h]
    rw [hx, variableChangePointY_negY]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne htarget_hx htarget_hy]
  unfold variableChangePointX variableChangePointY
  simp [WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  rw [← sub_eq_zero]
  ring_nf
  convert
    (show C.s *
        (1 - (x₁ * W.a₁ + W.a₃ + y₁ * 2) *
          (x₁ * W.a₁ + W.a₃ + y₁ * 2)⁻¹) = 0 by
      rw [hmul]
      ring) using 1
  ring

lemma variableChange_slope
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂)) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  by_cases hx : x₁ = x₂
  · exact variableChange_slope_of_Y_ne W C h₁ h₂ hx (fun hy => hxy ⟨hx, hy⟩)
  · exact variableChange_slope_of_X_ne W C hx

lemma variableChange_nonvertical
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂)) :
    ¬(variableChangePointX C x₁ = variableChangePointX C x₂ ∧
      variableChangePointY C x₁ y₁ =
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂)) := by
  rintro ⟨hx', hy'⟩
  apply hxy
  have hx : x₁ = x₂ := (variableChangePointX_eq_iff C).mp hx'
  refine ⟨hx, ?_⟩
  rw [← hx]
  apply (variableChangePointY_eq_iff C x₁).mp
  rw [hy', hx, ← variableChangePointY_negY]

lemma variableChange_vertical
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ}
    (hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂) :
    variableChangePointX C x₁ = variableChangePointX C x₂ ∧
      variableChangePointY C x₁ y₁ =
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂) := by
  rcases hxy with ⟨hx, hy⟩
  constructor
  · simp [hx]
  · rw [hy, ← variableChangePointY_negY, hx]

lemma variableChange_addX
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ x₂ ℓ : ℚ) :
    variableChangePointX C (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ) =
      WeierstrassCurve.Affine.addX (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        ((C.u⁻¹ : ℚ) * (ℓ - C.s)) := by
  simp [variableChangePointX, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

lemma variableChange_addY
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ x₂ y₁ ℓ : ℚ) :
    variableChangePointY C (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ)
        (WeierstrassCurve.Affine.addY W x₁ x₂ y₁ ℓ) =
      WeierstrassCurve.Affine.addY (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) ((C.u⁻¹ : ℚ) * (ℓ - C.s)) := by
  simp [variableChangePointX, variableChangePointY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

noncomputable def variableChangePointMap
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point W → WeierstrassCurve.Affine.Point (C • W)
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some x y h =>
      WeierstrassCurve.Affine.Point.some
        (variableChangePointX C x) (variableChangePointY C x y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePoint_equation W C h.left))

noncomputable def variableChangePointMapInv
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (C • W) → WeierstrassCurve.Affine.Point W
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some X Y h =>
      WeierstrassCurve.Affine.Point.some
        (variableChangePointInvX C X) (variableChangePointInvY C X Y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePointInv_equation W C h.left))

lemma variableChangePointMap_leftInverse
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    Function.LeftInverse (variableChangePointMapInv W C) (variableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp [variableChangePointMap, variableChangePointMapInv,
        variableChangePointInvX_pointX, variableChangePointInvY_pointY]

lemma variableChangePointMap_rightInverse
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    Function.RightInverse (variableChangePointMapInv W C) (variableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some X Y h =>
      simp [variableChangePointMap, variableChangePointMapInv,
        variableChangePointX_invX, variableChangePointY_invY]

noncomputable def variableChangePointEquiv
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point W ≃ WeierstrassCurve.Affine.Point (C • W) where
  toFun := variableChangePointMap W C
  invFun := variableChangePointMapInv W C
  left_inv := variableChangePointMap_leftInverse W C
  right_inv := variableChangePointMap_rightInverse W C

lemma variableChangePointMap_add
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point W) :
    variableChangePointMap W C (P + Q) =
      variableChangePointMap W C P + variableChangePointMap W C Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂
      · have htarget := variableChange_vertical W C hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq htarget.left htarget.right]
      · have htarget := variableChange_nonvertical W C hxy
        have hslope := variableChange_slope W C h₁.left h₂.left hxy
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_some htarget]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · change
            variableChangePointX C
                (WeierstrassCurve.Affine.addX W x₁ x₂
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) =
              WeierstrassCurve.Affine.addX (C • W)
                (variableChangePointX C x₁) (variableChangePointX C x₂)
                (WeierstrassCurve.Affine.slope (C • W)
                  (variableChangePointX C x₁) (variableChangePointX C x₂)
                  (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂))
          rw [hslope]
          exact variableChange_addX W C x₁ x₂
            (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)
        · change
            variableChangePointY C
                (WeierstrassCurve.Affine.addX W x₁ x₂
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂))
                (WeierstrassCurve.Affine.addY W x₁ x₂ y₁
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) =
              WeierstrassCurve.Affine.addY (C • W)
                (variableChangePointX C x₁) (variableChangePointX C x₂)
                (variableChangePointY C x₁ y₁)
                (WeierstrassCurve.Affine.slope (C • W)
                  (variableChangePointX C x₁) (variableChangePointX C x₂)
                  (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂))
          rw [hslope]
          exact variableChange_addY W C x₁ x₂ y₁
            (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)

noncomputable def variableChangePointAddEquiv
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point (C • W) :=
  AddEquiv.mk (variableChangePointEquiv W C) (variableChangePointMap_add W C)

noncomputable def pointCurveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

end

end Scratch.TateZ2xZ10Reduction


