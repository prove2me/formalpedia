-- Prove2me | Definitions.Def_RPLib_S2_TateNFA
-- name    : RPLib_S2_TateNFA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:45:45.781549+00:00
-- url     : https://prove2.me/theorems/0b115d60-fa53-435b-b8d5-2e2eebf073b5
-- title:
--   Tate normal form $E(b,c)$ of an elliptic curve with a point of order at least 4
-- statement:
--   The curves $E(b,c): y^2 + (1-c)xy - by = x^3 - bx^2$, their discriminant, and the existence and uniqueness of the change of variables bringing a pair $(E, P)$, $P$ of order at least 4, to Tate normal form with $P = (0,0)$; such pairs have no nontrivial automorphisms.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Husemoller, Elliptic Curves, 2nd ed., GTM 111, Springer 2004, Section 4.4, doi:10.1007/b97292

import Mathlib

/-!
# Tate normal form `E(b,c)` and the moduli bijection for `Y₁(M)`, `M ≥ 4` (part A)

Library unit S2-TateNF of the Ramanujan-Petersson project (Mathlib-only imports).
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.TateNF

/-! ## The Tate normal form over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- Tate normal form `E(b,c) : y² + (1 - c)xy - by = x³ - bx²`. -/
def tate (b c : R) : WeierstrassCurve R := ⟨1 - c, -b, -b, 0, 0⟩

@[simp] lemma tate_a₁ (b c : R) : (tate b c).a₁ = 1 - c := rfl
@[simp] lemma tate_a₂ (b c : R) : (tate b c).a₂ = -b := rfl
@[simp] lemma tate_a₃ (b c : R) : (tate b c).a₃ = -b := rfl
@[simp] lemma tate_a₄ (b c : R) : (tate b c).a₄ = 0 := rfl
@[simp] lemma tate_a₆ (b c : R) : (tate b c).a₆ = 0 := rfl

/-- The discriminant of `E(b,c)`. -/
def tateDisc (b c : R) : R :=
  b ^ 3 * (16 * b ^ 2 - 8 * b * c ^ 2 - 20 * b * c + b + c * (c - 1) ^ 3)

theorem tate_Δ (b c : R) : (tate b c).Δ = tateDisc b c := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, tate_a₁, tate_a₂, tate_a₃, tate_a₄, tate_a₆, tateDisc]
  ring

lemma tate_equation_zero (b c : R) : (tate b c).toAffine.Equation 0 0 := by
  rw [equation_zero]; rfl

lemma tate_nonsingular_zero_iff (b c : R) : (tate b c).toAffine.Nonsingular 0 0 ↔ b ≠ 0 := by
  rw [nonsingular_zero]; simp [tate]

lemma ne_zero_of_tateDisc_ne_zero {b c : R} (h : tateDisc b c ≠ 0) : b ≠ 0 := by
  rintro rfl; simp [tateDisc] at h

end Ring

/-! ## Points under a change of variables -/

section VC

variable {F : Type*} [Field F]

/-- `u⁻¹` of a change of variables, as an element of `F`. -/
def ui (C : VariableChange F) : F := ((C.u⁻¹ : Fˣ) : F)

lemma ui_ne_zero (C : VariableChange F) : ui C ≠ 0 := Units.ne_zero _

lemma ui_eq_inv (C : VariableChange F) : ui C = (C.u : F)⁻¹ := Units.val_inv_eq_inv_val _

lemma ui_mul (C C' : VariableChange F) : ui (C * C') = ui C * ui C' := by
  simp only [ui, VariableChange.mul_def, mul_inv, Units.val_mul]

lemma ui_one : ui (1 : VariableChange F) = 1 := by simp [ui, VariableChange.one_def]

@[simp] lemma one_r : (1 : VariableChange F).r = 0 := rfl
@[simp] lemma one_s : (1 : VariableChange F).s = 0 := rfl
@[simp] lemma one_t : (1 : VariableChange F).t = 0 := rfl

/-- New `x`-coordinate of a point under `C`: `x' = u⁻²(x - r)`. -/
def vcX (C : VariableChange F) (x : F) : F := ui C ^ 2 * (x - C.r)

/-- New `y`-coordinate of a point under `C`: `y' = u⁻³(y - s(x - r) - t)`. -/
def vcY (C : VariableChange F) (x y : F) : F := ui C ^ 3 * (y - C.s * (x - C.r) - C.t)

variable (W : WeierstrassCurve F)

lemma vc_a₁ (C : VariableChange F) : (C • W).a₁ = ui C * (W.a₁ + 2 * C.s) := rfl
lemma vc_a₂ (C : VariableChange F) :
    (C • W).a₂ = ui C ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := rfl
lemma vc_a₃ (C : VariableChange F) : (C • W).a₃ = ui C ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) := rfl
lemma vc_a₄ (C : VariableChange F) : (C • W).a₄ = ui C ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ -
    (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t) := rfl
lemma vc_a₆ (C : VariableChange F) : (C • W).a₆ = ui C ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ +
    C.r ^ 3 - C.t * W.a₃ - C.t ^ 2 - C.r * C.t * W.a₁) := rfl

lemma vcX_eq_iff (C : VariableChange F) {x₁ x₂ : F} : vcX C x₁ = vcX C x₂ ↔ x₁ = x₂ := by
  constructor
  · intro h
    have h' : ui C ^ 2 * (x₁ - x₂) = 0 := by simp only [vcX] at h; linear_combination h
    have := (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 (ui_ne_zero C))
    exact sub_eq_zero.mp this
  · rintro rfl; rfl

lemma vcY_sub_negY (C : VariableChange F) (x₁ x₂ y₁ y₂ : F) :
    vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂) =
      ui C ^ 3 * (y₁ - W.toAffine.negY x₂ y₂ + C.s * (x₂ - x₁)) := by
  simp only [negY, vcX, vcY, vc_a₁, vc_a₃]; ring

lemma equation_vc (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Equation (vcX C x) (vcY C x y) ↔ W.toAffine.Equation x y := by
  have key : vcY C x y ^ 2 + (C • W).a₁ * vcX C x * vcY C x y + (C • W).a₃ * vcY C x y -
      (vcX C x ^ 3 + (C • W).a₂ * vcX C x ^ 2 + (C • W).a₄ * vcX C x + (C • W).a₆) =
      ui C ^ 6 * (y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
    simp only [vc_a₁, vc_a₂, vc_a₃, vc_a₄, vc_a₆, vcX, vcY]; ring
  rw [equation_iff', equation_iff']
  constructor
  · intro h
    exact (mul_eq_zero.mp (key.symm.trans h)).resolve_left (pow_ne_zero 6 (ui_ne_zero C))
  · intro h
    exact key.trans (by rw [h, mul_zero])

lemma nonsingular_vc (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Nonsingular (vcX C x) (vcY C x y) ↔ W.toAffine.Nonsingular x y := by
  have hA : (C • W).a₁ * vcY C x y - (3 * vcX C x ^ 2 + 2 * (C • W).a₂ * vcX C x + (C • W).a₄) =
      ui C ^ 4 * ((W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) +
        C.s * (2 * y + W.a₁ * x + W.a₃)) := by
    simp only [vc_a₁, vc_a₂, vc_a₄, vcX, vcY]; ring
  have hB : 2 * vcY C x y + (C • W).a₁ * vcX C x + (C • W).a₃ =
      ui C ^ 3 * (2 * y + W.a₁ * x + W.a₃) := by
    simp only [vc_a₁, vc_a₃, vcX, vcY]; ring
  have hu := ui_ne_zero C
  rw [nonsingular_iff', nonsingular_iff', equation_vc]
  refine and_congr_right fun _ => ?_
  rw [← not_iff_not, not_or, not_or, not_not, not_not, not_not, not_not]
  change ((C • W).a₁ * vcY C x y - (3 * vcX C x ^ 2 + 2 * (C • W).a₂ * vcX C x + (C • W).a₄) = 0 ∧
      2 * vcY C x y + (C • W).a₁ * vcX C x + (C • W).a₃ = 0) ↔ _
  rw [hA, hB]
  constructor
  · rintro ⟨h1, h2⟩
    have hb := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 3 hu)
    refine ⟨?_, hb⟩
    have := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 4 hu)
    rw [hb, mul_zero, add_zero] at this
    exact this
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; simp

/-- The map on points induced by a change of variables `C` with `C • W = W'`:
`(x, y) ↦ (u⁻²(x - r), u⁻³(y - s(x - r) - t))`. -/
def ptMap (C : VariableChange F) {W W' : WeierstrassCurve F} (h : C • W = W') :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y hxy => .some (vcX C x) (vcY C x y) (h ▸ (nonsingular_vc W C x y).mpr hxy)

variable {W}

@[simp] lemma ptMap_zero (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W') :
    ptMap C h 0 = 0 := rfl

lemma ptMap_some (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W') {x y : F}
    (hxy : W.toAffine.Nonsingular x y) :
    ptMap C h (.some x y hxy) = .some (vcX C x) (vcY C x y) (h ▸ (nonsingular_vc W C x y).mpr hxy) :=
  rfl

lemma ptMap_neg (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W')
    (P : W.toAffine.Point) : ptMap C h (-P) = -ptMap C h P := by
  subst h
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · simp only [Point.neg_some, ptMap_some, Point.some.injEq, true_and]
    simp only [negY, vcX, vcY, vc_a₁, vc_a₃]; ring

lemma ptMap_congr {C₁ C₂ : VariableChange F} (hC : C₁ = C₂) {W' : WeierstrassCurve F}
    (h₁ : C₁ • W = W') (h₂ : C₂ • W = W') (P : W.toAffine.Point) :
    ptMap C₁ h₁ P = ptMap C₂ h₂ P := by
  subst hC; rfl

lemma ptMap_one (h : (1 : VariableChange F) • W = W) (P : W.toAffine.Point) :
    ptMap 1 h P = P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · simp only [ptMap_some, Point.some.injEq]
    simp only [vcX, vcY, ui_one, one_r, one_s, one_t]; constructor <;> ring

lemma ptMap_mul (C C' : VariableChange F) {W₁ W₂ : WeierstrassCurve F} (h' : C' • W = W₁)
    (h : C • W₁ = W₂) (h'' : (C * C') • W = W₂) (P : W.toAffine.Point) :
    ptMap (C * C') h'' P = ptMap C h (ptMap C' h' P) := by
  subst h' h
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · simp only [ptMap_some, Point.some.injEq]
    have hu' : (C'.u : F) ≠ 0 := Units.ne_zero _
    simp only [vcX, vcY, VariableChange.mul_def, Units.val_mul, ui_eq_inv]
    constructor
    · field_simp; ring
    · field_simp; ring

lemma ptMap_inv_ptMap (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W')
    (h' : C⁻¹ • W' = W) (P : W.toAffine.Point) : ptMap C⁻¹ h' (ptMap C h P) = P := by
  have h'' : (C⁻¹ * C) • W = W := by rw [mul_smul, h, h']
  rw [← ptMap_mul C⁻¹ C h h' h'', ptMap_congr (inv_mul_cancel C) h'' (one_smul _ W), ptMap_one]

lemma inv_smul_eq (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W') :
    C⁻¹ • W' = W := by
  rw [← h, inv_smul_smul]

lemma ptMap_injective (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W') :
    Function.Injective (ptMap C h) :=
  Function.LeftInverse.injective (ptMap_inv_ptMap C h (inv_smul_eq C h))

variable [DecidableEq F]

variable (W) in
lemma slope_vc (C : VariableChange F) {x₁ x₂ y₁ y₂ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      ui C * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  have hu := ui_ne_zero C
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hy12 : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hy12
    have e2 := vcY_sub_negY W C x₁ x₁ y₁ y₁
    have hD : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hy' : vcY C x₁ y₁ ≠ (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) := by
      intro h
      apply hD
      have : ui C ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) = 0 := by linear_combination h - e2
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hu)
    have e1 : 3 * vcX C x₁ ^ 2 + 2 * (C • W).a₂ * vcX C x₁ + (C • W).a₄ - (C • W).a₁ * vcY C x₁ y₁ =
        ui C ^ 4 * ((3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) -
          C.s * (y₁ - W.toAffine.negY x₁ y₁)) := by
      simp only [negY, vc_a₁, vc_a₂, vc_a₄, vcX, vcY]; ring
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy]
    change (3 * vcX C x₁ ^ 2 + 2 * (C • W).a₂ * vcX C x₁ + (C • W).a₄ - (C • W).a₁ * vcY C x₁ y₁) /
      (vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁)) = _
    rw [e1, show vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) =
      ui C ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) by rw [e2]; ring]
    field_simp
  · have hx' : vcX C x₁ ≠ vcX C x₂ := fun h => hx ((vcX_eq_iff C).mp h)
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have e3 : vcX C x₁ - vcX C x₂ = ui C ^ 2 * (x₁ - x₂) := by simp only [vcX]; ring
    have e4 : vcY C x₁ y₁ - vcY C x₂ y₂ = ui C ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
      simp only [vcY]; ring
    rw [slope_of_X_ne hx', slope_of_X_ne hx, e3, e4]
    field_simp

omit [DecidableEq F] in
lemma cond_vc (C : VariableChange F) (x₁ x₂ y₁ y₂ : F) :
    (vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂)) ↔
      (x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by
  rw [vcX_eq_iff]
  have hu := ui_ne_zero C
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    have e := vcY_sub_negY W C x₁ x₁ y₁ y₂
    have : ui C ^ 3 * (y₁ - W.toAffine.negY x₁ y₂) = 0 := by linear_combination h - e
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hu))
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    have e := vcY_sub_negY W C x₁ x₁ y₁ y₂
    linear_combination e + ui C ^ 3 * h

theorem ptMap_add (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W')
    (P Q : W.toAffine.Point) : ptMap C h (P + Q) = ptMap C h P + ptMap C h Q := by
  subst h
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, ptMap_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, ptMap_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · have hxy' := (cond_vc C x₁ x₂ y₁ y₂).mpr hxy
    rw [Point.add_of_Y_eq hxy.1 hxy.2, ptMap_some, ptMap_some, Point.add_of_Y_eq hxy'.1 hxy'.2]
    rfl
  · have hxy' : ¬(vcX C x₁ = vcX C x₂ ∧
        vcY C x₁ y₁ = (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂)) :=
      fun h => hxy ((cond_vc C x₁ x₂ y₁ y₂).mp h)
    rw [Point.add_some hxy, ptMap_some, ptMap_some, ptMap_some, Point.add_some hxy', Point.some.injEq]
    have hs := slope_vc W C h₁.1 h₂.1 hxy
    constructor
    · rw [hs]; simp only [addX, vcX, vc_a₁, vc_a₂]; ring
    · rw [hs]; simp only [addY, negAddY, addX, negY, vcX, vcY, vc_a₁, vc_a₂, vc_a₃]; ring

/-- The point map of `C` as an additive group homomorphism. -/
def ptHom (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W') :
    W.toAffine.Point →+ W'.toAffine.Point where
  toFun := ptMap C h
  map_zero' := rfl
  map_add' := ptMap_add C h

@[simp] lemma ptHom_apply (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W')
    (P : W.toAffine.Point) : ptHom C h P = ptMap C h P := rfl

lemma ptMap_nsmul (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W') (n : ℕ)
    (P : W.toAffine.Point) : ptMap C h (n • P) = n • ptMap C h P :=
  map_nsmul (ptHom C h) n P

theorem addOrderOf_ptMap (C : VariableChange F) {W' : WeierstrassCurve F} (h : C • W = W')
    (P : W.toAffine.Point) : addOrderOf (ptMap C h P) = addOrderOf P :=
  addOrderOf_injective (ptHom C h) (ptMap_injective C h) P

end VC

/-! ## The point `(0,0)`, rigidity and the normal form -/

section Tate

variable {F : Type*} [Field F] [DecidableEq F]

/-- The point `P = (0,0)` of `E(b,c)` (the zero point when `b = 0`, where `(0,0)` is singular). -/
def tatePt (b c : F) : (tate b c).toAffine.Point :=
  if hb : b = 0 then 0 else .some 0 0 ((tate_nonsingular_zero_iff b c).mpr hb)

lemma tatePt_of_ne {b c : F} (hb : b ≠ 0) :
    tatePt b c = .some 0 0 ((tate_nonsingular_zero_iff b c).mpr hb) := dif_neg hb

/-- `C` is an isomorphism of pointed curves `(W, P) ≅ (W', P')`: `C • W = W'` and `C` maps `P`
to `P'`. -/
def IsPtIso (C : VariableChange F) {W W' : WeierstrassCurve F} (P : W.toAffine.Point)
    (P' : W'.toAffine.Point) : Prop :=
  ∃ h : C • W = W', ptMap C h P = P'

omit [DecidableEq F] in
lemma ptMap_ne_zero (C : VariableChange F) {W W' : WeierstrassCurve F} (h : C • W = W')
    {Q : W.toAffine.Point} (hQ : Q ≠ 0) : ptMap C h Q ≠ 0 :=
  fun hz => hQ (ptMap_injective C h (hz.trans (ptMap_zero C h).symm))

/-- Rigidity of the Tate normal form: a change of variables taking `(E(b,c), (0,0))` to
`(E(b',c'), (0,0))` is the identity, and `(b,c) = (b',c')`. -/
theorem tate_rigid {b c b' c' : F} (hb : b ≠ 0) (C : VariableChange F)
    (hC : IsPtIso C (tatePt b c) (tatePt b' c')) : C = 1 ∧ b = b' ∧ c = c' := by
  obtain ⟨h, hP⟩ := hC
  have hb' : b' ≠ 0 := by
    rintro rfl
    rw [tatePt_of_ne hb, ptMap_some] at hP
    simp [tatePt] at hP
  rw [tatePt_of_ne hb, ptMap_some, tatePt_of_ne hb', Point.some.injEq] at hP
  obtain ⟨hr, ht⟩ := hP
  have hu := ui_ne_zero C
  have hr0 : C.r = 0 := by
    simp only [vcX] at hr
    have := (mul_eq_zero.mp hr).resolve_left (pow_ne_zero 2 hu)
    linear_combination -this
  have ht0 : C.t = 0 := by
    simp only [vcY, hr0] at ht
    have := (mul_eq_zero.mp ht).resolve_left (pow_ne_zero 3 hu)
    linear_combination -this
  have e1 := congrArg WeierstrassCurve.a₁ h
  have e2 := congrArg WeierstrassCurve.a₂ h
  have e3 := congrArg WeierstrassCurve.a₃ h
  have e4 := congrArg WeierstrassCurve.a₄ h
  simp only [vc_a₁, vc_a₂, vc_a₃, vc_a₄, tate_a₁, tate_a₂, tate_a₃, tate_a₄, hr0, ht0] at e1 e2 e3 e4
  have hs0 : C.s = 0 := by
    have : ui C ^ 4 * (C.s * b) = 0 := by linear_combination e4
    exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (pow_ne_zero 4 hu))).resolve_right hb
  have hui : ui C = 1 := by
    have : ui C ^ 2 * b * (ui C - 1) = 0 := by rw [hs0] at e2; linear_combination e2 - e3
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero (pow_ne_zero 2 hu) hb)
    linear_combination this
  have hu1 : C.u = 1 := by
    have : C.u⁻¹ = 1 := Units.val_eq_one.mp hui
    exact inv_eq_one.mp this
  refine ⟨?_, ?_, ?_⟩
  · rcases C with ⟨u, r, s, t⟩
    simp only at hr0 hs0 ht0 hu1
    subst hr0 hs0 ht0 hu1
    rfl
  · rw [hs0, hui] at e2; linear_combination -e2
  · rw [hs0, hui] at e1; linear_combination -e1

/-- The translation-shear moving `(x₀, y₀)` to `(0,0)` with horizontal tangent. -/
def transVC (W : WeierstrassCurve F) (x₀ y₀ : F) : VariableChange F :=
  ⟨1, x₀, (W.a₄ + 2 * x₀ * W.a₂ - y₀ * W.a₁ + 3 * x₀ ^ 2) / (W.a₃ + x₀ * W.a₁ + 2 * y₀), y₀⟩

/-- Scaling by a unit. -/
def scaleVC (u : Fˣ) : VariableChange F := ⟨u, 0, 0, 0⟩

omit [DecidableEq F] in
lemma ui_transVC (W : WeierstrassCurve F) (x₀ y₀ : F) : ui (transVC W x₀ y₀) = 1 := by
  simp [ui, transVC]

lemma a₂_ne_zero_of_three_nsmul {W : WeierstrassCurve F} (h : W.toAffine.Nonsingular 0 0)
    (h4 : W.a₄ = 0) (h3 : W.a₃ ≠ 0)
    (h3P : 3 • (Point.some 0 0 h : W.toAffine.Point) ≠ 0) : W.a₂ ≠ 0 := by
  intro ha2
  have hy : (0 : F) ≠ W.toAffine.negY 0 0 := by
    simp only [negY, neg_zero, mul_zero, zero_sub]
    exact fun h' => h3 (neg_eq_zero.mp h'.symm)
  have hns := nonsingular_add h h fun hxy => hy hxy.2
  have h2 : (Point.some 0 0 h : W.toAffine.Point) + Point.some 0 0 h = Point.some _ _ hns :=
    Point.add_self_of_Y_ne hy
  have hx : W.toAffine.addX 0 0 (W.toAffine.slope 0 0 0 0) = 0 := by
    rw [slope_of_Y_ne rfl hy]
    simp [addX, h4, ha2]
  have h3eq : (3 : ℕ) • (Point.some 0 0 h : W.toAffine.Point) =
      Point.some 0 0 h + Point.some 0 0 h + Point.some 0 0 h := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
  rcases (Point.X_eq_iff (h₁ := hns) (h₂ := h)).mp hx with h' | h'
  · rw [← h2] at h'
    have : (Point.some 0 0 h : W.toAffine.Point) = 0 := by
      have := congrArg (· - (Point.some 0 0 h : W.toAffine.Point)) h'
      simpa using this
    exact Point.some_ne_zero h this
  · rw [← h2] at h'
    apply h3P
    rw [h3eq, h', neg_add_cancel]

omit [DecidableEq F] in
lemma scale_tate {W : WeierstrassCurve F} (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (h3 : W.a₃ ≠ 0)
    (h2 : W.a₂ ≠ 0) :
    scaleVC (Units.mk0 (W.a₃ / W.a₂) (div_ne_zero h3 h2)) • W =
      tate (-(W.a₂ ^ 3 / W.a₃ ^ 2)) (1 - W.a₁ * W.a₂ / W.a₃) := by
  have hui : ui (scaleVC (Units.mk0 (W.a₃ / W.a₂) (div_ne_zero h3 h2))) = W.a₂ / W.a₃ := by
    simp [ui, scaleVC]
  ext <;> simp only [vc_a₁, vc_a₂, vc_a₃, vc_a₄, vc_a₆, hui, tate_a₁, tate_a₂, tate_a₃, tate_a₄,
    tate_a₆, h4, h6] <;> simp [scaleVC] <;> field_simp

/-- Existence of the Tate normal form: if `P`, `2P`, `3P` are nonzero then some change of variables
takes `(W, P)` to `(E(b,c), (0,0))` with `b ≠ 0`. -/
theorem exists_normalForm (W : WeierstrassCurve F) (P : W.toAffine.Point) (h1 : P ≠ 0)
    (h2 : 2 • P ≠ 0) (h3 : 3 • P ≠ 0) :
    ∃ (b c : F) (C : VariableChange F), b ≠ 0 ∧ IsPtIso C P (tatePt b c) := by
  rcases P with _ | ⟨x₀, y₀, h₀⟩
  · exact absurd rfl h1
  have hD : W.a₃ + x₀ * W.a₁ + 2 * y₀ ≠ 0 := by
    intro hD
    apply h2
    rw [two_nsmul]
    apply Point.add_self_of_Y_eq
    simp only [negY]
    linear_combination hD
  set C₁ := transVC W x₀ y₀ with hC₁
  have hu1 := ui_transVC W x₀ y₀
  have hx0 : vcX C₁ x₀ = 0 := by simp [vcX, C₁, transVC]
  have hy0 : vcY C₁ x₀ y₀ = 0 := by simp [vcY, C₁, transVC]
  have hW1a3 : (C₁ • W).a₃ = W.a₃ + x₀ * W.a₁ + 2 * y₀ := by
    rw [vc_a₃, hu1]; simp [C₁, transVC]
  have hW1a4 : (C₁ • W).a₄ = 0 := by
    rw [vc_a₄, hu1]; simp only [C₁, transVC]; field_simp; ring
  have hW1a6 : (C₁ • W).a₆ = 0 := by
    rw [vc_a₆, hu1]
    have := (equation_iff' x₀ y₀).mp h₀.1
    simp only [C₁, transVC]
    linear_combination -this
  have hns1 : (C₁ • W).toAffine.Nonsingular 0 0 := by
    have := (nonsingular_vc W C₁ x₀ y₀).mpr h₀
    rwa [hx0, hy0] at this
  have hP1 : ptMap C₁ rfl (Point.some x₀ y₀ h₀) = Point.some 0 0 hns1 := by
    rw [ptMap_some, Point.some.injEq]; exact ⟨hx0, hy0⟩
  have h3P1 : 3 • (Point.some 0 0 hns1 : (C₁ • W).toAffine.Point) ≠ 0 := by
    rw [← hP1, ← ptMap_nsmul]; exact ptMap_ne_zero C₁ rfl h3
  have ha3 : (C₁ • W).a₃ ≠ 0 := by rw [hW1a3]; exact hD
  have ha2 := a₂_ne_zero_of_three_nsmul hns1 hW1a4 ha3 h3P1
  have hscale := scale_tate hW1a4 hW1a6 ha3 ha2
  set C₂ := scaleVC (Units.mk0 ((C₁ • W).a₃ / (C₁ • W).a₂) (div_ne_zero ha3 ha2))
  have hb : -((C₁ • W).a₂ ^ 3 / (C₁ • W).a₃ ^ 2) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 3 ha2) (pow_ne_zero 2 ha3))
  refine ⟨_, _, C₂ * C₁, hb, by rw [mul_smul, hscale], ?_⟩
  rw [ptMap_mul C₂ C₁ rfl hscale, hP1, ptMap_some, tatePt_of_ne hb, Point.some.injEq]
  simp [vcX, vcY, C₂, scaleVC]

/-- Uniqueness of the normal form: the change of variables and `(b,c)` are unique. -/
theorem normalForm_unique {W : WeierstrassCurve F} {P : W.toAffine.Point} {b c b' c' : F}
    {C C' : VariableChange F} (hb : b ≠ 0) (hC : IsPtIso C P (tatePt b c))
    (hC' : IsPtIso C' P (tatePt b' c')) : C = C' ∧ b = b' ∧ c = c' := by
  obtain ⟨h, hP⟩ := hC
  obtain ⟨h', hP'⟩ := hC'
  have hinv := inv_smul_eq C h
  have hD : IsPtIso (C' * C⁻¹) (tatePt b c) (tatePt b' c') := by
    refine ⟨by rw [mul_smul, hinv, h'], ?_⟩
    rw [ptMap_mul C' C⁻¹ hinv h', ← hP, ptMap_inv_ptMap, hP']
  obtain ⟨h1, hbb, hcc⟩ := tate_rigid hb _ hD
  exact ⟨(mul_inv_eq_one.mp h1).symm, hbb, hcc⟩

/-- Existence and uniqueness of the Tate normal form of `(W, P)` with `P, 2P, 3P ≠ 0`. -/
theorem existsUnique_normalForm (W : WeierstrassCurve F) (P : W.toAffine.Point) (h1 : P ≠ 0)
    (h2 : 2 • P ≠ 0) (h3 : 3 • P ≠ 0) :
    ∃! bcC : F × F × VariableChange F, IsPtIso bcC.2.2 P (tatePt bcC.1 bcC.2.1) := by
  obtain ⟨b, c, C, hb, hC⟩ := exists_normalForm W P h1 h2 h3
  refine ⟨(b, c, C), hC, ?_⟩
  rintro ⟨b', c', C'⟩ hC'
  obtain ⟨h1, h2, h3⟩ := normalForm_unique hb hC hC'
  subst h1 h2 h3; rfl

/-- Pointed curves `(W, P)` with `P, 2P, 3P ≠ 0` have no nontrivial automorphisms. -/
theorem aut_trivial {W : WeierstrassCurve F} {P : W.toAffine.Point} (h1 : P ≠ 0)
    (h2 : 2 • P ≠ 0) (h3 : 3 • P ≠ 0) {C : VariableChange F} (hC : IsPtIso C P P) : C = 1 := by
  obtain ⟨b, c, C₀, hb, h₀, hP₀⟩ := exists_normalForm W P h1 h2 h3
  obtain ⟨h, hP⟩ := hC
  have : IsPtIso (C₀ * C) P (tatePt b c) :=
    ⟨by rw [mul_smul, h, h₀], by rw [ptMap_mul C₀ C h h₀, hP, hP₀]⟩
  exact mul_eq_left.mp (normalForm_unique hb this ⟨h₀, hP₀⟩).1

end Tate

end RPLib.TateNF


