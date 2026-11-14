-- Prove2me | Definitions.Def_RPLib_S2_Torsion
-- name    : RPLib_S2_Torsion
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:51:40.019+00:00
-- url     : https://prove2.me/theorems/d01926f8-6f89-4f11-8aa9-83d33332cc62
-- title:
--   Prime-to-$p$ torsion of an elliptic curve: $E[n] \cong (\mathbb{Z}/n)^2$
-- statement:
--   For a Weierstrass curve over a field and $n$ invertible in the field: the multiplication formula $x(nP) = \Phi_n(x)/\Psi_n^2(x)$ via division polynomials, $nP = 0 \iff \Psi_n^2(x(P)) = 0$, and over a separably closed field $\#E[n] = n^2$, $E[n] \cong \mathbb{Z}/n \times \mathbb{Z}/n$, with separable torsion coordinates.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Corollary III.6.4 and Exercise 3.7

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Prime-to-`p` torsion of an elliptic curve (unit S2-Torsion)

For a Weierstrass curve `W` over a field and `n ≠ 0` in the field:
* `kummer`, `mult_formula`, `kumId`, `local_formula`: the x-only addition law and the multiplication
  formula `x(n • P) = Φₙ(x) / ΨSqₙ(x)` (proved here; Mathlib only defines the division polynomials);
* `nsmul_eq_zero_iff`: `n • (x, y) = 0 ↔ ΨSqₙ(x) = 0`;
* `card_tors` (O5): over a separably closed field, `Nat.card (tors W n) = n ^ 2`;
* `tors_equiv` (O6): over a separably closed field, `tors W n ≃+ ZMod n × ZMod n`;
* `card_tors_baseChange`, `tors_equiv_baseChange`, `card_tors_sepClosure`, `tors_equiv_sepClosure`:
  the same over any separably closed extension `L / K`, in particular `K^sep = SeparableClosure K`;
* `tors_coords_separable`, `tors_coords_separable_algClosure`, `tors_map_bijective` (O7): every
  `n`-torsion point over a separably closed `L ⊇ K` has coordinates separable over `K`; the base change
  map `E(K^sep)[n] → E(L)[n]` is bijective.

Separability argument (O5): generic fibre / Wronskian. `Φₙ - t ΨSqₙ` is monic of degree `n²` and
separable for all `t` outside a finite set (roots of the Wronskian `Φₙ'ΨSqₙ - ΦₙΨSqₙ'`, whose
`X^(2n²-2)` coefficient is `n² ≠ 0`, and the 2-torsion abscissae), so the fibre of `[n]` over `±R₀`
has `2n²` points and is two cosets of `E[n]`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.Torsion

/-! ## Part A: the x-only (Kummer) addition law -/

section Kummer

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

/-- Projective `x`-coordinate `(X, Z)` of a point: `O ↦ (1, 0)`, `(x, y) ↦ (x, 1)`. -/
def xP : W.toAffine.Point → F × F
  | .zero => (1, 0)
  | .some x _ _ => (x, 1)

@[simp] lemma xP_zero : xP (0 : W.toAffine.Point) = (1, 0) := rfl

@[simp] lemma xP_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    xP (Point.some x y h) = (x, 1) := rfl

@[simp] lemma xP_neg (P : W.toAffine.Point) : xP (-P) = xP P := by
  cases P <;> rfl

lemma xP_ne_zero (P : W.toAffine.Point) : xP P ≠ 0 := by
  cases P <;> simp [xP, Prod.ext_iff]

lemma xP_snd_eq_zero_iff (P : W.toAffine.Point) : (xP P).2 = 0 ↔ P = 0 := by
  cases P
  · simp [xP, Point.zero_def]
  · simp [xP, Point.zero_def]

/-- Symmetric product of two binary linear forms: coefficients `(ZZ, XZ, XX)`. -/
def sym (p q : F × F) : F × F × F := (p.2 * q.2, p.1 * q.2 + q.1 * p.2, p.1 * q.1)

lemma sym_comm (p q : F × F) : sym p q = sym q p := by
  simp only [sym, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

lemma sym_smul_right (p q : F × F) (c : F) : sym p (c • q) = c • sym p q := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [sym, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

/-- Cancellation: `sym p r = μ • sym q r` with `r ≠ 0` forces `p = μ • q`. -/
lemma sym_cancel {p q r : F × F} {μ : F} (hr : r ≠ 0) (h : sym p r = μ • sym q r) :
    p = μ • q := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r
  simp only [sym, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hr2 : r2 = 0
  · subst hr2
    have hr1 : r1 ≠ 0 := by rintro rfl; exact hr rfl
    refine ⟨mul_right_cancel₀ hr1 (by linear_combination h3), mul_left_cancel₀ hr1 ?_⟩
    linear_combination h2
  · have e2 : p2 = μ * q2 := mul_right_cancel₀ hr2 (by linear_combination h1)
    refine ⟨mul_right_cancel₀ hr2 ?_, e2⟩
    linear_combination h2 - r1 * e2

/-- Affine Kummer sum form `S(a, b)`. -/
def S1 (W : WeierstrassCurve F) (a b : F) : F :=
  2 * a * b * (a + b) + W.b₂ * a * b + W.b₄ * (a + b) + W.b₆

/-- Affine Kummer product form `Q(a, b)`. -/
def Q1 (W : WeierstrassCurve F) (a b : F) : F :=
  a ^ 2 * b ^ 2 - W.b₄ * a * b - W.b₆ * (a + b) - W.b₈

/-- The Kummer biquadratic forms `(B_ZZ, B_XZ, B_XX)`. -/
def kB (W : WeierstrassCurve F) (p q : F × F) : F × F × F :=
  ((p.1 * q.2 - q.1 * p.2) ^ 2,
    2 * p.1 * q.1 * (p.1 * q.2 + q.1 * p.2) + W.b₂ * p.1 * q.1 * p.2 * q.2 +
      W.b₄ * (p.1 * q.2 + q.1 * p.2) * p.2 * q.2 + W.b₆ * p.2 ^ 2 * q.2 ^ 2,
    p.1 ^ 2 * q.1 ^ 2 - W.b₄ * p.1 * q.1 * p.2 * q.2 - W.b₆ * (p.1 * q.2 + q.1 * p.2) * p.2 * q.2 -
      W.b₈ * p.2 ^ 2 * q.2 ^ 2)

lemma kB_comm (p q : F × F) : kB W p q = kB W q p := by
  simp only [kB, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

lemma kB_smul_left (p q : F × F) (c : F) : kB W (c • p) q = c ^ 2 • kB W p q := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [kB, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

lemma kB_affine (a b : F) : kB W (a, 1) (b, 1) = ((a - b) ^ 2, S1 W a b, Q1 W a b) := by
  simp only [kB, S1, Q1, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

/-- `ψ₂` of an affine point: `2y + a₁x + a₃`. -/
def yψ (W : WeierstrassCurve F) (x y : F) : F := 2 * y + W.a₁ * x + W.a₃

/-- `Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆`. -/
def fx (W : WeierstrassCurve F) (x : F) : F := 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

lemma eqn {x y : F} (h : W.toAffine.Equation x y) :
    y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
  (equation_iff x y).mp h

lemma yψ_sq {x y : F} (h : W.toAffine.Equation x y) : yψ W x y ^ 2 = fx W x := by
  have e := eqn h
  simp only [yψ, fx, b₂, b₄, b₆]
  linear_combination 4 * e

lemma S1_self (a : F) : S1 W a a = fx W a := by simp only [S1, fx]; ring

lemma yψ_eq_zero_iff {x y : F} : yψ W x y = 0 ↔ y = W.toAffine.negY x y := by
  simp only [yψ, negY]; constructor <;> intro h <;> linear_combination h

/-- Doubling at a non-2-torsion affine point. -/
lemma double_some {x y : F} (h : W.toAffine.Nonsingular x y) (hy : yψ W x y ≠ 0) :
    ∃ (x₃ y₃ : F) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      Point.some x y h + Point.some x y h = Point.some x₃ y₃ h₃ ∧ x₃ * yψ W x y ^ 2 = Q1 W x x := by
  have hy' : y ≠ W.toAffine.negY x y := fun e => hy (yψ_eq_zero_iff.mpr e)
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy', ?_⟩
  have e := eqn h.1
  rw [addX, slope_of_Y_ne rfl hy']
  have hd : y - W.toAffine.negY x y = yψ W x y := by simp only [yψ, negY]; ring
  rw [hd]
  field_simp
  simp only [yψ, Q1, b₂, b₄, b₆, b₈]
  linear_combination (-8 * x - W.a₁ ^ 2 - 4 * W.a₂) * e

/-- At a 2-torsion point `Φ₂(x) = Q(x, x) ≠ 0` (nonsingularity). -/
lemma Q1_self_ne_zero_of_two_torsion {x y : F} (h : W.toAffine.Nonsingular x y)
    (hy : yψ W x y = 0) : Q1 W x x ≠ 0 := by
  have e := eqn h.1
  have hD : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 := by
    rcases ((nonsingular_iff' x y).mp h).2 with h' | h'
    · exact h'
    · exact absurd hy h'
  have key : Q1 W x x = (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) ^ 2 := by
    simp only [yψ] at hy
    simp only [Q1, b₄, b₆, b₈]
    linear_combination (8 * x + W.a₁ ^ 2 + 4 * W.a₂) * e +
      ((-4 * x - W.a₁ ^ 2 - 2 * W.a₂) * y +
        (W.a₁ * x ^ 2 + W.a₁ * W.a₂ * x - 2 * W.a₃ * x + W.a₁ * W.a₄ - W.a₂ * W.a₃)) * hy
  rw [key]; exact pow_ne_zero 2 hD

/-- Kummer law for `A + A` (with `A - A = O`). -/
lemma kummer_double (A : W.toAffine.Point) :
    ∃ c : F, sym (xP (A + A)) (1, 0) = c • kB W (xP A) (xP A) := by
  rcases A with _ | ⟨x, y, h⟩
  · refine ⟨1, ?_⟩
    rw [← Point.zero_def, zero_add, xP_zero]
    simp only [sym, kB, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  · rw [xP_some, kB_affine, S1_self]
    by_cases hy : yψ W x y = 0
    · have hy' : y = W.toAffine.negY x y := yψ_eq_zero_iff.mp hy
      rw [Point.add_self_of_Y_eq hy', xP_zero]
      have hf : fx W x = 0 := by rw [← yψ_sq h.1, hy]; ring
      have hQ := Q1_self_ne_zero_of_two_torsion h hy
      refine ⟨(Q1 W x x)⁻¹, ?_⟩
      simp only [sym, hf, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      refine ⟨by ring, by ring, by field_simp⟩
    · obtain ⟨x₃, y₃, h₃, hA, hx₃⟩ := double_some h hy
      rw [hA, xP_some]
      refine ⟨(yψ W x y ^ 2)⁻¹, ?_⟩
      have hf : fx W x = yψ W x y ^ 2 := (yψ_sq h.1).symm
      simp only [sym, hf, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      refine ⟨by ring, by field_simp <;> ring_nf, ?_⟩
      rw [← hx₃]; field_simp

/-- Addition and subtraction of affine points with distinct `x`-coordinates. -/
lemma add_sub_of_X_ne {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    ∃ (x₃ y₃ : F) (h₃ : W.toAffine.Nonsingular x₃ y₃) (x₄ y₄ : F)
      (h₄ : W.toAffine.Nonsingular x₄ y₄),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
      Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ = Point.some x₄ y₄ h₄ ∧
      (x₃ + x₄) * (x₁ - x₂) ^ 2 = S1 W x₁ x₂ ∧
      x₃ * x₄ * (x₁ - x₂) ^ 2 = Q1 W x₁ x₂ ∧
      (x₃ - x₄) * (x₁ - x₂) ^ 2 = -(yψ W x₁ y₁ * yψ W x₂ y₂) := by
  have h₂' : W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) := (nonsingular_neg ..).mpr h₂
  refine ⟨_, _, nonsingular_add h₁ h₂ (fun e => hx e.1), _, _,
    nonsingular_add h₁ h₂' (fun e => hx e.1), Point.add_of_X_ne hx, ?_, ?_⟩
  · rw [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hx]
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have e₁ := eqn h₁.1
  have e₂ := eqn h₂.1
  have E3 : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
    rw [addX, slope_of_X_ne hx]; field_simp; ring
  have E4 : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) *
      (x₁ - x₂) ^ 2 = (y₁ + y₂ + W.a₁ * x₂ + W.a₃) ^ 2 +
        W.a₁ * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
    rw [addX, slope_of_X_ne hx, negY]; field_simp; ring
  set x₃ := W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)
  set x₄ := W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
  refine ⟨?_, ?_, ?_⟩
  · simp only [S1, b₂, b₄, b₆]
    linear_combination E3 + E4 + 2 * e₁ + 2 * e₂
  · have key : (x₁ - x₂) ^ 2 * (x₃ * x₄ * (x₁ - x₂) ^ 2 - Q1 W x₁ x₂) = 0 := by
      simp only [Q1, b₄, b₆, b₈]
      linear_combination (x₄ * (x₁ - x₂) ^ 2) * E3 +
        ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) * E4 +
        (-x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ - x₁ ^ 2 * W.a₂ + x₁ * y₁ * W.a₁ + 2 * x₁ * x₂ ^ 2 +
          x₁ * x₂ * W.a₁ ^ 2 + 4 * x₁ * x₂ * W.a₂ + x₁ * W.a₁ * W.a₃ + x₁ * W.a₄ + y₁ ^ 2 +
          y₁ * W.a₃ - 2 * x₂ ^ 3 - x₂ ^ 2 * W.a₁ ^ 2 - 2 * x₂ ^ 2 * W.a₂ - 2 * x₂ * y₂ * W.a₁ -
          x₂ * W.a₁ * W.a₃ - 2 * y₂ ^ 2 - 2 * y₂ * W.a₃ + W.a₆) * e₁ +
        (-4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ - x₁ ^ 2 * W.a₁ ^ 2 - 4 * x₁ ^ 2 * W.a₂ +
          2 * x₁ * x₂ ^ 2 + x₁ * x₂ * W.a₁ ^ 2 + 4 * x₁ * x₂ * W.a₂ - x₁ * W.a₁ * W.a₃ -
          2 * x₁ * W.a₄ - x₂ ^ 3 - x₂ ^ 2 * W.a₂ + x₂ * y₂ * W.a₁ + x₂ * W.a₁ * W.a₃ +
          x₂ * W.a₄ + y₂ ^ 2 + y₂ * W.a₃ - W.a₆) * e₂
    have := (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hd)
    linear_combination this
  · simp only [yψ]
    linear_combination E3 - E4

/-- **Kummer law.** For all points `A, B`, the pair `{x(A+B), x(A-B)}` is determined (projectively)
by `x(A)` and `x(B)` through the biquadratic forms `kB`. -/
theorem kummer (A B : W.toAffine.Point) :
    ∃ c : F, sym (xP (A + B)) (xP (A - B)) = c • kB W (xP A) (xP B) := by
  rcases A with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, zero_sub, xP_neg, xP_zero]
    refine ⟨1, ?_⟩
    simp only [sym, kB, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  rcases B with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, sub_zero, xP_zero]
    refine ⟨1, ?_⟩
    simp only [sym, kB, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  by_cases hx : x₁ = x₂
  · subst hx
    rcases Y_eq_of_X_eq h₁.1 h₂.1 rfl with rfl | rfl
    · rw [sub_self, xP_zero]
      exact kummer_double _
    · have hneg : Point.some x₁ (W.toAffine.negY x₁ y₂) h₁ = -Point.some x₁ y₂ h₂ := rfl
      rw [hneg, neg_add_cancel, show -Point.some x₁ y₂ h₂ - Point.some x₁ y₂ h₂ =
        -(Point.some x₁ y₂ h₂ + Point.some x₁ y₂ h₂) by abel, xP_neg, xP_zero, sym_comm, xP_neg]
      exact kummer_double _
  · obtain ⟨x₃, y₃, h₃, x₄, y₄, h₄, hadd, hsub, hS, hQ, -⟩ := add_sub_of_X_ne h₁ h₂ hx
    rw [hadd, hsub, xP_some, xP_some, xP_some, xP_some, kB_affine]
    have hd : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
    refine ⟨((x₁ - x₂) ^ 2)⁻¹, ?_⟩
    simp only [sym, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨by field_simp, ?_, ?_⟩
    · rw [← hS]; field_simp <;> ring_nf
    · rw [← hQ]; field_simp

end Kummer

/-! ## Part B: the generic multiplication formula (O2) -/

section Mult

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

/-- `Q` is an affine point with `x`-coordinate `a`. -/
def HasX (Q : W.toAffine.Point) (a : F) : Prop :=
  ∃ (b : F) (h : W.toAffine.Nonsingular a b), Q = Point.some a b h

lemma HasX_of_eq {Q : W.toAffine.Point} {a b c : F} {h : W.toAffine.Nonsingular a b}
    (hQ : Q = Point.some a b h) (hac : a = c) : HasX Q c := by
  subst hac; exact ⟨b, h, hQ⟩

lemma HasX_unique {Q : W.toAffine.Point} {a a' : F} (h : HasX Q a) (h' : HasX Q a') : a = a' := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', e⟩ := h'
  simp only [Point.some.injEq] at e
  exact e.1

/-- The division polynomial `ψₙ` evaluated at `(x, y)`. -/
noncomputable def wv (W : WeierstrassCurve F) (x y : F) (n : ℤ) : F := (W.ψ n).evalEval x y

/-- The rational function `x - ψ_{n+1} ψ_{n-1} / ψ_n²` at `(x, y)`. -/
noncomputable def xs (W : WeierstrassCurve F) (x y : F) (n : ℤ) : F :=
  x - wv W x y (n + 1) * wv W x y (n - 1) / wv W x y n ^ 2

lemma wv_zero (x y : F) : wv W x y 0 = 0 := by simp [wv]

lemma wv_one (x y : F) : wv W x y 1 = 1 := by simp [wv]

lemma wv_two (x y : F) : wv W x y 2 = yψ W x y := by
  simp only [wv, ψ_two, ψ₂, evalEval_polynomialY, yψ]

lemma wv_three (x y : F) :
    wv W x y 3 = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  rw [wv, ψ_three, evalEval_C]; simp [Ψ₃]

lemma wv_four (x y : F) : wv W x y 4 = (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 +
    10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x +
    (W.b₄ * W.b₈ - W.b₆ ^ 2)) * yψ W x y := by
  rw [wv, ψ_four, evalEval_mul, evalEval_C, ψ₂, evalEval_polynomialY, yψ]
  congr 1
  simp [preΨ₄]

lemma wv_odd (x y : F) (m : ℤ) : wv W x y (2 * m + 1) =
    wv W x y (m + 2) * wv W x y m ^ 3 - wv W x y (m - 1) * wv W x y (m + 1) ^ 3 := by
  simp only [wv, ψ_odd, evalEval_sub, evalEval_mul, evalEval_pow]

lemma wv_even (x y : F) (m : ℤ) : wv W x y (2 * m) * yψ W x y =
    wv W x y (m - 1) ^ 2 * wv W x y m * wv W x y (m + 2) -
      wv W x y (m - 2) * wv W x y m * wv W x y (m + 1) ^ 2 := by
  have := congrArg (evalEval x y) (W.ψ_even m)
  simp only [evalEval_sub, evalEval_mul, evalEval_pow, ψ₂, evalEval_polynomialY] at this
  simpa only [wv, yψ] using this

lemma xs_rel (x y : F) (n : ℤ) (hn : wv W x y n ≠ 0) :
    wv W x y (n + 1) * wv W x y (n - 1) = wv W x y n ^ 2 * (x - xs W x y n) := by
  rw [xs, sub_sub_cancel]; field_simp

lemma xs_eq_of {x y s : F} {n : ℤ} (hn : wv W x y n ≠ 0)
    (h : wv W x y (n + 1) * wv W x y (n - 1) = (x - s) * wv W x y n ^ 2) : s = xs W x y n := by
  rw [xs, h, mul_div_assoc, div_self (pow_ne_zero 2 hn), mul_one]; ring

lemma odd_alg (x y : F) (j : ℤ) (hb : wv W x y j ≠ 0) (hc : wv W x y (j + 1) ≠ 0) :
    wv W x y (2 * j + 1) =
      wv W x y j ^ 2 * wv W x y (j + 1) ^ 2 * (xs W x y j - xs W x y (j + 1)) := by
  have R1 := xs_rel x y j hb
  have R2 := xs_rel x y (j + 1) hc
  rw [show j + 1 + 1 = j + 2 by ring, show j + 1 - 1 = j by ring] at R2
  rw [wv_odd]
  linear_combination wv W x y j ^ 2 * R2 - wv W x y (j + 1) ^ 2 * R1

lemma even_alg (x y : F) (j : ℤ) (ha : wv W x y (j - 1) ≠ 0) (hc : wv W x y (j + 1) ≠ 0) :
    wv W x y (2 * j) * yψ W x y =
      wv W x y (j - 1) ^ 2 * wv W x y (j + 1) ^ 2 * (xs W x y (j - 1) - xs W x y (j + 1)) := by
  have R3 := xs_rel x y (j - 1) ha
  have R2 := xs_rel x y (j + 1) hc
  rw [show j + 1 + 1 = j + 2 by ring, show j + 1 - 1 = j by ring] at R2
  rw [show j - 1 + 1 = j by ring, show j - 1 - 1 = j - 2 by ring] at R3
  rw [wv_even]
  linear_combination wv W x y (j - 1) ^ 2 * R2 - wv W x y (j + 1) ^ 2 * R3

/-- Sum, product and difference relations, packaged with the existence of the two points. -/
lemma rel_of_X_ne {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    ∃ a b : F, HasX (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) a ∧
      HasX (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) b ∧
      (a + b) * (x₁ - x₂) ^ 2 = S1 W x₁ x₂ ∧ a * b * (x₁ - x₂) ^ 2 = Q1 W x₁ x₂ ∧
      (a - b) * (x₁ - x₂) ^ 2 = -(yψ W x₁ y₁ * yψ W x₂ y₂) := by
  obtain ⟨x₃, y₃, h₃, x₄, y₄, h₄, hadd, hsub, hS, hQ, hD⟩ := add_sub_of_X_ne h₁ h₂ hx
  exact ⟨x₃, x₄, ⟨y₃, h₃, hadd⟩, ⟨y₄, h₄, hsub⟩, hS, hQ, hD⟩

lemma odd_step {x y : F} {h : W.toAffine.Nonsingular x y}
    (hw : ∀ n : ℤ, n ≠ 0 → wv W x y n ≠ 0) (j : ℤ) (hj : 2 ≤ j)
    {Qa Qb Qc Qd : W.toAffine.Point}
    (h1 : Qb + Point.some x y h = Qc) (h2 : Qb - Point.some x y h = Qa)
    (h3 : Qc + Point.some x y h = Qd) (h4 : Qc - Point.some x y h = Qb)
    (h5 : Qc - Qb = Point.some x y h)
    (ha : HasX Qa (xs W x y (j - 1))) (hb : HasX Qb (xs W x y j))
    (hc : HasX Qc (xs W x y (j + 1))) (hd : HasX Qd (xs W x y (j + 2))) :
    HasX (Qc + Qb) (xs W x y (2 * j + 1)) := by
  obtain ⟨yb, hyb, rfl⟩ := hb
  obtain ⟨yc, hyc, rfl⟩ := hc
  have ha0 : wv W x y (j - 1) ≠ 0 := hw _ (by omega)
  have hb0 : wv W x y j ≠ 0 := hw _ (by omega)
  have hc0 : wv W x y (j + 1) ≠ 0 := hw _ (by omega)
  have hd0 : wv W x y (j + 2) ≠ 0 := hw _ (by omega)
  have hε : yψ W x y ≠ 0 := by rw [← wv_two]; exact hw 2 (by norm_num)
  have A : (xs W x y j - x) * wv W x y j ^ 2 = -(wv W x y (j + 1) * wv W x y (j - 1)) := by
    linear_combination xs_rel x y j hb0
  have B : (xs W x y (j + 1) - x) * wv W x y (j + 1) ^ 2 = -(wv W x y (j + 2) * wv W x y j) := by
    have := xs_rel x y (j + 1) hc0
    rw [show j + 1 + 1 = j + 2 by ring, show j + 1 - 1 = j by ring] at this
    linear_combination this
  have Eo := odd_alg x y j hb0 hc0
  have E1 := even_alg x y (j + 1) (by rw [show j + 1 - 1 = j by ring]; exact hb0)
    (by rw [show j + 1 + 1 = j + 2 by ring]; exact hd0)
  rw [show j + 1 - 1 = j by ring, show j + 1 + 1 = j + 2 by ring] at E1
  have E2 := even_alg x y j ha0 hc0
  have hNw : wv W x y (2 * j + 1) ≠ 0 := hw _ (by omega)
  have huw : xs W x y j ≠ xs W x y (j + 1) := by
    intro e; apply hNw; rw [Eo, e, sub_self, mul_zero]
  have hux : xs W x y j ≠ x := by
    intro e; rw [e, sub_self, zero_mul] at A
    exact mul_ne_zero hc0 ha0 (neg_eq_zero.mp A.symm)
  have hwx : xs W x y (j + 1) ≠ x := by
    intro e; rw [e, sub_self, zero_mul] at B
    exact mul_ne_zero hd0 hb0 (neg_eq_zero.mp B.symm)
  -- DIFF on (Qb, P)
  obtain ⟨a1, b1, hA1, hB1, -, -, D1⟩ := rel_of_X_ne hyb h hux
  rw [h1] at hA1; rw [h2] at hB1
  have e1 : a1 = xs W x y (j + 1) := HasX_unique hA1 ⟨yc, hyc, rfl⟩
  have e1' : b1 = xs W x y (j - 1) := HasX_unique hB1 ha
  rw [e1, e1'] at D1
  -- DIFF on (Qc, P)
  obtain ⟨a2, b2, hA2, hB2, -, -, D2⟩ := rel_of_X_ne hyc h hwx
  rw [h3] at hA2; rw [h4] at hB2
  have e2 : a2 = xs W x y (j + 2) := HasX_unique hA2 hd
  have e2' : b2 = xs W x y j := HasX_unique hB2 ⟨yb, hyb, rfl⟩
  rw [e2, e2'] at D2
  -- DIFF on (Qc, Qb)
  obtain ⟨s, b3, hA3, hB3, -, -, D3⟩ := rel_of_X_ne hyc hyb (Ne.symm huw)
  rw [h5] at hB3
  have e3 : b3 = x := HasX_unique hB3 ⟨y, h, rfl⟩
  rw [e3] at D3
  obtain ⟨ys, hys, hs⟩ := hA3
  refine HasX_of_eq hs ?_
  -- algebra
  set t := xs W x y (j - 1)
  set u := xs W x y j
  set w' := xs W x y (j + 1)
  set z := xs W x y (j + 2)
  set η := yψ W u yb
  set η' := yψ W w' yc
  set ε := yψ W x y
  have hηε : η * ε = (t - w') * (u - x) ^ 2 := by linear_combination D1
  have hη'ε : η' * ε = (u - z) * (w' - x) ^ 2 := by linear_combination D2
  have hprod : wv W x y (2 * (j + 1)) * wv W x y (2 * j) =
      wv W x y j ^ 4 * wv W x y (j + 1) ^ 4 * η * η' := by
    have key : wv W x y (2 * (j + 1)) * wv W x y (2 * j) * ε ^ 2 =
        wv W x y j ^ 4 * wv W x y (j + 1) ^ 4 * η * η' * ε ^ 2 := by
      calc wv W x y (2 * (j + 1)) * wv W x y (2 * j) * ε ^ 2
          = (wv W x y (2 * (j + 1)) * ε) * (wv W x y (2 * j) * ε) := by ring
        _ = (wv W x y j ^ 2 * wv W x y (j + 2) ^ 2 * (u - z)) *
              (wv W x y (j - 1) ^ 2 * wv W x y (j + 1) ^ 2 * (t - w')) := by rw [E1, E2]
        _ = (t - w') * (u - z) * ((u - x) * wv W x y j ^ 2) ^ 2 *
              ((w' - x) * wv W x y (j + 1) ^ 2) ^ 2 := by rw [A, B]; ring
        _ = wv W x y j ^ 4 * wv W x y (j + 1) ^ 4 * ((t - w') * (u - x) ^ 2) *
              ((u - z) * (w' - x) ^ 2) := by ring
        _ = wv W x y j ^ 4 * wv W x y (j + 1) ^ 4 * (η * ε) * (η' * ε) := by rw [hηε, hη'ε]
        _ = _ := by ring
    exact mul_right_cancel₀ (pow_ne_zero 2 hε) key
  apply xs_eq_of hNw
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, show 2 * j + 1 - 1 = 2 * j by ring, hprod, Eo]
  linear_combination wv W x y j ^ 4 * wv W x y (j + 1) ^ 4 * D3

lemma even_step {x y : F} {h : W.toAffine.Nonsingular x y}
    (hw : ∀ n : ℤ, n ≠ 0 → wv W x y n ≠ 0) (j : ℤ) (hj : 2 ≤ j)
    {Qa Qb Qc : W.toAffine.Point}
    (h1 : Qb + Point.some x y h = Qc) (h2 : Qb - Point.some x y h = Qa)
    (ha : HasX Qa (xs W x y (j - 1))) (hb : HasX Qb (xs W x y j))
    (hc : HasX Qc (xs W x y (j + 1))) :
    HasX (Qb + Qb) (xs W x y (2 * j)) := by
  obtain ⟨yb, hyb, rfl⟩ := hb
  have ha0 : wv W x y (j - 1) ≠ 0 := hw _ (by omega)
  have hb0 : wv W x y j ≠ 0 := hw _ (by omega)
  have hc0 : wv W x y (j + 1) ≠ 0 := hw _ (by omega)
  have hε : yψ W x y ≠ 0 := by rw [← wv_two]; exact hw 2 (by norm_num)
  have A : (xs W x y j - x) * wv W x y j ^ 2 = -(wv W x y (j + 1) * wv W x y (j - 1)) := by
    linear_combination xs_rel x y j hb0
  have Eo := odd_alg x y j hb0 hc0
  have Eo' := odd_alg x y (j - 1) ha0 (by rw [show j - 1 + 1 = j by ring]; exact hb0)
  rw [show j - 1 + 1 = j by ring, show 2 * (j - 1) + 1 = 2 * j - 1 by ring] at Eo'
  have Ee := even_alg x y j ha0 hc0
  have h2j : wv W x y (2 * j) ≠ 0 := hw _ (by omega)
  have hux : xs W x y j ≠ x := by
    intro e; rw [e, sub_self, zero_mul] at A
    exact mul_ne_zero hc0 ha0 (neg_eq_zero.mp A.symm)
  have htw : xs W x y (j - 1) - xs W x y (j + 1) ≠ 0 := by
    intro e; apply mul_ne_zero h2j hε; rw [Ee, e, mul_zero]
  obtain ⟨a1, b1, hA1, hB1, SUM, PROD, D1⟩ := rel_of_X_ne hyb h hux
  rw [h1] at hA1; rw [h2] at hB1
  have e1 : a1 = xs W x y (j + 1) := HasX_unique hA1 hc
  have e1' : b1 = xs W x y (j - 1) := HasX_unique hB1 ha
  rw [e1, e1'] at D1 SUM PROD
  set t := xs W x y (j - 1)
  set u := xs W x y j
  set w' := xs W x y (j + 1)
  set η := yψ W u yb
  set ε := yψ W x y
  have hηε : η * ε = (t - w') * (u - x) ^ 2 := by linear_combination D1
  have hη : η ≠ 0 := by
    intro e; rw [e, zero_mul] at hηε
    exact mul_ne_zero htw (pow_ne_zero 2 (sub_ne_zero.mpr hux)) hηε.symm
  obtain ⟨s, ys, hys, hD, hsx⟩ := double_some hyb hη
  refine HasX_of_eq hD ?_
  have hη2 : η ^ 2 = fx W u := yψ_sq hyb.1
  have hQ : Q1 W u u = x * fx W u - (u - w') * (t - u) * (u - x) ^ 2 := by
    simp only [Q1, S1, fx] at SUM PROD ⊢
    linear_combination u * SUM - PROD
  have hs2 : (x - s) * η ^ 2 = (u - w') * (t - u) * (u - x) ^ 2 := by
    linear_combination x * hη2 - hsx - hQ
  have hK : wv W x y (2 * j + 1) * wv W x y (2 * j - 1) * η ^ 2 =
      wv W x y (2 * j) ^ 2 * ((u - w') * (t - u) * (u - x) ^ 2) := by
    have key : wv W x y (2 * j + 1) * wv W x y (2 * j - 1) * η ^ 2 * ε ^ 2 =
        wv W x y (2 * j) ^ 2 * ((u - w') * (t - u) * (u - x) ^ 2) * ε ^ 2 := by
      calc wv W x y (2 * j + 1) * wv W x y (2 * j - 1) * η ^ 2 * ε ^ 2
          = (wv W x y j ^ 2 * wv W x y (j + 1) ^ 2 * (u - w')) *
              (wv W x y (j - 1) ^ 2 * wv W x y j ^ 2 * (t - u)) * (η * ε) ^ 2 := by
            rw [Eo, Eo']; ring
        _ = wv W x y (j - 1) ^ 2 * wv W x y (j + 1) ^ 2 * (t - w') ^ 2 * (u - w') * (t - u) *
              (u - x) ^ 2 * ((u - x) * wv W x y j ^ 2) ^ 2 := by rw [hηε]; ring
        _ = (wv W x y (j - 1) ^ 2 * wv W x y (j + 1) ^ 2 * (t - w')) ^ 2 *
              ((u - w') * (t - u) * (u - x) ^ 2) := by rw [A]; ring
        _ = (wv W x y (2 * j) * ε) ^ 2 * ((u - w') * (t - u) * (u - x) ^ 2) := by rw [Ee]
        _ = _ := by ring
    exact mul_right_cancel₀ (pow_ne_zero 2 hε) key
  apply xs_eq_of h2j
  apply mul_right_cancel₀ (pow_ne_zero 2 hη)
  linear_combination hK - wv W x y (2 * j) ^ 2 * hs2

/-- **Generic multiplication formula (O2).** If no `ψₙ` vanishes at `P = (x, y)`, then
`x(nP) = x - ψ_{n+1} ψ_{n-1} / ψₙ²` for every `n ≥ 1`. -/
theorem mult_formula {x y : F} (h : W.toAffine.Nonsingular x y)
    (hw : ∀ n : ℤ, n ≠ 0 → wv W x y n ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    HasX (N • Point.some x y h) (xs W x y N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  have hε : yψ W x y ≠ 0 := by rw [← wv_two]; exact hw 2 (by norm_num)
  have hf : yψ W x y ^ 2 = fx W x := yψ_sq h.1
  have hxs1 : xs W x y 1 = x := by simp [xs, wv_zero]
  rcases (by omega : N = 1 ∨ N = 2 ∨ N = 3 ∨ 4 ≤ N) with rfl | rfl | rfl | hN4
  · rw [one_smul, Nat.cast_one, hxs1]; exact ⟨y, h, rfl⟩
  · obtain ⟨x₃, y₃, h₃, hA, hx₃⟩ := double_some h hε
    rw [Nat.cast_ofNat, two_nsmul, hA]
    refine HasX_of_eq rfl ?_
    apply xs_eq_of (hw 2 (by norm_num))
    rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, wv_three, wv_one,
      wv_two]
    simp only [Q1, fx] at hx₃ hf
    linear_combination hx₃ - x * hf
  · rw [Nat.cast_ofNat]
    have i2 := ih 2 (by norm_num) (by norm_num)
    rw [Nat.cast_ofNat] at i2
    obtain ⟨y2, h2, e2⟩ := i2
    have R := xs_rel x y 2 (hw 2 (by norm_num))
    rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, wv_one, mul_one,
      wv_two, wv_three] at R
    have hx2 : xs W x y 2 ≠ x := by
      intro e
      have h3 := hw 3 (by norm_num)
      rw [wv_three] at h3
      apply h3; rw [R, e, sub_self, mul_zero]
    obtain ⟨a1, b1, hA1, hB1, SUM, -, -⟩ := rel_of_X_ne h2 h hx2
    rw [← e2] at hA1 hB1
    have e3 : (3 : ℕ) • Point.some x y h = 2 • Point.some x y h + Point.some x y h :=
      succ_nsmul _ 2
    have eP : 2 • Point.some x y h - Point.some x y h = Point.some x y h := by
      rw [two_nsmul, add_sub_cancel_right]
    rw [eP] at hB1
    have eb : b1 = x := HasX_unique hB1 ⟨y, h, rfl⟩
    rw [eb] at SUM
    rw [e3]
    obtain ⟨ya, hya, ha⟩ := hA1
    refine HasX_of_eq ha ?_
    apply xs_eq_of (hw 3 (by norm_num))
    rw [show (3 : ℤ) + 1 = 4 by norm_num, show (3 : ℤ) - 1 = 2 by norm_num, wv_four, wv_two,
      wv_three]
    set x2 := xs W x y 2
    set ε := yψ W x y
    simp only [S1, fx] at SUM hf
    linear_combination (-(x - a1) * ((3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x +
      W.b₈) + ε ^ 2 * (x - x2)) + ε ^ 2 * (6 * x ^ 2 + W.b₂ * x + W.b₄)) * R + ε ^ 4 * SUM +
      ε ^ 2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * hf + ε ^ 2 * x ^ 2 * W.b_relation
  · obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' N
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      subst hk
      have iha := ih (m + 1) (by omega) (by omega)
      have ihb := ih (m + 2) (by omega) (by omega)
      have ihc := ih (m + 3) (by omega) (by omega)
      rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 2 - 1 by push_cast; ring] at iha
      rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by push_cast; ring] at ihb
      rw [show ((m + 3 : ℕ) : ℤ) = (m : ℤ) + 2 + 1 by push_cast; ring] at ihc
      have s1 : (m + 2) • Point.some x y h + Point.some x y h = (m + 3) • Point.some x y h :=
        (succ_nsmul _ (m + 2)).symm
      have s2 : (m + 1) • Point.some x y h + Point.some x y h = (m + 2) • Point.some x y h :=
        (succ_nsmul _ (m + 1)).symm
      have h2 : (m + 2) • Point.some x y h - Point.some x y h = (m + 1) • Point.some x y h := by
        rw [← s2]; abel
      rw [show ((2 * (m + 2) : ℕ) : ℤ) = 2 * ((m : ℤ) + 2) by push_cast; ring,
        show 2 * (m + 2) = (m + 2) + (m + 2) by ring, add_nsmul]
      exact even_step hw ((m : ℤ) + 2) (by omega) s1 h2 iha ihb ihc
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      subst hk
      have iha := ih (m + 1) (by omega) (by omega)
      have ihb := ih (m + 2) (by omega) (by omega)
      have ihc := ih (m + 3) (by omega) (by omega)
      have ihd := ih (m + 4) (by omega) (by omega)
      rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 2 - 1 by push_cast; ring] at iha
      rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by push_cast; ring] at ihb
      rw [show ((m + 3 : ℕ) : ℤ) = (m : ℤ) + 2 + 1 by push_cast; ring] at ihc
      rw [show ((m + 4 : ℕ) : ℤ) = (m : ℤ) + 2 + 2 by push_cast; ring] at ihd
      have s1 : (m + 2) • Point.some x y h + Point.some x y h = (m + 3) • Point.some x y h :=
        (succ_nsmul _ (m + 2)).symm
      have s2 : (m + 1) • Point.some x y h + Point.some x y h = (m + 2) • Point.some x y h :=
        (succ_nsmul _ (m + 1)).symm
      have s3 : (m + 3) • Point.some x y h + Point.some x y h = (m + 4) • Point.some x y h :=
        (succ_nsmul _ (m + 3)).symm
      have h2 : (m + 2) • Point.some x y h - Point.some x y h = (m + 1) • Point.some x y h := by
        rw [← s2]; abel
      have h4 : (m + 3) • Point.some x y h - Point.some x y h = (m + 2) • Point.some x y h := by
        rw [← s1]; abel
      have h5 : (m + 3) • Point.some x y h - (m + 2) • Point.some x y h = Point.some x y h := by
        rw [← s1]; abel
      rw [show ((2 * (m + 2) + 1 : ℕ) : ℤ) = 2 * ((m : ℤ) + 2) + 1 by push_cast; ring,
        show 2 * (m + 2) + 1 = (m + 3) + (m + 2) by ring, add_nsmul]
      exact odd_step hw ((m : ℤ) + 2) (by omega) s1 h2 s3 h4 h5 iha ihb ihc ihd

end Mult

/-! ## Part C: universal Kummer identities via the generic point (O3) -/

section Universal

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The `ZZ` component of the Kummer identity, straight from the definitions. -/
lemma zz_id (n : ℤ) : W.ΨSq (n + 1) * W.ΨSq (n - 1) = (W.Φ n - X * W.ΨSq n) ^ 2 := by
  by_cases hn : Even n <;>
    simp only [WeierstrassCurve.Φ, WeierstrassCurve.ΨSq, Int.even_add_one, Int.even_sub_one, hn,
      not_true_eq_false, not_false_eq_true, if_true, if_false] <;> ring

/-- The `XZ` and `XX` components of the Kummer identity `I_n`. -/
def KumId (n : ℤ) : Prop :=
  W.Φ (n + 1) * W.ΨSq (n - 1) + W.Φ (n - 1) * W.ΨSq (n + 1) =
      2 * W.Φ n * X * (W.Φ n + X * W.ΨSq n) + C W.b₂ * W.Φ n * X * W.ΨSq n +
        C W.b₄ * (W.Φ n + X * W.ΨSq n) * W.ΨSq n + C W.b₆ * W.ΨSq n ^ 2 ∧
    W.Φ (n + 1) * W.Φ (n - 1) = W.Φ n ^ 2 * X ^ 2 - C W.b₄ * W.Φ n * X * W.ΨSq n -
      C W.b₆ * (W.Φ n + X * W.ΨSq n) * W.ΨSq n - C W.b₈ * W.ΨSq n ^ 2

lemma kumId_one : KumId W 1 := by
  refine ⟨?_, ?_⟩ <;>
    simp [WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two, Ψ₂Sq, map_mul, map_ofNat] <;> ring

end Universal

section Generic

open WeierstrassCurve.Affine.CoordinateRing

/-- The universal Weierstrass curve over `ℤ[A₁, A₂, A₃, A₄, A₆]`. -/
noncomputable def Wu : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨.X 0, .X 1, .X 2, .X 3, .X 4⟩


/-- Evaluation at the generic point of the universal curve. -/
noncomputable def θ : Polynomial (Polynomial (MvPolynomial (Fin 5) ℤ)) →+* (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))) :=
  (algebraMap (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)))).comp (mk Wu.toAffine)

lemma θ_CC (r : (MvPolynomial (Fin 5) ℤ)) : θ (C (C r)) = algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))) r := by
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 5) ℤ) (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)))]; rfl

lemma θ_eq (p : Polynomial (Polynomial (MvPolynomial (Fin 5) ℤ))) :
    θ p = (p.map (mapRingHom (algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)))))).evalEval (θ (C X)) (θ X) := by
  have key : θ = eval₂RingHom (eval₂RingHom (algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)))) (θ (C X))) (θ X) := by
    refine Polynomial.ringHom_ext (fun a => ?_) (by simp)
    rw [coe_eval₂RingHom, eval₂_C]
    show (θ.comp C) a = eval₂RingHom (algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)))) (θ (C X)) a
    congr 1
    exact Polynomial.ringHom_ext (fun r => by simp [θ_CC]) (by simp)
  conv_lhs => rw [key]
  rw [coe_eval₂RingHom, eval₂_eval₂RingHom_apply]

lemma θC_inj : Function.Injective (fun q : Polynomial (MvPolynomial (Fin 5) ℤ) => θ (C q)) := by
  have e : (fun q : Polynomial (MvPolynomial (Fin 5) ℤ) => θ (C q)) = (algebraMap (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)))) ∘ (algebraMap (Polynomial (MvPolynomial (Fin 5) ℤ)) (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))) := by
    funext q; rfl
  rw [e]
  exact (IsFractionRing.injective (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu)))).comp (FaithfulSMul.algebraMap_injective _ _)

/-- The universal curve base changed to the function field. -/
noncomputable abbrev Wk : WeierstrassCurve (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))) := Wu.map (algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))))

lemma wv_generic (n : ℤ) : wv Wk (θ (C X)) (θ X) n = θ (Wu.ψ n) := by
  rw [wv, map_ψ, ← θ_eq]

lemma wv_generic_sq (n : ℤ) : wv Wk (θ (C X)) (θ X) n ^ 2 = θ (C (Wu.ΨSq n)) := by
  rw [wv_generic, ← map_pow]
  simp only [θ, RingHom.comp_apply, map_pow, mk_ψ]
  rw [← map_pow]
  exact congrArg (algebraMap _ _) (mk_Ψ_sq Wu n)

lemma wv_generic_ne (n : ℤ) (hn : n ≠ 0) : wv Wk (θ (C X)) (θ X) n ≠ 0 := by
  intro h
  have h2 := wv_generic_sq n
  rw [h, zero_pow two_ne_zero] at h2
  have hne : Wu.ΨSq n ≠ 0 := Wu.ΨSq_ne_zero (by exact_mod_cast hn)
  exact hne (θC_inj (by simpa using h2.symm))

lemma Φ_generic (n : ℤ) : θ (C (Wu.Φ n)) = θ (C X) * wv Wk (θ (C X)) (θ X) n ^ 2 -
    wv Wk (θ (C X)) (θ X) (n + 1) * wv Wk (θ (C X)) (θ X) (n - 1) := by
  simp only [wv_generic]
  have : θ (C (Wu.Φ n)) = θ (Wu.φ n) := by
    simp only [θ, RingHom.comp_apply, mk_φ]
  have e : Wu.φ n + Wu.ψ (n + 1) * Wu.ψ (n - 1) = C X * Wu.ψ n ^ 2 := by
    rw [WeierstrassCurve.φ]; ring
  have e2 := congrArg θ e
  rw [map_add, map_mul, map_mul, map_pow] at e2
  rw [this]
  linear_combination e2

lemma equation_generic : Wk.toAffine.Equation (θ (C X)) (θ X) := by
  rw [Affine.Equation]
  have hp := Affine.map_polynomial (W := Wu.toAffine) (f := algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))))
  rw [show (Wk.toAffine).polynomial = _ from hp, ← θ_eq]
  simp only [θ, RingHom.comp_apply, AdjoinRoot.mk_self, map_zero]

lemma nonsingular_generic : Wk.toAffine.Nonsingular (θ (C X)) (θ X) := by
  have h2 := wv_generic_ne 2 (by norm_num)
  rw [wv_two, yψ] at h2
  exact (nonsingular_iff' _ _).mpr ⟨equation_generic, Or.inr h2⟩

end Generic

/-! ## Part D: the Kummer identities over every ring (O3) and the local formula (O4) -/

section GenericKum

open WeierstrassCurve.Affine.CoordinateRing


lemma kumId_generic (n : ℕ) (hn : 2 ≤ n) : KumId Wu n := by
  classical
  have hns := nonsingular_generic
  have hw : ∀ j : ℤ, j ≠ 0 → wv Wk (θ (C X)) (θ X) j ≠ 0 := fun j hj => wv_generic_ne j hj
  have hF : ∀ j : ℤ, j ≠ 0 →
      θ (C (Wu.Φ j)) = xs Wk (θ (C X)) (θ X) j * wv Wk (θ (C X)) (θ X) j ^ 2 := by
    intro j hj
    rw [Φ_generic]
    have := xs_rel (θ (C X)) (θ X) j (hw j hj)
    linear_combination -this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  have c1 : ((m + 2 : ℕ) : ℤ) + 1 = ((m + 3 : ℕ) : ℤ) := by push_cast; ring
  have c2 : ((m + 2 : ℕ) : ℤ) - 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  have H0 := mult_formula hns hw (m + 2) (by omega)
  have H1 := mult_formula hns hw (m + 3) (by omega)
  have Hm := mult_formula hns hw (m + 1) (by omega)
  obtain ⟨b, hb, hnP⟩ := H0
  have Rn := xs_rel (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) (hw _ (by omega))
  rw [c1, c2] at Rn
  have hne : xs Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ≠ θ (C X) := by
    intro e
    rw [e, sub_self, mul_zero] at Rn
    exact mul_ne_zero (hw _ (by omega)) (hw _ (by omega)) Rn
  obtain ⟨a, c, Ha, Hc, SUM, PROD, -⟩ := rel_of_X_ne hb hns hne
  rw [← hnP, ← succ_nsmul] at Ha
  rw [← hnP, show m + 2 = (m + 1) + 1 from rfl, succ_nsmul, add_sub_cancel_right] at Hc
  have ea := HasX_unique Ha H1
  have ec := HasX_unique Hc Hm
  subst ea ec
  simp only [S1, Q1, map_b₂, map_b₄, map_b₆, map_b₈] at SUM PROD
  have hF1 := hF ((m + 3 : ℕ) : ℤ) (by omega)
  have hFm := hF ((m + 1 : ℕ) : ℤ) (by omega)
  have hF0 := hF ((m + 2 : ℕ) : ℤ) (by omega)
  refine ⟨?_, ?_⟩
  · apply θC_inj
    simp only [map_add, map_mul, map_pow, map_ofNat, θ_CC, ← wv_generic_sq, c1, c2]
    linear_combination
      wv Wk (θ (C X)) (θ X) ((m + 1 : ℕ) : ℤ) ^ 2 * hF1 +
      wv Wk (θ (C X)) (θ X) ((m + 3 : ℕ) : ℤ) ^ 2 * hFm +
      (xs Wk (θ (C X)) (θ X) ((m + 3 : ℕ) : ℤ) + xs Wk (θ (C X)) (θ X) ((m + 1 : ℕ) : ℤ)) *
        (wv Wk (θ (C X)) (θ X) ((m + 3 : ℕ) : ℤ) * wv Wk (θ (C X)) (θ X) ((m + 1 : ℕ) : ℤ) +
          wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2 *
            (θ (C X) - xs Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ))) * Rn +
      (wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2) ^ 2 * SUM -
      (2 * θ (C X) * (θ (C (Wu.Φ ((m + 2 : ℕ) : ℤ))) + xs Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) *
          wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2) +
        2 * θ (C X) ^ 2 * wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2 +
        algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))) Wu.b₂ * θ (C X) * wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2 +
        algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))) Wu.b₄ * wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2) * hF0
  · rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq, eq_sub_iff_add_eq]
    apply θC_inj
    simp only [map_add, map_mul, map_pow, map_ofNat, θ_CC, ← wv_generic_sq, c1, c2]
    linear_combination
      θ (C (Wu.Φ ((m + 1 : ℕ) : ℤ))) * hF1 +
      xs Wk (θ (C X)) (θ X) ((m + 3 : ℕ) : ℤ) * wv Wk (θ (C X)) (θ X) ((m + 3 : ℕ) : ℤ) ^ 2 * hFm +
      (xs Wk (θ (C X)) (θ X) ((m + 3 : ℕ) : ℤ) * xs Wk (θ (C X)) (θ X) ((m + 1 : ℕ) : ℤ)) *
        (wv Wk (θ (C X)) (θ X) ((m + 3 : ℕ) : ℤ) * wv Wk (θ (C X)) (θ X) ((m + 1 : ℕ) : ℤ) +
          wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2 *
            (θ (C X) - xs Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ))) * Rn +
      (wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2) ^ 2 * PROD -
      (θ (C X) ^ 2 * (θ (C (Wu.Φ ((m + 2 : ℕ) : ℤ))) + xs Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) *
          wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2) -
        algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))) Wu.b₄ * θ (C X) * wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2 -
        algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine Wu))) Wu.b₆ * wv Wk (θ (C X)) (θ X) ((m + 2 : ℕ) : ℤ) ^ 2) * hF0

end GenericKum

section AnyRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The Kummer identities `I_n` hold over every commutative ring, for `n ≥ 1`. -/
lemma kumId (n : ℕ) (hn : 1 ≤ n) : KumId W n := by
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · rw [Nat.cast_one]; exact kumId_one W
  let φ : MvPolynomial (Fin 5) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hW : Wu.map φ = W := by
    ext <;> simp [Wu, φ, WeierstrassCurve.map]
  obtain ⟨h1, h2⟩ := kumId_generic n hn2
  have key : KumId (Wu.map φ) n := by
    refine ⟨?_, ?_⟩
    · simp only [map_Φ, map_ΨSq, map_b₂, map_b₄, map_b₆, map_b₈]
      have := congrArg (mapRingHom φ) h1
      simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, coe_mapRingHom,
        Polynomial.map_C, Polynomial.map_X] using this
    · simp only [map_Φ, map_ΨSq, map_b₂, map_b₄, map_b₆, map_b₈]
      have := congrArg (mapRingHom φ) h2
      simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, coe_mapRingHom,
        Polynomial.map_C, Polynomial.map_X] using this
  rwa [hW] at key

end AnyRing

section Local

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

/-- The pair `(Φₙ(x), ΨSqₙ(x))`. -/
noncomputable def vP (W : WeierstrassCurve F) (x : F) (n : ℤ) : F × F :=
  ((W.Φ n).eval x, (W.ΨSq n).eval x)

lemma kB_vP (x : F) (n : ℕ) :
    kB W (vP W x ((n + 1 : ℕ) : ℤ)) (x, 1) = sym (vP W x ((n + 2 : ℕ) : ℤ)) (vP W x n) := by
  obtain ⟨h1, h2⟩ := kumId W (n + 1) (by omega)
  have h3 := zz_id W ((n + 1 : ℕ) : ℤ)
  have c1 : ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  have c2 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
  rw [c1, c2] at h1 h2 h3
  have e1 := congrArg (eval x) h1
  have e2 := congrArg (eval x) h2
  have e3 := congrArg (eval x) h3
  simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_C, eval_X, eval_ofNat] at e1 e2 e3
  simp only [kB, sym, vP, Prod.mk.injEq]
  refine ⟨by linear_combination -e3, by linear_combination -e1, by linear_combination -e2⟩

/-- **Local multiplication formula (O4).** At every affine point, `x(nP)` is projectively
`(Φₙ(x) : ΨSqₙ(x))`. -/
theorem local_formula {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℕ) :
    ∃ c : F, c ≠ 0 ∧ xP (n • Point.some x y h) = c • vP W x n := by
  suffices H : ∀ n : ℕ, (∃ c : F, c ≠ 0 ∧ xP (n • Point.some x y h) = c • vP W x n) ∧
      (∃ c : F, c ≠ 0 ∧ xP ((n + 1) • Point.some x y h) = c • vP W x ((n + 1 : ℕ) : ℤ)) from
    (H n).1
  intro n
  induction n with
  | zero =>
    refine ⟨⟨1, one_ne_zero, ?_⟩, ⟨1, one_ne_zero, ?_⟩⟩
    · simp [vP, Φ_zero, ΨSq_zero]
    · simp [vP, Φ_one, ΨSq_one]
  | succ n ih =>
    obtain ⟨⟨c0, hc0, e0⟩, ⟨c1, hc1, e1⟩⟩ := ih
    refine ⟨⟨c1, hc1, by exact_mod_cast e1⟩, ?_⟩
    obtain ⟨μ, hμ⟩ := kummer ((n + 1) • Point.some x y h) (Point.some x y h)
    rw [← succ_nsmul, show (n + 1) • Point.some x y h - Point.some x y h = n • Point.some x y h by
      rw [succ_nsmul, add_sub_cancel_right], e0, e1, xP_some, kB_smul_left, kB_vP,
      sym_smul_right, smul_smul] at hμ
    have hv0 : vP W x n ≠ 0 := by
      intro hv; apply xP_ne_zero (n • Point.some x y h); rw [e0, hv, smul_zero]
    have hμ' := congrArg (fun q => c0⁻¹ • q) hμ
    simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hμ'
    have key := sym_cancel hv0 hμ'
    refine ⟨c0⁻¹ * (μ * c1 ^ 2), ?_, by rw [show n + 1 + 1 = n + 2 from rfl]; exact key⟩
    intro hc
    apply xP_ne_zero ((n + 1 + 1) • Point.some x y h)
    rw [show n + 1 + 1 = n + 2 from rfl, key, hc, zero_smul]

lemma vP_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℕ) : vP W x n ≠ 0 := by
  obtain ⟨c, -, e⟩ := local_formula h n
  intro hv; apply xP_ne_zero (n • Point.some x y h); rw [e, hv, smul_zero]

/-- `nP = 0` iff `ΨSqₙ(x) = 0`. -/
lemma nsmul_eq_zero_iff {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℕ) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 := by
  obtain ⟨c, hc, e⟩ := local_formula h n
  rw [← xP_snd_eq_zero_iff, e]
  simp [vP, hc]

/-- If `nP = (x', y')` then `x' ΨSqₙ(x) = Φₙ(x)`. -/
lemma x_nsmul {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℕ) {x' y' : F}
    {h' : W.toAffine.Nonsingular x' y'} (e : n • Point.some x y h = Point.some x' y' h') :
    x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  obtain ⟨c, hc, e2⟩ := local_formula h n
  rw [e, xP_some] at e2
  simp only [vP, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at e2
  obtain ⟨ea, eb⟩ := e2
  rw [ea]
  linear_combination -((W.Φ n).eval x) * eb

end Local

/-! ## Part E: `#E[n] = n²` over a separably closed field (O5) -/

section Torsion

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `n`-torsion subgroup `E[n]`. -/
def tors (W : WeierstrassCurve F) (n : ℕ) : AddSubgroup W.toAffine.Point where
  carrier := {P | n • P = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, nsmul_add] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, smul_neg] at *
    rw [ha, neg_zero]

lemma mem_tors {W : WeierstrassCurve F} {n : ℕ} {P : W.toAffine.Point} :
    P ∈ tors W n ↔ n • P = 0 := Iff.rfl

end Torsion

section Quadratic

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The quadratic in `y` cutting out the points with `x`-coordinate `a`. -/
noncomputable def yq (a : F) : F[X] :=
  X ^ 2 + C (W.a₁ * a + W.a₃) * X - C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆)

lemma equation_of_yq {a y : F} (h : (yq W a).eval y = 0) : W.toAffine.Equation a y := by
  rw [Affine.equation_iff]
  simp only [yq, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X] at h
  linear_combination h

lemma yq_degree (a : F) : (yq W a).degree = 2 := by
  unfold yq; compute_degree!

lemma exists_y_alg [IsAlgClosed F] (a : F) : ∃ y, W.toAffine.Equation a y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (yq W a) (by rw [yq_degree]; norm_num)
  exact ⟨y, equation_of_yq W hy⟩

lemma yq_separable (a : F) (hD : fx W a ≠ 0) : (yq W a).Separable := by
  have hd : derivative (yq W a) = 2 * X + C (W.a₁ * a + W.a₃) := by
    rw [yq, derivative_sub, derivative_C, sub_zero]
    simp [derivative_X_pow]
    try ring
  have hfx : fx W a = (W.a₁ * a + W.a₃) ^ 2 + 4 * (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆) := by
    simp only [fx, b₂, b₄, b₆]; ring
  have key : (2 * X + C (W.a₁ * a + W.a₃)) ^ 2 - 4 * yq W a = C (fx W a) := by
    rw [hfx]; simp only [yq, map_add, map_mul, map_pow, map_ofNat]; ring
  have hCD : C (fx W a)⁻¹ * C (fx W a) = 1 := by rw [← C_mul, inv_mul_cancel₀ hD, C_1]
  refine ⟨-4 * C (fx W a)⁻¹, C (fx W a)⁻¹ * (2 * X + C (W.a₁ * a + W.a₃)), ?_⟩
  rw [hd]
  linear_combination C (fx W a)⁻¹ * key + hCD

lemma exists_y_sep [IsSepClosed F] (a : F) (hD : fx W a ≠ 0) : ∃ y, W.toAffine.Equation a y := by
  obtain ⟨y, hy⟩ := IsSepClosed.exists_root (yq W a) (by rw [yq_degree]; norm_num)
    (yq_separable W a hD)
  exact ⟨y, equation_of_yq W hy⟩

lemma eval_Ψ₂Sq (a : F) : W.Ψ₂Sq.eval a = fx W a := by
  simp [Ψ₂Sq, fx]

lemma Ψ₂Sq_ne_zero_of_elliptic [W.IsElliptic] : W.Ψ₂Sq ≠ 0 := by
  intro h
  have h2 : W.b₂ = 0 := by
    have := congrArg (coeff · 2) h; simpa [Ψ₂Sq, coeff_X, coeff_C, coeff_X_pow] using this
  have h1 : 2 * W.b₄ = 0 := by
    have := congrArg (coeff · 1) h; simpa [Ψ₂Sq, coeff_X, coeff_C, coeff_X_pow] using this
  have h0 : W.b₆ = 0 := by
    have := congrArg (coeff · 0) h; simpa [Ψ₂Sq, coeff_X, coeff_C, coeff_X_pow] using this
  have hΔ := (W.isUnit_Δ).ne_zero
  apply hΔ
  simp only [Δ]
  linear_combination (-(W.b₂ * W.b₈) + 9 * W.b₄ * W.b₆) * h2 - 4 * W.b₄ ^ 2 * h1 +
    (-27 * W.b₆) * h0

end Quadratic

section Coprime

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

lemma coprime_alg [IsAlgClosed F] [W.IsElliptic] (n : ℕ) (a : F) :
    (W.Φ n).eval a ≠ 0 ∨ (W.ΨSq n).eval a ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_y_alg W a
  have h := (Affine.equation_iff_nonsingular).mp hy
  have hv := vP_ne_zero h n
  by_contra hc
  push_neg at hc
  apply hv
  simp only [vP, hc.1, hc.2, Prod.mk_zero_zero]

/-- Points with the same `x`-coordinate are equal up to sign. -/
lemma some_eq_or_neg {x y y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x y') :
    Point.some x y' h' = Point.some x y h ∨ Point.some x y' h' = -Point.some x y h := by
  rcases Y_eq_of_X_eq h'.1 h.1 rfl with e | e
  · subst e; exact Or.inl rfl
  · right; subst e; rw [Point.neg_some]

end Coprime

section GroupCount

/-- Counting a fibre pair of `[n]`: if `T = [n]⁻¹{R, -R}` has `2M` elements with `R ≠ -R`, then
`#ker [n] = M`. -/
lemma card_ker_of_fibres {G : Type*} [AddCommGroup G] (n : ℕ) (R : G) (hR : R ≠ -R)
    (T : Set G) (hT : ∀ P, P ∈ T ↔ n • P = R ∨ n • P = -R) {M : ℕ} (hTc : Nat.card T = 2 * M)
    (hM : 0 < M) : Nat.card {P : G // n • P = 0} = M := by
  classical
  have hTf : T.Finite := Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero (by omega))
  set A : Set G := {P | n • P = R}
  set A' : Set G := {P | n • P = -R}
  have hTA : T = A ∪ A' := by ext P; simp only [hT, Set.mem_union, Set.mem_setOf_eq, A, A']
  have hdis : Disjoint A A' := by
    rw [Set.disjoint_left]
    intro P hP hP'
    simp only [Set.mem_setOf_eq, A, A'] at hP hP'
    exact hR (hP.symm.trans hP')
  have hAf : A.Finite := hTf.subset (by rw [hTA]; exact Set.subset_union_left)
  have hA'f : A'.Finite := hTf.subset (by rw [hTA]; exact Set.subset_union_right)
  have hneg : A' = (fun P => -P) '' A := by
    ext P
    simp only [Set.mem_image, Set.mem_setOf_eq, A, A']
    constructor
    · intro h; exact ⟨-P, by rw [smul_neg, h, neg_neg], neg_neg P⟩
    · rintro ⟨Q, hQ, rfl⟩; rw [smul_neg, hQ]
  have hcA' : A'.ncard = A.ncard := by
    rw [hneg]; exact Set.ncard_image_of_injective _ neg_injective
  have hcT : T.ncard = 2 * A.ncard := by
    rw [hTA, Set.ncard_union_eq hdis hAf hA'f, hcA']; ring
  have hTn : T.ncard = 2 * M := by rw [← Nat.card_coe_set_eq]; exact hTc
  have hAc : A.ncard = M := by omega
  have hAne : A.Nonempty := by
    rw [← Set.ncard_pos hAf]; omega
  obtain ⟨P0, hP0⟩ := hAne
  simp only [Set.mem_setOf_eq, A] at hP0
  rw [← hAc, ← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun Q => ⟨P0 + Q.1, by simp only [Set.mem_setOf_eq, A, nsmul_add, hP0, Q.2, add_zero]⟩
      invFun := fun P => ⟨P.1 - P0, by
        have := P.2; simp only [Set.mem_setOf_eq, A] at this; rw [nsmul_sub, this, hP0, sub_self]⟩
      left_inv := fun Q => by ext; simp
      right_inv := fun P => by ext; simp }

end GroupCount

section SepClosed

variable {K : Type*} [Field K] [DecidableEq K] [IsSepClosed K] {W : WeierstrassCurve K}

lemma infinite_of_isSepClosed : Infinite K := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI : Finite K := h
  haveI : IsAlgClosed K := IsSepClosed.isAlgClosed_of_perfectField K
  exact not_finite K

lemma coprime_L [W.IsElliptic] (n : ℕ) (a : AlgebraicClosure K) :
    aeval a (W.Φ n) ≠ 0 ∨ aeval a (W.ΨSq n) ≠ 0 := by
  classical
  have := coprime_alg (W := W.map (algebraMap K (AlgebraicClosure K))) n a
  simpa only [map_Φ, map_ΨSq, eval_map_algebraMap] using this

/-- The Wronskian `Φₙ' ΨSqₙ - Φₙ ΨSqₙ'`. -/
noncomputable def wr (W : WeierstrassCurve K) (n : ℕ) : K[X] :=
  derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)

lemma coeff_wr (n : ℕ) (hn : 2 ≤ n) : (wr W n).coeff (2 * n ^ 2 - 2) = (n : K) ^ 2 := by
  have hN : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
  have dΦ := W.natDegree_Φ_le (n : ℤ)
  have cΦ := W.coeff_Φ (n : ℤ)
  have dΨ := W.natDegree_ΨSq_le (n : ℤ)
  have cΨ := W.coeff_ΨSq (n : ℤ)
  rw [hN] at dΦ cΦ dΨ cΨ
  have h4 : 4 ≤ n ^ 2 := by nlinarith
  have d1 : (derivative (W.Φ n)).natDegree ≤ n ^ 2 - 1 :=
    (natDegree_derivative_le _).trans (by omega)
  have d2 : (derivative (W.ΨSq n)).natDegree ≤ n ^ 2 - 2 :=
    (natDegree_derivative_le _).trans (by omega)
  have c1 : ((n ^ 2 - 1 : ℕ) : K) = (n : K) ^ 2 - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n ^ 2)]; push_cast; ring
  have c2 : ((n ^ 2 - 2 : ℕ) : K) = (n : K) ^ 2 - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n ^ 2)]; push_cast; ring
  have e1 := coeff_mul_add_eq_of_natDegree_le d1 dΨ
  have e2 := coeff_mul_add_eq_of_natDegree_le dΦ d2
  rw [wr, coeff_sub, show 2 * n ^ 2 - 2 = n ^ 2 - 1 + (n ^ 2 - 1) by omega, e1,
    show n ^ 2 - 1 + (n ^ 2 - 1) = n ^ 2 + (n ^ 2 - 2) by omega, e2, coeff_derivative,
    coeff_derivative, show n ^ 2 - 1 + 1 = n ^ 2 by omega, show n ^ 2 - 2 + 1 = n ^ 2 - 1 by omega,
    cΦ, cΨ, c1, c2]
  push_cast; ring

lemma wr_ne_zero (n : ℕ) (hn : 2 ≤ n) (hnK : (n : K) ≠ 0) : wr W n ≠ 0 := by
  intro h
  have := coeff_wr (W := W) n hn
  rw [h, coeff_zero] at this
  exact pow_ne_zero 2 hnK this.symm

/-- **O5.** Over a separably closed field, `#E[n] = n²` when `n ≠ 0` in the field. -/
theorem card_tors [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) :
    Nat.card (tors W n) = n ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact hnK Nat.cast_zero
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn
  · rw [one_pow, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨0⟩⟩
    have ha := a.2; have hb := b.2
    rw [mem_tors, one_smul] at ha hb
    rw [ha, hb]
  haveI := infinite_of_isSepClosed (K := K)
  have ιinj : Function.Injective (algebraMap K (AlgebraicClosure K)) := (algebraMap K _).injective
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = n ^ 2 := ⟨_, rfl⟩
  have hN : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
  let g : AlgebraicClosure K → AlgebraicClosure K := fun a => aeval a (W.Φ n) / aeval a (W.ΨSq n)
  have hΨ2 : W.Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero_of_elliptic W
  let B : Finset (AlgebraicClosure K) := ((wr W n).map (algebraMap K (AlgebraicClosure K))).roots.toFinset.image g ∪
    (W.Ψ₂Sq.map (algebraMap K (AlgebraicClosure K))).roots.toFinset.image g ∪ (W.Ψ₂Sq.map (algebraMap K (AlgebraicClosure K))).roots.toFinset
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (B.preimage (algebraMap K (AlgebraicClosure K)) ιinj.injOn)
  rw [Finset.mem_preimage] at ht
  have mem_root : ∀ (p : K[X]) (a : AlgebraicClosure K), p ≠ 0 → aeval a p = 0 → a ∈ (p.map (algebraMap K (AlgebraicClosure K))).roots.toFinset := by
    intro p a hp ha
    rw [Multiset.mem_toFinset, mem_roots_map hp, ← aeval_def]; exact ha
  -- the polynomial `f_t = Φₙ - t ΨSqₙ`
  set f := W.Φ n - C t * W.ΨSq n with hf
  have dΦ : (W.Φ n).natDegree = N := by rw [W.natDegree_Φ, hN, hNdef]
  have dΨ : (C t * W.ΨSq n).natDegree < N := by
    have := W.natDegree_ΨSq_le (n : ℤ); rw [hN] at this
    have h4 : 4 ≤ N := by rw [hNdef]; nlinarith
    exact (natDegree_C_mul_le _ _).trans_lt (by omega)
  have hmon : f.Monic := by
    have hΦm : (W.Φ n).Monic := by
      rw [Monic, leadingCoeff, dΦ, hNdef]; have := W.coeff_Φ (n : ℤ); rwa [hN] at this
    exact hΦm.sub_of_left (degree_lt_degree (by rw [dΦ]; exact dΨ))
  have hfdeg : f.natDegree = N := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt (by rw [dΦ]; exact dΨ), dΦ]
  have hf0 : f ≠ 0 := hmon.ne_zero
  -- separability of `f_t`
  have hsep : f.Separable := by
    rw [separable_def]
    refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := AlgebraicClosure K) _ _).mpr ?_
    intro a
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have hd : derivative f = derivative (W.Φ n) - C t * derivative (W.ΨSq n) := by
      rw [hf, derivative_sub, derivative_C_mul]
    rw [hd] at h2
    simp only [hf, map_sub, map_mul, aeval_C] at h1 h2
    have hΨa : aeval a (W.ΨSq n) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero] at h1
      rcases coprime_L (W := W) n a with h | h <;> exact h (by assumption)
    have hw : aeval a (wr W n) = 0 := by
      simp only [wr, map_sub, map_mul]
      linear_combination aeval a (W.ΨSq n) * h2 - aeval a (derivative (W.ΨSq n)) * h1
    have hga : g a = algebraMap K (AlgebraicClosure K) t := by
      simp only [g]; rw [div_eq_iff hΨa]; linear_combination h1
    apply ht
    rw [← hga]
    simp only [B, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl ⟨a, mem_root _ _ (wr_ne_zero n hn hnK) hw, rfl⟩)
  have hsplit : f.Splits := IsSepClosed.splits_of_separable f hsep
  set S := f.roots.toFinset with hS
  have hScard : S.card = N := by
    rw [hS, Multiset.toFinset_card_of_nodup (nodup_roots hsep), splits_iff_card_roots.mp hsplit,
      hfdeg]
  -- facts at the roots
  have root_facts : ∀ r ∈ S, (W.ΨSq n).eval r ≠ 0 ∧ fx W r ≠ 0 ∧
      (W.Φ n).eval r = t * (W.ΨSq n).eval r := by
    intro r hr
    rw [hS, Multiset.mem_toFinset, mem_roots hf0, IsRoot.def, hf, eval_sub, eval_mul, eval_C,
      sub_eq_zero] at hr
    have hΨr : (W.ΨSq n).eval r ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hr
      have := coprime_L (W := W) n (algebraMap K (AlgebraicClosure K) r)
      simp only [aeval_algebraMap_apply_eq_algebraMap_eval, hr, h0, map_zero, ne_eq,
        not_true_eq_false, or_self] at this
    refine ⟨hΨr, ?_, hr⟩
    intro hfx
    apply ht
    have hga : g (algebraMap K (AlgebraicClosure K) r) = algebraMap K (AlgebraicClosure K) t := by
      simp only [g, aeval_algebraMap_apply_eq_algebraMap_eval, hr, map_mul]
      exact mul_div_cancel_right₀ _ ((map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr hΨr)
    rw [← hga]
    simp only [B, Finset.mem_union, Finset.mem_image]
    refine Or.inl (Or.inr ⟨algebraMap K (AlgebraicClosure K) r, mem_root _ _ hΨ2 ?_, rfl⟩)
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, eval_Ψ₂Sq, hfx, map_zero]
  -- the base point `R₀` above `t`
  have hft : fx W t ≠ 0 := by
    intro h0
    apply ht
    simp only [B, Finset.mem_union]
    refine Or.inr (mem_root _ _ hΨ2 ?_)
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, eval_Ψ₂Sq, h0, map_zero]
  obtain ⟨y0, hy0⟩ := exists_y_sep W t hft
  have h0 : W.toAffine.Nonsingular t y0 := (Affine.equation_iff_nonsingular).mp hy0
  have hR0 : Point.some t y0 h0 ≠ -Point.some t y0 h0 := by
    intro e
    rw [Point.neg_some] at e
    simp only [Point.some.injEq, true_and] at e
    have h1 := (yψ_eq_zero_iff (W := W)).mpr e
    have h2 := yψ_sq (W := W) hy0
    rw [h1] at h2
    exact hft (by rw [← h2]; ring)
  -- the points above the roots
  choose yr hyr using fun r : S => exists_y_sep W r (root_facts r r.2).2.1
  have hNr : ∀ r : S, W.toAffine.Nonsingular r (yr r) :=
    fun r => (Affine.equation_iff_nonsingular).mp (hyr r)
  let Pt : S × Bool → W.toAffine.Point := fun p =>
    bif p.2 then Point.some _ _ (hNr p.1) else -Point.some _ _ (hNr p.1)
  have hPt_inj : Function.Injective Pt := by
    rintro ⟨r, b⟩ ⟨s, c⟩ e
    have hr2 := (root_facts r r.2).2.1
    cases b <;> cases c <;> simp only [Pt, cond_true, cond_false, neg_inj,
      Point.neg_some, Point.some.injEq] at e
    · obtain ⟨e1, -⟩ := e; rw [Subtype.ext e1]
    · exfalso
      obtain ⟨e1, e2⟩ := e
      have e1' : r = s := Subtype.ext e1
      subst e1'
      have h1 := (yψ_eq_zero_iff (W := W)).mpr e2.symm
      have h2 := yψ_sq (W := W) (hyr r)
      rw [h1] at h2
      exact hr2 (by rw [← h2]; ring)
    · exfalso
      obtain ⟨e1, e2⟩ := e
      have e1' : r = s := Subtype.ext e1
      subst e1'
      have h1 := (yψ_eq_zero_iff (W := W)).mpr e2
      have h2 := yψ_sq (W := W) (hyr r)
      rw [h1] at h2
      exact hr2 (by rw [← h2]; ring)
    · obtain ⟨e1, -⟩ := e; rw [Subtype.ext e1]
  -- `nP = ±R₀` exactly for the points above the roots
  have fibre : ∀ P : W.toAffine.Point, (n • P = Point.some t y0 h0 ∨ n • P = -Point.some t y0 h0) ↔ P ∈ Set.range Pt := by
    intro P
    constructor
    · intro hP
      rcases P with _ | ⟨r, y, hry⟩
      · exfalso
        rw [← Point.zero_def, nsmul_zero] at hP
        rcases hP with e | e
        · exact Point.some_ne_zero h0 e.symm
        · rw [Point.neg_some] at e; exact Point.some_ne_zero _ e.symm
      have hrt : t * (W.ΨSq n).eval r = (W.Φ n).eval r := by
        rcases hP with e | e
        · exact x_nsmul hry n e
        · rw [Point.neg_some] at e; exact x_nsmul hry n e
      have hrS : r ∈ S := by
        rw [hS, Multiset.mem_toFinset, mem_roots hf0, IsRoot.def, hf, eval_sub, eval_mul, eval_C,
          hrt, sub_self]
      rcases some_eq_or_neg (hNr ⟨r, hrS⟩) hry with e | e
      · exact ⟨(⟨r, hrS⟩, true), by simp only [Pt, cond_true]; exact e.symm⟩
      · exact ⟨(⟨r, hrS⟩, false), by simp only [Pt, cond_false]; exact e.symm⟩
    · rintro ⟨⟨r, b⟩, rfl⟩
      obtain ⟨hΨr, -, hΦr⟩ := root_facts r r.2
      have key : n • Point.some _ _ (hNr r) = Point.some t y0 h0 ∨ n • Point.some _ _ (hNr r) = -Point.some t y0 h0 := by
        have hne : n • Point.some _ _ (hNr r) ≠ 0 := by
          rw [Ne, nsmul_eq_zero_iff]; exact hΨr
        rcases hQ : n • Point.some _ _ (hNr r) with _ | ⟨x', y', h'⟩
        · exact absurd hQ hne
        have hx := x_nsmul (hNr r) n hQ
        rw [hΦr] at hx
        have hx' : x' = t := mul_right_cancel₀ hΨr hx
        subst hx'
        exact some_eq_or_neg h0 h'
      cases b
      · simp only [Pt, cond_false, smul_neg, neg_inj]
        rcases key with e | e
        · right; rw [e]
        · left; rw [e, neg_neg]
      · simp only [Pt, cond_true]; exact key
  have hTc : Nat.card (Set.range Pt) = 2 * N := by
    rw [Nat.card_range_of_injective hPt_inj, Nat.card_prod, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_bool, hScard]; ring
  have := card_ker_of_fibres n (Point.some t y0 h0) hR0 (Set.range Pt) (fun P => (fibre P).symm) hTc
    (by rw [hNdef]; exact pow_pos (by omega) 2)
  rw [← hNdef, ← this]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun P => mem_tors))

end SepClosed


/-! ## Part F: `E[n] ≃+ (ℤ/n)²` (O6) -/

section GroupStructure

variable {G : Type*} [AddCommGroup G]

lemma card_sub_univ {d : ℕ} (h : ∀ g : G, d • g = 0) :
    Nat.card {g : G // d • g = 0} = Nat.card G :=
  Nat.card_congr (Equiv.subtypeUnivEquiv h)

/-- **O6, group part.** A finite abelian group killed by `n > 0` that has exactly `d²` elements
killed by `d` for every `d ∣ n` is isomorphic to `(ℤ/n)²`.
Elementary proof: the exponent is `n`; take `P` of order `n`, `H = ⟨P⟩`; the quotient `G ⧸ H` has
`n` elements and exponent `n` (for `e' = exp (G ⧸ H)`, `e' • G` is a cyclic subgroup of `H` with
`n² / e'²` elements killed by `n / e'`); lift an element of order `n` of `G ⧸ H` to `Q`; then
`(a, b) ↦ a • P + b • Q` is injective, hence bijective by counting. -/
theorem nonempty_equiv_zmod_sq [Finite G] (n : ℕ) (hn : 0 < n) (hG : ∀ g : G, n • g = 0)
    (hcard : ∀ d, d ∣ n → Nat.card {g : G // d • g = 0} = d ^ 2) :
    Nonempty (G ≃+ ZMod n × ZMod n) := by
  classical
  have hGc : Nat.card G = n ^ 2 := by rw [← card_sub_univ hG, hcard n dvd_rfl]
  -- the exponent of `G` is `n`
  have hexp : AddMonoid.exponent G = n := by
    have hdvd : AddMonoid.exponent G ∣ n := AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hG
    have h1 := hcard _ hdvd
    rw [card_sub_univ (fun g => AddMonoid.exponent_nsmul_eq_zero g), hGc] at h1
    exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1).symm
  obtain ⟨P, hP⟩ :=
    AddMonoid.exists_addOrderOf_eq_exponent (AddMonoid.ExponentExists.of_finite (G := G))
  rw [hexp] at hP
  let H : AddSubgroup G := AddSubgroup.zmultiples P
  have hHc : Nat.card H = n := by rw [Nat.card_zmultiples, hP]
  have hQc : Nat.card (G ⧸ H) = n := by
    have := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
    rw [hGc, hHc, sq] at this
    exact (Nat.eq_of_mul_eq_mul_right hn this).symm
  -- the exponent of the quotient is `n`
  have hexpQ : AddMonoid.exponent (G ⧸ H) = n := by
    set e' := AddMonoid.exponent (G ⧸ H) with he'
    have he'dvd : e' ∣ n := AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero (fun q => by
      induction q using QuotientAddGroup.induction_on with
      | H g => rw [← QuotientAddGroup.mk_nsmul, hG, QuotientAddGroup.mk_zero])
    have he'pos : 0 < e' := Nat.pos_of_ne_zero AddMonoid.exponent_ne_zero_of_finite
    have hmemH : ∀ g : G, e' • g ∈ H := fun g => by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul]
      exact AddMonoid.exponent_nsmul_eq_zero _
    let f : G →+ G := nsmulAddMonoidHom e'
    have hRle : f.range ≤ H := by
      rintro _ ⟨g, rfl⟩
      exact hmemH g
    haveI : IsAddCyclic f.range := AddSubgroup.isAddCyclic_of_le hRle
    have hker : Nat.card f.ker = e' ^ 2 := by
      rw [← hcard e' he'dvd]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun g => by
        simp [f, AddMonoidHom.mem_ker]))
    have hrange : Nat.card f.range * e' ^ 2 = n ^ 2 := by
      rw [← hker, ← hGc, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
      exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker).symm
    have hRdvd : Nat.card f.range ∣ n / e' := by
      rw [← IsAddCyclic.exponent_eq_card]
      refine AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero (fun r => ?_)
      obtain ⟨_, g, rfl⟩ := r
      apply Subtype.ext
      change (n / e') • (e' • g) = 0
      rw [smul_smul, Nat.div_mul_cancel he'dvd, hG]
    have hpos : 0 < n / e' := Nat.div_pos (Nat.le_of_dvd hn he'dvd) he'pos
    have hle := Nat.le_of_dvd hpos hRdvd
    have hne : n / e' * e' = n := Nat.div_mul_cancel he'dvd
    have key : n * n ≤ n * e' := by
      calc n * n = n ^ 2 := (sq n).symm
        _ = Nat.card f.range * e' ^ 2 := hrange.symm
        _ ≤ n / e' * e' ^ 2 := Nat.mul_le_mul_right _ hle
        _ = n / e' * e' * e' := by ring
        _ = n * e' := by rw [hne]
    exact Nat.le_antisymm (Nat.le_of_dvd hn he'dvd) (Nat.le_of_mul_le_mul_left key hn)
  obtain ⟨Q', hQ'⟩ := AddMonoid.exists_addOrderOf_eq_exponent
    (AddMonoid.ExponentExists.of_finite (G := G ⧸ H))
  rw [hexpQ] at hQ'
  obtain ⟨Q, rfl⟩ := QuotientAddGroup.mk_surjective Q'
  have hPn : zmultiplesHom G P (n : ℤ) = 0 := by
    rw [zmultiplesHom_apply, natCast_zsmul, hG]
  have hQn : zmultiplesHom G Q (n : ℤ) = 0 := by
    rw [zmultiplesHom_apply, natCast_zsmul, hG]
  let φ : ZMod n × ZMod n →+ G :=
    (ZMod.lift n ⟨zmultiplesHom G P, hPn⟩).coprod (ZMod.lift n ⟨zmultiplesHom G Q, hQn⟩)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨l, rfl⟩ := ZMod.intCast_surjective b
    simp only [φ, AddMonoidHom.coprod_apply, ZMod.lift_coe, zmultiplesHom_apply] at hab
    have hl : (n : ℤ) ∣ l := by
      rw [← hQ', addOrderOf_dvd_iff_zsmul_eq_zero, ← QuotientAddGroup.mk_zsmul,
        QuotientAddGroup.eq_zero_iff]
      have : l • Q = -(k • P) := eq_neg_of_add_eq_zero_right hab
      rw [this]
      exact H.neg_mem (H.zsmul_mem (AddSubgroup.mem_zmultiples P) k)
    obtain ⟨c, rfl⟩ := hl
    have hlQ : ((n : ℤ) * c) • Q = 0 := by
      rw [mul_comm, ← smul_smul, natCast_zsmul, hG, smul_zero]
    rw [hlQ, add_zero] at hab
    have hk : (n : ℤ) ∣ k := by
      rw [← hP, addOrderOf_dvd_iff_zsmul_eq_zero]
      exact hab
    simp only [Prod.mk_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨hk, dvd_mul_right _ _⟩
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hGc, Nat.card_prod, Nat.card_zmod, sq])
  exact ⟨(AddEquiv.ofBijective φ hbij).symm⟩

end GroupStructure

section TorsStructure

variable {F : Type*} [Field F] [DecidableEq F]

lemma tors_mono {W : WeierstrassCurve F} {d n : ℕ} (h : d ∣ n) : tors W d ≤ tors W n := by
  intro P hP
  rw [mem_tors] at hP ⊢
  obtain ⟨c, rfl⟩ := h
  rw [mul_comm, ← smul_smul, hP, smul_zero]

lemma card_sub_tors {W : WeierstrassCurve F} {d n : ℕ} (h : d ∣ n) :
    Nat.card {g : tors W n // d • g = 0} = Nat.card (tors W d) :=
  Nat.card_congr
    { toFun := fun g => ⟨g.1.1, by
        have h2 := congrArg Subtype.val g.2
        rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at h2
        exact mem_tors.mpr h2⟩
      invFun := fun P => ⟨⟨P.1, tors_mono h P.2⟩, by
        apply Subtype.ext
        rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
        exact mem_tors.mp P.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {K : Type*} [Field K] [DecidableEq K] [IsSepClosed K] {W : WeierstrassCurve K}

lemma finite_tors [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) : Finite (tors W n) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hnK Nat.cast_zero
  exact Nat.finite_of_card_ne_zero (by rw [card_tors n hnK]; exact pow_ne_zero 2 hn0)

/-- **O6.** Over a separably closed field, `E[n] ≃+ (ℤ/n)²` when `n ≠ 0` in the field. -/
theorem tors_equiv [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) :
    Nonempty (tors W n ≃+ ZMod n × ZMod n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hnK Nat.cast_zero)
  haveI := finite_tors (W := W) n hnK
  refine nonempty_equiv_zmod_sq n hn0 (fun g => Subtype.ext ?_) (fun d hd => ?_)
  · rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
    exact mem_tors.mp g.2
  · have hdK : (d : K) ≠ 0 := by
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.cast_mul] at hnK
      exact left_ne_zero_of_mul hnK
    rw [card_sub_tors hd, card_tors d hdK]

end TorsStructure

/-! ## Part G: torsion over a separable closure (O7) -/

section SepCoords

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

lemma natCast_ne_zero_of_algebra (L : Type*) [Field L] [Algebra K L] {n : ℕ} (hnK : (n : K) ≠ 0) :
    (n : L) ≠ 0 := by
  rw [← map_natCast (algebraMap K L)]
  exact (_root_.map_ne_zero _).mpr hnK

instance isElliptic_baseChange (L : Type*) [Field L] [Algebra K L] [W.IsElliptic] :
    (W.baseChange L).IsElliptic :=
  inferInstanceAs (W.map (algebraMap K L)).IsElliptic

variable (L : Type*) [Field L] [Algebra K L] [IsSepClosed L] [DecidableEq L]

/-- `#E(L)[n] = n²` for the base change to any separably closed extension `L`. -/
theorem card_tors_baseChange [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) :
    Nat.card (tors (W.baseChange L) n) = n ^ 2 :=
  card_tors n (natCast_ne_zero_of_algebra L hnK)

/-- `E(L)[n] ≃+ (ℤ/n)²` for the base change to any separably closed extension `L`. -/
theorem tors_equiv_baseChange [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) :
    Nonempty (tors (W.baseChange L) n ≃+ ZMod n × ZMod n) :=
  tors_equiv n (natCast_ne_zero_of_algebra L hnK)

/-- **O7.** If `L ⊇ K` is separably closed and `n ≠ 0` in `K`, every `n`-torsion point of `E(L)`
has both coordinates separable over `K` (they lie in the separable closure of `K` in `L`).
Proof: `E(K^sep)[n] → E(L)[n]` is injective and both sides have `n²` points. -/
theorem tors_coords_separable [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y)
    (hP : (Point.some x y h : (W.baseChange L).toAffine.Point) ∈ tors (W.baseChange L) n) :
    IsSeparable K x ∧ IsSeparable K y := by
  classical
  let S := separableClosure K L
  haveI : IsSepClosed S := IsSepClosure.sep_closed K
  let φ := Point.map (W' := W.toAffine) S.val
  let g : tors (W.baseChange S) n → tors (W.baseChange L) n := fun Q =>
    ⟨φ Q.1, by
      rw [mem_tors, ← map_nsmul, mem_tors.mp Q.2]
      exact map_zero φ⟩
  have hginj : Function.Injective g := by
    intro Q₁ Q₂ hQ
    exact Subtype.ext (Point.map_injective (W' := W.toAffine) S.val (congrArg Subtype.val hQ))
  haveI : Finite (tors (W.baseChange L) n) := finite_tors n (natCast_ne_zero_of_algebra L hnK)
  have hgbij : Function.Bijective g := hginj.bijective_of_nat_card_le (by
    rw [card_tors_baseChange W L n hnK, card_tors_baseChange W S n hnK])
  obtain ⟨⟨Q, hQm⟩, hQ⟩ := hgbij.2 ⟨Point.some x y h, hP⟩
  have hQ' := congrArg Subtype.val hQ
  rcases Q with _ | ⟨x', y', h'⟩
  · exact absurd hQ'.symm (Point.some_ne_zero h)
  · change Point.some _ _ _ = Point.some x y h at hQ'
    rw [Point.some.injEq] at hQ'
    obtain ⟨hx, hy⟩ := hQ'
    refine ⟨?_, ?_⟩
    · rw [← mem_separableClosure_iff, ← hx]
      exact x'.2
    · rw [← mem_separableClosure_iff, ← hy]
      exact y'.2

/-- Every `n`-torsion point over `L` comes from a point over the separable closure of `K` in `L`:
the base change map `E(K^sep)[n] → E(L)[n]` is bijective. -/
theorem tors_map_bijective [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) [DecidableEq (separableClosure K L)] :
    Function.Bijective (fun Q : tors (W.baseChange (separableClosure K L)) n =>
      (⟨Point.map (W' := W.toAffine) (separableClosure K L).val Q.1, by
        rw [mem_tors, ← map_nsmul, mem_tors.mp Q.2]
        exact map_zero _⟩ : tors (W.baseChange L) n)) := by
  haveI : IsSepClosed (separableClosure K L) := IsSepClosure.sep_closed K
  haveI : Finite (tors (W.baseChange L) n) := finite_tors n (natCast_ne_zero_of_algebra L hnK)
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro Q₁ Q₂ hQ
    exact Subtype.ext (Point.map_injective (W' := W.toAffine) _ (congrArg Subtype.val hQ))
  · rw [card_tors_baseChange W L n hnK, card_tors_baseChange W _ n hnK]

end SepCoords

section SepClosureK

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

open scoped Classical in
/-- `#E(K^sep)[n] = n²` for `K^sep = SeparableClosure K`. -/
theorem card_tors_sepClosure [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) :
    Nat.card (tors (W.baseChange (SeparableClosure K)) n) = n ^ 2 :=
  card_tors_baseChange W _ n hnK

open scoped Classical in
/-- `E(K^sep)[n] ≃+ (ℤ/n)²` for `K^sep = SeparableClosure K`. -/
theorem tors_equiv_sepClosure [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0) :
    Nonempty (tors (W.baseChange (SeparableClosure K)) n ≃+ ZMod n × ZMod n) :=
  tors_equiv_baseChange W _ n hnK

open scoped Classical in
/-- `n`-torsion points over an algebraic closure have coordinates in `K^sep`. -/
theorem tors_coords_separable_algClosure [W.IsElliptic] (n : ℕ) (hnK : (n : K) ≠ 0)
    {x y : AlgebraicClosure K} (h : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hP : (Point.some x y h : (W.baseChange (AlgebraicClosure K)).toAffine.Point) ∈
      tors (W.baseChange (AlgebraicClosure K)) n) :
    IsSeparable K x ∧ IsSeparable K y :=
  tors_coords_separable W _ n hnK h hP

end SepClosureK

end RPLib.Torsion


