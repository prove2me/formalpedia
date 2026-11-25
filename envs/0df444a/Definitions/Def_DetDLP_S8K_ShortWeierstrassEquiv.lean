-- Prove2me | Definitions.Def_DetDLP_S8K_ShortWeierstrassEquiv
-- name    : DetDLP_S8K_ShortWeierstrassEquiv
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:18:26.638337+00:00
-- url     : https://prove2.me/theorems/c686983d-c96f-4249-bd84-2262233a211f
-- title:
--   Short Weierstrass equivalence for p > 3
-- statement:
--   Defines an additive equivalence between the affine points of a general elliptic Weierstrass curve over ZMod p and its short Weierstrass model, including coordinate maps X and Y and a proof that six is nonzero for primes p > 3.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace DetDLP.S8K.SWEquiv
open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] (E : WeierstrassCurve F)

def short : WeierstrassCurve F := ⟨0, 0, 0, -27 * E.c₄, -54 * E.c₆⟩
def X (x : F) := 36 * x + 3 * E.b₂
def Y (x y : F) := 108 * (2 * y + E.a₁ * x + E.a₃)

theorem disc : (short E).Δ = 6 ^ 12 * E.Δ := by
  simp only [short, Δ, b₈, c₄, c₆, b₂, b₄, b₆]
  ring

theorem elliptic [E.IsElliptic] (h6 : (6 : F) ≠ 0) : (short E).IsElliptic :=
  ⟨by rw [disc]; exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 12 h6)).mul E.isUnit_Δ⟩

theorem equation (h6 : (6 : F) ≠ 0) (x y : F) :
    (short E).toAffine.Equation (X E x) (Y E x y) ↔ E.toAffine.Equation x y := by
  rw [equation_iff', equation_iff']
  have h := pow_ne_zero 6 h6
  convert (mul_eq_zero.trans (or_iff_right h) : (6:F)^6 * _ = 0 ↔ _) using 2
  simp only [short, X, Y, c₄, c₆, b₂, b₄, b₆, WeierstrassCurve.toAffine]
  ring

variable [E.IsElliptic]

def point (h6 : (6:F) ≠ 0) : E.toAffine.Point → (short E).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (X E x) (Y E x y) (by
      letI := elliptic E h6
      exact equation_iff_nonsingular.mp ((equation E h6 x y).2 h.1))

variable (h6 : (6:F) ≠ 0)

include h6 in
private theorem nz36 : (36:F) ≠ 0 := by
  convert pow_ne_zero 2 h6 using 1 <;> norm_num
include h6 in
private theorem nz216 : (216:F) ≠ 0 := by
  convert pow_ne_zero 3 h6 using 1 <;> norm_num

include h6 in
private theorem X_inj (x z : F) : X E x = X E z ↔ x = z := by
  simp only [X, add_left_inj, mul_right_inj' (nz36 h6)]

include h6 in
private theorem Y_inj (x y w : F) : Y E x y = Y E x w ↔ y = w := by
  have H (v : F) : Y E x v = 216 * v + 108*(E.a₁*x+E.a₃) := by unfold Y; ring
  simp only [H, add_left_inj, mul_right_inj' (nz216 h6)]

private theorem Y_neg (x y : F) :
    Y E x (E.toAffine.negY x y) = (short E).toAffine.negY (X E x) (Y E x y) := by
  simp only [Y, negY, short, WeierstrassCurve.toAffine]; ring

private theorem point_bij : Function.Bijective (point E h6) := by
  constructor
  · intro P Q h
    cases P <;> cases Q <;> simp only [point, Point.some.injEq, reduceCtorEq] at h ⊢
    · obtain ⟨hx, hy⟩ := h
      obtain rfl := (X_inj E h6 ..).1 hx
      exact ⟨rfl, (Y_inj E h6 ..).1 hy⟩
  · rintro (_ | ⟨v, w, hw⟩)
    · exact ⟨.zero, rfl⟩
    · let x := (v - 3 * E.b₂) / 36
      let y := (w - 108 * (E.a₁*x+E.a₃)) / 216
      have hx : X E x = v := by unfold X x; field_simp [nz36 h6]; ring
      have hy : Y E x y = w := by unfold Y y; field_simp [nz216 h6]; ring
      have hn : E.toAffine.Nonsingular x y := equation_iff_nonsingular.mp <|
        (equation E h6 x y).mp (hx ▸ hy ▸ hw.1)
      exact ⟨.some x y hn, by simp only [point, Point.some.injEq, hx, hy, and_self]⟩

variable [DecidableEq F]

include h6 in
private theorem slope_transport {x z y w : F} (hp : E.toAffine.Nonsingular x y)
    (hq : E.toAffine.Nonsingular z w) (hn : ¬(x = z ∧ y = E.toAffine.negY z w)) :
    (short E).toAffine.slope (X E x) (X E z) (Y E x y) (Y E z w) =
      6 * E.toAffine.slope x z y w + 3 * E.a₁ := by
  by_cases hx : x = z
  · subst z
    have hn' : y ≠ E.toAffine.negY x w := fun h => hn ⟨rfl,h⟩
    obtain rfl := Y_eq_of_Y_ne hp.1 hq.1 rfl hn'
    have h' : Y E x y ≠ (short E).toAffine.negY (X E x) (Y E x y) := by
      rw [← Y_neg]; exact fun h => hn' ((Y_inj E h6 ..).1 h)
    rw [slope_of_Y_ne rfl h', slope_of_Y_ne rfl hn']
    have ho := sub_ne_zero.mpr hn'
    have ht := sub_ne_zero.mpr h'
    field_simp [ho, ht]
    simp only [short, X, Y, negY, c₄, b₂, b₄, WeierstrassCurve.toAffine]; ring
  · have hx' := fun h => hx ((X_inj E h6 ..).1 h)
    rw [slope_of_X_ne hx', slope_of_X_ne hx]
    field_simp [sub_ne_zero.mpr hx', sub_ne_zero.mpr hx]
    simp only [X, Y]; ring

private theorem addX_transport (x z m : F) :
    X E (E.toAffine.addX x z m) = (short E).toAffine.addX (X E x) (X E z) (6*m+3*E.a₁) := by
  simp only [X, addX, short, b₂, WeierstrassCurve.toAffine]; ring

private theorem addY_transport (x z y m : F) :
    Y E (E.toAffine.addX x z m) (E.toAffine.addY x z y m) =
      (short E).toAffine.addY (X E x) (X E z) (Y E x y) (6*m+3*E.a₁) := by
  simp only [X, Y, addX, addY, negAddY, negY, short, b₂, WeierstrassCurve.toAffine]; ring

theorem additive (P Q : E.toAffine.Point) : point E h6 (P+Q) = point E h6 P + point E h6 Q := by
  cases P with
  | zero => rfl
  | some x y hp =>
    cases Q with
    | zero => rfl
    | some z w hq =>
      have H : (X E x = X E z ∧ Y E x y = (short E).toAffine.negY (X E z) (Y E z w)) ↔
          (x = z ∧ y = E.toAffine.negY z w) := by
        rw [X_inj E h6]; refine and_congr_right fun hx => ?_
        subst z; rw [← Y_neg, Y_inj E h6]
      by_cases hn : x = z ∧ y = E.toAffine.negY z w
      · obtain ⟨ha,hb⟩ := H.2 hn
        rw [Point.add_of_Y_eq hn.1 hn.2]; simp only [point, Point.add_of_Y_eq ha hb]; rfl
      · rw [Point.add_some hn]; simp only [point, Point.add_some (mt H.1 hn), Point.some.injEq,
          slope_transport E h6 hp hq hn]
        exact ⟨addX_transport E .., addY_transport E ..⟩

noncomputable def equiv : E.toAffine.Point ≃+ (short E).toAffine.Point :=
  AddEquiv.ofBijective (⟨⟨point E h6, rfl⟩, additive E h6⟩ : E.toAffine.Point →+ (short E).toAffine.Point)
    (point_bij E h6)

variable {p : ℕ} [Fact p.Prime]

theorem six_ne_zero (hp : 3 < p) : (6 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp h
  have hbound : p ≤ 6 := Nat.le_of_dvd (by decide) hd
  have hprime : Nat.Prime p := Fact.out
  interval_cases p <;> norm_num at *

end DetDLP.S8K.SWEquiv


