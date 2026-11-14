-- Prove2me | Definitions.Def_RPLib_S2_TateNFB
-- name    : RPLib_S2_TateNFB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:47:41.791433+00:00
-- url     : https://prove2.me/theorems/3abefcb9-e4ff-4706-8fef-170c2eb0e42a
-- title:
--   The moduli bijection for $Y_1(M)$, $M \ge 4$
-- statement:
--   Over a field $F$ and $M \ge 4$: the set $Y_1(M)(F)$ of $(b,c)$ with $\Delta(b,c) \neq 0$ and $(0,0)$ of exact order $M$ on $E(b,c)$ is in bijection with isomorphism classes of pairs $(E, P)$ with $P \in E(F)$ of exact order $M$; explicit order polynomials for $M = 4,5,6,7$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Husemoller, Elliptic Curves, 2nd ed., GTM 111, Springer 2004, Section 4.4, doi:10.1007/b97292; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 8.2

import Mathlib
import Definitions.Def_RPLib_S2_TateNFA

/-!
# Tate normal form, part B: exact order, `Y₁(M)`, the moduli bijection, explicit order polynomials

Library unit S2-TateNF of the Ramanujan-Petersson project. Over a field `F`:
* `HasExactOrder M b c`: `(0,0)` has exact order `M` on `E(b,c)` (group law);
* `Y1 F M = {(b,c) : Δ(b,c) ≠ 0, (0,0) of exact order M}`;
* `PairM F M`: Weierstrass curves over `F` with `Δ ≠ 0` and a point of exact order `M`, and
  `PairClass F M`: their isomorphism classes (isomorphisms of Weierstrass models = changes of variables);
* `y1Equiv (hM : 4 ≤ M) : Y1 F M ≃ PairClass F M`, and `card_Y1` for finite fields;
* `tateN`, `tateD`: numerator/denominator of `x(n • (0,0))` (polynomials in `b, c`), `tateF M`:
  the order-`M` polynomial, and `hasExactOrder_iff_tateF`: for `M ≥ 4`, `(0,0)` has exact order `M`
  iff `b ≠ 0`, `N_j(b,c) ≠ 0` for `2 ≤ j ≤ M/2`, and `F_M(b,c) = 0`. Explicit cases `M = 4,5,6,7`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.TateNF

/-! ## The `x`-coordinate sequence as polynomials in `b, c` -/

section Seq

variable {R : Type*} [CommRing R]

/-- One step `(N_{n-1}, D_{n-1}), (N_n, D_n) ↦ (N_{n+1}, D_{n+1})` of the chord recursion
`x_{n+1} = b (b - (1 - c) x_n) / x_n² - x_{n-1}`. -/
def tateStep (b c : R) (q p : R × R) : R × R :=
  (b * (b * p.2 - (1 - c) * p.1) * p.2 * q.2 - q.1 * p.1 ^ 2, p.1 ^ 2 * q.2)

/-- `(N_n, D_n)` with `x(n • (0,0)) = N_n / D_n` on `E(b,c)` (index `0` is a dummy). -/
def tateND (b c : R) : ℕ → R × R
  | 0 => (0, 1)
  | 1 => (0, 1)
  | 2 => (b, 1)
  | n + 3 => tateStep b c (tateND b c (n + 1)) (tateND b c (n + 2))

/-- Numerator `N_n` of `x(n • (0,0))`. -/
def tateN (b c : R) (n : ℕ) : R := (tateND b c n).1

/-- Denominator `D_n` of `x(n • (0,0))`. -/
def tateD (b c : R) (n : ℕ) : R := (tateND b c n).2

@[simp] lemma tateN_one (b c : R) : tateN b c 1 = 0 := rfl
@[simp] lemma tateD_one (b c : R) : tateD b c 1 = 1 := rfl
@[simp] lemma tateN_two (b c : R) : tateN b c 2 = b := rfl
@[simp] lemma tateD_two (b c : R) : tateD b c 2 = 1 := rfl

lemma tateN_add_three (b c : R) (n : ℕ) : tateN b c (n + 3) =
    b * (b * tateD b c (n + 2) - (1 - c) * tateN b c (n + 2)) * tateD b c (n + 2) *
      tateD b c (n + 1) - tateN b c (n + 1) * tateN b c (n + 2) ^ 2 := rfl

lemma tateD_add_three (b c : R) (n : ℕ) :
    tateD b c (n + 3) = tateN b c (n + 2) ^ 2 * tateD b c (n + 1) := rfl

lemma tateN_three (b c : R) : tateN b c 3 = b ^ 2 * c := by
  rw [show tateN b c 3 = b * (b * 1 - (1 - c) * b) * 1 * 1 - 0 * b ^ 2 from rfl]; ring

lemma tateD_three (b c : R) : tateD b c 3 = b ^ 2 := by
  rw [show tateD b c 3 = b ^ 2 * 1 from rfl]; ring

lemma tateN_four (b c : R) : tateN b c 4 = b ^ 5 * (b - c) := by
  rw [show (4 : ℕ) = 1 + 3 from rfl, tateN_add_three]
  simp only [Nat.reduceAdd, tateN_three, tateD_three, tateN_two, tateD_two]; ring

lemma tateD_four (b c : R) : tateD b c 4 = b ^ 4 * c ^ 2 := by
  rw [show (4 : ℕ) = 1 + 3 from rfl, tateD_add_three]
  simp only [Nat.reduceAdd, tateN_three, tateD_two]; ring

lemma map_tateN_tateD {S G : Type*} [CommRing S] [FunLike G R S] [RingHomClass G R S] (f : G)
    (b c : R) (n : ℕ) :
    f (tateN b c n) = tateN (f b) (f c) n ∧ f (tateD b c n) = tateD (f b) (f c) n := by
  have key : ∀ n, (f (tateN b c (n + 1)) = tateN (f b) (f c) (n + 1) ∧
      f (tateD b c (n + 1)) = tateD (f b) (f c) (n + 1)) ∧
      (f (tateN b c (n + 2)) = tateN (f b) (f c) (n + 2) ∧
      f (tateD b c (n + 2)) = tateD (f b) (f c) (n + 2)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ih
      show f (tateN b c (n + 3)) = tateN (f b) (f c) (n + 3) ∧
        f (tateD b c (n + 3)) = tateD (f b) (f c) (n + 3)
      rw [tateN_add_three, tateN_add_three, tateD_add_three, tateD_add_three]
      simp only [map_sub, map_mul, map_pow, map_one, h1, h2, h3, h4, and_self]
  rcases n with _ | n
  · simp [tateN, tateD, tateND]
  · exact (key n).1

lemma map_tateN {S G : Type*} [CommRing S] [FunLike G R S] [RingHomClass G R S] (f : G)
    (b c : R) (n : ℕ) : f (tateN b c n) = tateN (f b) (f c) n := (map_tateN_tateD f b c n).1

lemma map_tateD {S G : Type*} [CommRing S] [FunLike G R S] [RingHomClass G R S] (f : G)
    (b c : R) (n : ℕ) : f (tateD b c n) = tateD (f b) (f c) n := (map_tateN_tateD f b c n).2

/-- The order-`M` polynomial: for `M = 2m+1`, `N_{m+1} D_m - N_m D_{m+1}` (`x(mP) = x((m+1)P)`);
for `M = 2m`, `2 N_m² N_{m+1} + b(1-c) N_m D_m D_{m+1} - b² D_m² D_{m+1}` (`mP = -mP`). -/
def tateF (b c : R) (M : ℕ) : R :=
  if M % 2 = 1 then
    tateN b c (M / 2 + 1) * tateD b c (M / 2) - tateN b c (M / 2) * tateD b c (M / 2 + 1)
  else
    2 * tateN b c (M / 2) ^ 2 * tateN b c (M / 2 + 1) +
      b * (1 - c) * tateN b c (M / 2) * tateD b c (M / 2) * tateD b c (M / 2 + 1) -
      b ^ 2 * tateD b c (M / 2) ^ 2 * tateD b c (M / 2 + 1)

lemma tateF_even (b c : R) (m : ℕ) : tateF b c (2 * m) =
    2 * tateN b c m ^ 2 * tateN b c (m + 1) + b * (1 - c) * tateN b c m * tateD b c m *
      tateD b c (m + 1) - b ^ 2 * tateD b c m ^ 2 * tateD b c (m + 1) := by
  rw [tateF, if_neg (show ¬(2 * m % 2 = 1) by omega), show 2 * m / 2 = m by omega]

lemma tateF_odd (b c : R) (m : ℕ) : tateF b c (2 * m + 1) =
    tateN b c (m + 1) * tateD b c m - tateN b c m * tateD b c (m + 1) := by
  rw [tateF, if_pos (show (2 * m + 1) % 2 = 1 by omega), show (2 * m + 1) / 2 = m by omega]

lemma map_tateF {S G : Type*} [CommRing S] [FunLike G R S] [RingHomClass G R S] (f : G)
    (b c : R) (M : ℕ) : f (tateF b c M) = tateF (f b) (f c) M := by
  unfold tateF
  split_ifs <;>
    simp only [map_sub, map_mul, map_add, map_pow, map_one, map_ofNat,
      map_tateN, map_tateD]

open MvPolynomial in
/-- `N_n ∈ ℤ[b, c]` (`X 0 = b`, `X 1 = c`). -/
noncomputable def polyN (n : ℕ) : MvPolynomial (Fin 2) ℤ := tateN (X 0) (X 1) n

open MvPolynomial in
/-- `D_n ∈ ℤ[b, c]`. -/
noncomputable def polyD (n : ℕ) : MvPolynomial (Fin 2) ℤ := tateD (X 0) (X 1) n

open MvPolynomial in
/-- The order-`M` polynomial `F_M ∈ ℤ[b, c]`. -/
noncomputable def polyF (M : ℕ) : MvPolynomial (Fin 2) ℤ := tateF (X 0) (X 1) M

lemma aeval_polyN (b c : R) (n : ℕ) : MvPolynomial.aeval ![b, c] (polyN n) = tateN b c n := by
  rw [polyN, map_tateN (MvPolynomial.aeval (R := ℤ) ![b, c])]; simp

lemma aeval_polyD (b c : R) (n : ℕ) : MvPolynomial.aeval ![b, c] (polyD n) = tateD b c n := by
  rw [polyD, map_tateD (MvPolynomial.aeval (R := ℤ) ![b, c])]; simp

lemma aeval_polyF (b c : R) (M : ℕ) : MvPolynomial.aeval ![b, c] (polyF M) = tateF b c M := by
  rw [polyF, map_tateF (MvPolynomial.aeval (R := ℤ) ![b, c])]; simp

end Seq

/-! ## Multiples of `(0,0)` -/

section Field

variable {F : Type*} [Field F]

lemma exists_some_eq {W : WeierstrassCurve F} {x y x' : F} (h : W.toAffine.Nonsingular x y)
    (hx : x = x') : ∃ (y' : F) (h' : W.toAffine.Nonsingular x' y'),
      (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; exact ⟨y, h, rfl⟩

lemma tate_equation_iff {b c x y : F} :
    (tate b c).toAffine.Equation x y ↔ y ^ 2 + (1 - c) * x * y - b * y = x ^ 3 - b * x ^ 2 := by
  rw [equation_iff']; simp only [tate_a₁, tate_a₂, tate_a₃, tate_a₄, tate_a₆]
  constructor <;> intro h <;> linear_combination h

lemma negY_tate_zero (b c : F) : (tate b c).toAffine.negY 0 0 = b := by simp [negY]

/-- Algebra of the recursion step. -/
lemma step_alg {b c N₁ D₁ D₂ X y : F} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0) (hX : X ≠ 0)
    (hrel : N₁ / D₁ = b * (b - y - (1 - c) * X) / X ^ 2) :
    b * y / X ^ 2 = (b * (b * D₂ - (1 - c) * (X * D₂)) * D₂ * D₁ - N₁ * (X * D₂) ^ 2) /
      ((X * D₂) ^ 2 * D₁) := by
  rw [div_eq_div_iff hD₁ (pow_ne_zero 2 hX)] at hrel
  rw [div_eq_div_iff (pow_ne_zero 2 hX) (mul_ne_zero (pow_ne_zero 2 (mul_ne_zero hX hD₂)) hD₁)]
  linear_combination (D₂ ^ 2 * X ^ 2) * hrel

variable [DecidableEq F]

lemma tatePt_ne_zero {b c : F} (hb : b ≠ 0) : tatePt b c ≠ 0 := by
  rw [tatePt_of_ne hb]; exact Point.some_ne_zero _

/-- Chord through `Q = (x, y)` and `P = (0,0)`: `x(Q + P) = b y / x²`. -/
lemma chord_add {b c : F} (hb : b ≠ 0) {x y : F} (h : (tate b c).toAffine.Nonsingular x y)
    (hx : x ≠ 0) : ∃ (y' : F) (h' : (tate b c).toAffine.Nonsingular (b * y / x ^ 2) y'),
      Point.some x y h + tatePt b c = Point.some _ y' h' := by
  rw [tatePt_of_ne hb, Point.add_of_X_ne hx]
  refine exists_some_eq _ ?_
  have e := tate_equation_iff.mp h.1
  have hL : (y - 0) / (x - 0) * x = y := by rw [sub_zero, sub_zero, div_mul_cancel₀ _ hx]
  rw [slope_of_X_ne hx, eq_div_iff (pow_ne_zero 2 hx)]
  simp only [addX, tate_a₁, tate_a₂]
  linear_combination e + ((y - 0) / (x - 0) * x + y + (1 - c) * x) * hL

/-- Chord through `Q = (x, y)` and `-P = (0, b)`: `x(Q - P) = b (b - y - (1-c) x) / x²`. -/
lemma chord_neg {b c : F} (hb : b ≠ 0) {x y : F} (h : (tate b c).toAffine.Nonsingular x y)
    (hx : x ≠ 0) : ∃ (y' : F)
      (h' : (tate b c).toAffine.Nonsingular (b * (b - y - (1 - c) * x) / x ^ 2) y'),
      Point.some x y h + -tatePt b c = Point.some _ y' h' := by
  rw [tatePt_of_ne hb, Point.neg_some, Point.add_of_X_ne hx]
  refine exists_some_eq _ ?_
  have e := tate_equation_iff.mp h.1
  rw [slope_of_X_ne hx, eq_div_iff (pow_ne_zero 2 hx), negY_tate_zero]
  have hL : (y - b) / (x - 0) * x = y - b := by rw [sub_zero, div_mul_cancel₀ _ hx]
  simp only [addX, tate_a₁, tate_a₂]
  linear_combination e + ((y - b) / (x - 0) * x + (y - b) + (1 - c) * x) * hL

lemma two_nsmul_tatePt {b c : F} (hb : b ≠ 0) :
    ∃ (y : F) (h : (tate b c).toAffine.Nonsingular b y), 2 • tatePt b c = Point.some b y h := by
  have hy : (0 : F) ≠ (tate b c).toAffine.negY 0 0 := by rw [negY_tate_zero]; exact hb.symm
  rw [two_nsmul, tatePt_of_ne hb, Point.add_self_of_Y_ne hy]
  refine exists_some_eq _ ?_
  rw [slope_of_Y_ne rfl hy]
  simp [addX]

/-- `n • (0,0) = (N_n / D_n, y)` with `D_n ≠ 0`. -/
def NSmulForm (b c : F) (n : ℕ) : Prop :=
  tateD b c n ≠ 0 ∧ ∃ (y : F) (h : (tate b c).toAffine.Nonsingular (tateN b c n / tateD b c n) y),
    n • tatePt b c = Point.some _ y h

lemma nsmulForm_one {b c : F} (hb : b ≠ 0) : NSmulForm b c 1 := by
  refine ⟨by simp, ?_⟩
  rw [one_nsmul, tatePt_of_ne hb]
  exact exists_some_eq _ (by simp)

lemma nsmulForm_two {b c : F} (hb : b ≠ 0) : NSmulForm b c 2 := by
  refine ⟨by simp, ?_⟩
  obtain ⟨y, h, h2⟩ := two_nsmul_tatePt (c := c) hb
  rw [h2]
  exact exists_some_eq _ (by simp)

lemma nsmulForm_step {b c : F} (hb : b ≠ 0) (n : ℕ) (h1 : NSmulForm b c (n + 1))
    (h2 : NSmulForm b c (n + 2)) (hN : tateN b c (n + 2) ≠ 0) : NSmulForm b c (n + 3) := by
  obtain ⟨hD1, y₁, hy₁, hP1⟩ := h1
  obtain ⟨hD2, y₂, hy₂, hP2⟩ := h2
  have hX : tateN b c (n + 2) / tateD b c (n + 2) ≠ 0 := div_ne_zero hN hD2
  have hsub : (n + 1) • tatePt b c = (n + 2) • tatePt b c + -tatePt b c := by
    rw [show (n + 2) • tatePt b c = (n + 1) • tatePt b c + tatePt b c from succ_nsmul _ _,
      add_neg_cancel_right]
  obtain ⟨y', hy', hneg⟩ := chord_neg hb hy₂ hX
  rw [hP1, hP2, hneg, Point.some.injEq] at hsub
  obtain ⟨y'', hy'', hadd⟩ := chord_add hb hy₂ hX
  refine ⟨by rw [tateD_add_three]; exact mul_ne_zero (pow_ne_zero 2 hN) hD1, ?_⟩
  rw [show (n + 3) • tatePt b c = (n + 2) • tatePt b c + tatePt b c from succ_nsmul _ _, hP2,
    hadd]
  refine exists_some_eq _ ?_
  have key := step_alg (D₂ := tateD b c (n + 2)) hD1 hD2 hX hsub.1
  rw [div_mul_cancel₀ _ hD2] at key
  rw [key, tateN_add_three, tateD_add_three]

lemma nsmulForm_aux {b c : F} (hb : b ≠ 0) (n : ℕ) :
    ((∀ j, 2 ≤ j → j < n + 1 → tateN b c j ≠ 0) → NSmulForm b c (n + 1)) ∧
      ((∀ j, 2 ≤ j → j < n + 2 → tateN b c j ≠ 0) → NSmulForm b c (n + 2)) := by
  induction n with
  | zero => exact ⟨fun _ => nsmulForm_one hb, fun _ => nsmulForm_two hb⟩
  | succ n ih =>
    refine ⟨ih.2, fun hj => ?_⟩
    exact nsmulForm_step hb n (ih.1 fun j h1 h2 => hj j h1 (by omega))
      (ih.2 fun j h1 h2 => hj j h1 (by omega)) (hj (n + 2) (by omega) (by omega))

/-- `n • (0,0) = (N_n / D_n, y)` on `E(b,c)`, `b ≠ 0`, as long as `N_j ≠ 0` for `2 ≤ j < n`. -/
theorem nsmulForm_of {b c : F} (hb : b ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ j, 2 ≤ j → j < n → tateN b c j ≠ 0) : NSmulForm b c n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (nsmulForm_aux hb m).1 h

lemma tateN_ne_zero_of {b c : F} (hb : b ≠ 0) (k : ℕ)
    (hprev : ∀ j, 2 ≤ j → j < k + 2 → tateN b c j ≠ 0) (h1 : (k + 1) • tatePt b c ≠ 0)
    (h3 : (k + 2 + 1) • tatePt b c ≠ 0) : tateN b c (k + 2) ≠ 0 := by
  obtain ⟨hD, y, hy, hP⟩ := nsmulForm_of hb (n := k + 2) (by omega) hprev
  intro hN0
  have hx : tateN b c (k + 2) / tateD b c (k + 2) = 0 := by rw [hN0, zero_div]
  have h0 : (tate b c).toAffine.Nonsingular 0 0 := (tate_nonsingular_zero_iff b c).mpr hb
  rcases (Point.X_eq_iff (h₁ := hy) (h₂ := h0)).mp hx with h' | h'
  · rw [← hP, ← tatePt_of_ne hb, show k + 2 = (k + 1) + 1 from rfl, succ_nsmul] at h'
    apply h1
    have : (k + 1) • tatePt b c + tatePt b c = 0 + tatePt b c := by rw [zero_add]; exact h'
    exact add_right_cancel this
  · rw [← hP, ← tatePt_of_ne hb] at h'
    apply h3
    rw [succ_nsmul, h', neg_add_cancel]

/-- For `b ≠ 0`: `j • (0,0) ≠ 0` for `1 ≤ j ≤ n + 1` iff `N_j ≠ 0` for `2 ≤ j ≤ n`. -/
theorem nsmul_ne_zero_iff_tateN {b c : F} (hb : b ≠ 0) (n : ℕ) :
    (∀ j, 1 ≤ j → j ≤ n + 1 → j • tatePt b c ≠ 0) ↔ ∀ j, 2 ≤ j → j ≤ n → tateN b c j ≠ 0 := by
  constructor
  · induction n with
    | zero => intro _ j h1 h2; omega
    | succ n ih =>
      intro H j hj1 hj2
      have ih' := ih fun j h1 h2 => H j h1 (by omega)
      rcases Nat.lt_or_ge j (n + 1) with hlt | hge
      · exact ih' j hj1 (by omega)
      · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
        exact tateN_ne_zero_of hb k (fun i h1 h2 => ih' i h1 (by omega)) (H (k + 1) (by omega)
          (by omega)) (H (k + 2 + 1) (by omega) (by omega))
  · intro H j hj1 hj2
    obtain ⟨hD, y, hy, hP⟩ := nsmulForm_of hb hj1 fun i h1 h2 => H i h1 (by omega)
    rw [hP]; exact Point.some_ne_zero _

/-! ## Exact order -/

/-- `(0,0)` has exact order `M` on `E(b,c)`: `M • P = 0` and `d • P ≠ 0` for every proper
divisor `d` of `M` (group law of Mathlib's `WeierstrassCurve.Affine.Point`). -/
def HasExactOrder (M : ℕ) (b c : F) : Prop :=
  M • tatePt b c = 0 ∧ ∀ d : ℕ, d ∣ M → d < M → d • tatePt b c ≠ 0

theorem hasExactOrder_iff {M : ℕ} (hM : 0 < M) (b c : F) :
    HasExactOrder M b c ↔ addOrderOf (tatePt b c) = M := by
  constructor
  · rintro ⟨h0, hd⟩
    have hdvd : addOrderOf (tatePt b c) ∣ M := addOrderOf_dvd_of_nsmul_eq_zero h0
    by_contra hne
    exact hd _ hdvd (lt_of_le_of_ne (Nat.le_of_dvd hM hdvd) hne) (addOrderOf_nsmul_eq_zero _)
  · intro h
    refine ⟨by rw [← h]; exact addOrderOf_nsmul_eq_zero _, fun d hd hlt => ?_⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hM.ne' (Nat.eq_zero_of_zero_dvd hd)
    exact nsmul_ne_zero_of_lt_addOrderOf hd0 (by rw [h]; exact hlt)

/-- For `M ≥ 4`, exact order `M` is decided by `j • P ≠ 0` for `j ≤ M/2 + 1` and `M • P = 0`. -/
theorem hasExactOrder_iff_nsmul {M : ℕ} (hM : 4 ≤ M) (b c : F) :
    HasExactOrder M b c ↔
      (∀ j, 1 ≤ j → j ≤ M / 2 + 1 → j • tatePt b c ≠ 0) ∧ M • tatePt b c = 0 := by
  rw [hasExactOrder_iff (by omega)]
  constructor
  · intro h
    refine ⟨fun j hj1 hj2 => nsmul_ne_zero_of_lt_addOrderOf (by omega) (by omega), ?_⟩
    rw [← h]; exact addOrderOf_nsmul_eq_zero _
  · rintro ⟨hne, h0⟩
    obtain ⟨k, hk⟩ := addOrderOf_dvd_of_nsmul_eq_zero h0
    by_contra hne'
    have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; omega
    have hk1 : k ≠ 1 := by rintro rfl; rw [mul_one] at hk; exact hne' hk.symm
    have hpos : addOrderOf (tatePt b c) ≠ 0 := by rintro h; rw [h, zero_mul] at hk; omega
    have h2 : addOrderOf (tatePt b c) * 2 ≤ M := by
      rw [hk]; exact Nat.mul_le_mul_left _ (by omega)
    exact hne _ (by omega) (by omega) (addOrderOf_nsmul_eq_zero _)

omit [DecidableEq F] in
lemma even_alg {b c N₂ D₂ N₃ D₃ y : F} (hb : b ≠ 0) (hD₂ : D₂ ≠ 0) (hD₃ : D₃ ≠ 0)
    (hN₂ : N₂ ≠ 0) (h : N₃ / D₃ = b * y / (N₂ / D₂) ^ 2) :
    y = (tate b c).toAffine.negY (N₂ / D₂) y ↔
      2 * N₂ ^ 2 * N₃ + b * (1 - c) * N₂ * D₂ * D₃ - b ^ 2 * D₂ ^ 2 * D₃ = 0 := by
  have hX : N₂ / D₂ ≠ 0 := div_ne_zero hN₂ hD₂
  rw [div_eq_div_iff hD₃ (pow_ne_zero 2 hX)] at h
  have hX' : N₂ = N₂ / D₂ * D₂ := (div_mul_cancel₀ N₂ hD₂).symm
  have key : 2 * N₂ ^ 2 * N₃ + b * (1 - c) * N₂ * D₂ * D₃ - b ^ 2 * D₂ ^ 2 * D₃ =
      b * D₂ ^ 2 * D₃ * (2 * y + (1 - c) * (N₂ / D₂) - b) := by
    linear_combination (2 * N₃ * (N₂ + N₂ / D₂ * D₂) + b * (1 - c) * D₂ * D₃) * hX' +
      2 * D₂ ^ 2 * h
  rw [key, mul_eq_zero, or_iff_right (mul_ne_zero (mul_ne_zero hb (pow_ne_zero 2 hD₂)) hD₃)]
  simp only [negY, tate_a₁, tate_a₃]
  constructor <;> intro h' <;> linear_combination h'

/-- `M • (0,0) = 0` iff `F_M(b,c) = 0`, given `b ≠ 0` and `N_j ≠ 0` for `2 ≤ j ≤ M/2`. -/
theorem nsmul_eq_zero_iff_tateF {b c : F} (hb : b ≠ 0) {M : ℕ} (hM : 4 ≤ M)
    (hN : ∀ j, 2 ≤ j → j ≤ M / 2 → tateN b c j ≠ 0) :
    M • tatePt b c = 0 ↔ tateF b c M = 0 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' M <;>
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  · obtain ⟨hD2, y₂, hy₂, hP2⟩ := nsmulForm_of hb (n := k + 2) (by omega)
      fun j h1 h2 => hN j h1 (by omega)
    obtain ⟨hD3, y₃, hy₃, hP3⟩ := nsmulForm_of hb (n := k + 2 + 1) (by omega)
      fun j h1 h2 => hN j h1 (by omega)
    have hN2 : tateN b c (k + 2) ≠ 0 := hN _ (by omega) (by omega)
    obtain ⟨y', hy', hadd⟩ := chord_add hb hy₂ (div_ne_zero hN2 hD2)
    have h3 : (k + 2 + 1) • tatePt b c = (k + 2) • tatePt b c + tatePt b c := succ_nsmul _ _
    rw [hP3, hP2, hadd, Point.some.injEq] at h3
    rw [tateF_even, show 2 * (k + 2) = (k + 2) + (k + 2) by ring, add_nsmul,
      add_eq_zero_iff_eq_neg, hP2, Point.neg_some, Point.some.injEq]
    exact (and_iff_right rfl).trans (even_alg hb hD2 hD3 hN2 h3.1)
  · obtain ⟨hD2, y₂, hy₂, hP2⟩ := nsmulForm_of hb (n := k + 2) (by omega)
      fun j h1 h2 => hN j h1 (by omega)
    obtain ⟨hD3, y₃, hy₃, hP3⟩ := nsmulForm_of hb (n := k + 2 + 1) (by omega)
      fun j h1 h2 => hN j h1 (by omega)
    have hne : (Point.some _ y₃ hy₃ : (tate b c).toAffine.Point) ≠ Point.some _ y₂ hy₂ := by
      intro heq
      rw [← hP3, ← hP2, succ_nsmul] at heq
      apply tatePt_ne_zero (c := c) hb
      have : (k + 2) • tatePt b c + tatePt b c = (k + 2) • tatePt b c + 0 := by
        rw [add_zero]; exact heq
      exact add_left_cancel this
    rw [tateF_odd, show 2 * (k + 2) + 1 = (k + 2 + 1) + (k + 2) by ring, add_nsmul,
      add_eq_zero_iff_eq_neg, hP3, hP2, sub_eq_zero, ← div_eq_div_iff hD3 hD2,
      Point.X_eq_iff (h₁ := hy₃) (h₂ := hy₂)]
    exact ⟨Or.inr, fun h => h.resolve_left hne⟩

/-- **Explicit order criterion.** For `M ≥ 4`, `(0,0)` has exact order `M` on `E(b,c)` iff
`b ≠ 0`, `N_j(b,c) ≠ 0` for `2 ≤ j ≤ M/2`, and `F_M(b,c) = 0`. -/
theorem hasExactOrder_iff_tateF {M : ℕ} (hM : 4 ≤ M) (b c : F) :
    HasExactOrder M b c ↔
      b ≠ 0 ∧ (∀ j, 2 ≤ j → j ≤ M / 2 → tateN b c j ≠ 0) ∧ tateF b c M = 0 := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨fun h => absurd ?_ (h.2 1 (one_dvd _) (by omega)), fun h => absurd rfl h.1⟩
    simp [tatePt]
  rw [hasExactOrder_iff_nsmul hM, nsmul_ne_zero_iff_tateN hb (M / 2)]
  constructor
  · rintro ⟨hN, h0⟩; exact ⟨hb, hN, (nsmul_eq_zero_iff_tateF hb hM hN).mp h0⟩
  · rintro ⟨-, hN, hF⟩; exact ⟨hN, (nsmul_eq_zero_iff_tateF hb hM hN).mpr hF⟩

/-- Polynomial form: the same criterion with `N_j, F_M ∈ ℤ[b,c]` evaluated at `(b,c)`. -/
theorem hasExactOrder_iff_polyF {M : ℕ} (hM : 4 ≤ M) (b c : F) :
    HasExactOrder M b c ↔ b ≠ 0 ∧
      (∀ j, 2 ≤ j → j ≤ M / 2 → MvPolynomial.aeval ![b, c] (polyN j) ≠ 0) ∧
      MvPolynomial.aeval ![b, c] (polyF M) = 0 := by
  simp only [aeval_polyN, aeval_polyF]; exact hasExactOrder_iff_tateF hM b c

theorem hasExactOrder_four_iff (b c : F) : HasExactOrder 4 b c ↔ b ≠ 0 ∧ c = 0 := by
  have hF : tateF b c 4 = b ^ 4 * c := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, tateF_even]
    simp only [Nat.reduceAdd, tateN_two, tateD_two, tateN_three, tateD_three]; ring
  rw [hasExactOrder_iff_tateF le_rfl, hF]
  constructor
  · rintro ⟨hb, -, h⟩; exact ⟨hb, by simpa [hb] using h⟩
  · rintro ⟨hb, rfl⟩
    refine ⟨hb, fun j h1 h2 => ?_, by ring⟩
    obtain rfl : j = 2 := by omega
    simpa using hb

theorem hasExactOrder_five_iff (b c : F) : HasExactOrder 5 b c ↔ b ≠ 0 ∧ b = c := by
  have hF : tateF b c 5 = b ^ 2 * (c - b) := by
    rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, tateF_odd]
    simp only [Nat.reduceAdd, tateN_two, tateD_two, tateN_three, tateD_three]; ring
  rw [hasExactOrder_iff_tateF (by norm_num), hF]
  constructor
  · rintro ⟨hb, -, h⟩
    exact ⟨hb, (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hb))).symm⟩
  · rintro ⟨hb, rfl⟩
    refine ⟨hb, fun j h1 h2 => ?_, by ring⟩
    obtain rfl : j = 2 := by omega
    simpa using hb

theorem hasExactOrder_six_iff (b c : F) :
    HasExactOrder 6 b c ↔ b ≠ 0 ∧ c ≠ 0 ∧ b = c + c ^ 2 := by
  have hF : tateF b c 6 = b ^ 9 * c ^ 2 * (b - c - c ^ 2) := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, tateF_even]
    simp only [Nat.reduceAdd, tateN_three, tateD_three, tateN_four, tateD_four]; ring
  rw [hasExactOrder_iff_tateF (by norm_num), hF]
  constructor
  · rintro ⟨hb, hN, h⟩
    have hc : c ≠ 0 := by
      intro hc; apply hN 3 (by norm_num) (by norm_num); rw [tateN_three, hc, mul_zero]
    refine ⟨hb, hc, ?_⟩
    have := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero 9 hb) (pow_ne_zero 2 hc))
    linear_combination this
  · rintro ⟨hb, hc, hbc⟩
    refine ⟨hb, fun j h1 h2 => ?_, by rw [hbc]; ring⟩
    obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
    · simpa using hb
    · rw [tateN_three]; exact mul_ne_zero (pow_ne_zero 2 hb) hc

theorem hasExactOrder_seven_iff (b c : F) :
    HasExactOrder 7 b c ↔ b ≠ 0 ∧ c ≠ 0 ∧ b ^ 2 - b * c - c ^ 3 = 0 := by
  have hF : tateF b c 7 = b ^ 6 * (b ^ 2 - b * c - c ^ 3) := by
    rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, tateF_odd]
    simp only [Nat.reduceAdd, tateN_three, tateD_three, tateN_four, tateD_four]; ring
  rw [hasExactOrder_iff_tateF (by norm_num), hF]
  constructor
  · rintro ⟨hb, hN, h⟩
    have hc : c ≠ 0 := by
      intro hc; apply hN 3 (by norm_num) (by norm_num); rw [tateN_three, hc, mul_zero]
    exact ⟨hb, hc, (mul_eq_zero.mp h).resolve_left (pow_ne_zero 6 hb)⟩
  · rintro ⟨hb, hc, h⟩
    refine ⟨hb, fun j h1 h2 => ?_, by rw [h, mul_zero]⟩
    obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
    · simpa using hb
    · rw [tateN_three]; exact mul_ne_zero (pow_ne_zero 2 hb) hc

/-! ## `Y₁(M)` and the moduli bijection -/

variable (F) in
/-- `Y₁(M)(F)`: pairs `(b,c)` with `Δ(b,c) ≠ 0` and `(0,0)` of exact order `M` on `E(b,c)`. -/
def Y1 (M : ℕ) : Set (F × F) := {bc | tateDisc bc.1 bc.2 ≠ 0 ∧ HasExactOrder M bc.1 bc.2}

variable (F) in
/-- Pairs `(E, P)`: a Weierstrass curve over `F` with `Δ ≠ 0` and `P ∈ E(F)` of exact order `M`. -/
def PairM (M : ℕ) : Type _ :=
  {x : Σ W : WeierstrassCurve F, W.toAffine.Point // x.1.Δ ≠ 0 ∧ addOrderOf x.2 = M}

variable (F) in
/-- Isomorphism of pointed curves: a change of variables carrying one to the other. -/
def pairSetoid (M : ℕ) : Setoid (PairM F M) where
  r x y := ∃ C : VariableChange F, IsPtIso C x.1.2 y.1.2
  iseqv := by
    refine ⟨fun x => ⟨1, one_smul _ _, ptMap_one _ _⟩, ?_, ?_⟩
    · rintro x y ⟨C, h, hP⟩
      exact ⟨C⁻¹, inv_smul_eq C h, by rw [← hP]; exact ptMap_inv_ptMap C h _ _⟩
    · rintro x y z ⟨C, h, hP⟩ ⟨C', h', hP'⟩
      exact ⟨C' * C, by rw [mul_smul, h, h'], by rw [ptMap_mul C' C h h', hP, hP']⟩

lemma pairSetoid_r {M : ℕ} {x y : PairM F M} :
    (pairSetoid F M).r x y ↔ ∃ C : VariableChange F, IsPtIso C x.1.2 y.1.2 := Iff.rfl

variable (F) in
/-- Isomorphism classes of pairs `(E, P)` with `P` of exact order `M`. -/
def PairClass (M : ℕ) : Type _ := Quotient (pairSetoid F M)

/-- The pair `(E(b,c), (0,0))` attached to a point of `Y₁(M)`. -/
def tatePair {M : ℕ} (hM : 0 < M) (bc : Y1 F M) : PairM F M :=
  ⟨⟨tate bc.1.1 bc.1.2, tatePt bc.1.1 bc.1.2⟩,
    by show (tate bc.1.1 bc.1.2).Δ ≠ 0; rw [tate_Δ]; exact bc.2.1,
    (hasExactOrder_iff hM _ _).mp bc.2.2⟩

/-- The moduli map `Y₁(M)(F) → {(E, P)}/≅`. -/
def y1ToClass {M : ℕ} (hM : 0 < M) (bc : Y1 F M) : PairClass F M :=
  Quotient.mk (pairSetoid F M) (tatePair hM bc)

theorem y1ToClass_injective {M : ℕ} (hM : 0 < M) : Function.Injective (y1ToClass (F := F) hM) := by
  rintro ⟨⟨b, c⟩, hbc⟩ ⟨⟨b', c'⟩, hbc'⟩ h
  obtain ⟨C, hC⟩ := pairSetoid_r.mp (Quotient.exact h)
  obtain ⟨-, rfl, rfl⟩ := tate_rigid (b := b) (c := c) (b' := b') (c' := c')
    (ne_zero_of_tateDisc_ne_zero hbc.1) C hC
  rfl

theorem y1ToClass_surjective {M : ℕ} (hM : 4 ≤ M) :
    Function.Surjective (y1ToClass (F := F) (by omega : 0 < M)) := by
  intro q
  obtain ⟨⟨⟨W, P⟩, hΔ0, hord0⟩, rfl⟩ := Quotient.exists_rep q
  have hΔ : W.Δ ≠ 0 := hΔ0
  have hord : addOrderOf P = M := hord0
  have hk : ∀ k : ℕ, k ≠ 0 → k < 4 → k • P ≠ 0 := fun k hk0 hk4 =>
    nsmul_ne_zero_of_lt_addOrderOf hk0 (by omega)
  have h1 : P ≠ 0 := by simpa using hk 1 one_ne_zero (by norm_num)
  obtain ⟨b, c, C, hb, h, hP⟩ := exists_normalForm W P h1 (hk 2 two_ne_zero (by norm_num))
    (hk 3 three_ne_zero (by norm_num))
  have hΔ' : tateDisc b c ≠ 0 := by
    rw [← tate_Δ, ← h, variableChange_Δ]
    exact mul_ne_zero (by simp) hΔ
  have hord' : addOrderOf (tatePt b c) = M := by rw [← hP, addOrderOf_ptMap, hord]
  refine ⟨⟨(b, c), hΔ', (hasExactOrder_iff (by omega) b c).mpr hord'⟩, ?_⟩
  apply Quotient.sound
  exact pairSetoid_r.mpr ⟨C⁻¹, inv_smul_eq C h, by
    show ptMap C⁻¹ (inv_smul_eq C h) (tatePt b c) = P
    rw [← hP]; exact ptMap_inv_ptMap C h _ _⟩

/-- **Moduli bijection.** For `M ≥ 4`, over any field, `Y₁(M)(F)` is in bijection with the
isomorphism classes of pairs `(E, P)`, `P ∈ E(F)` of exact order `M`. -/
noncomputable def y1Equiv {M : ℕ} (hM : 4 ≤ M) : Y1 F M ≃ PairClass F M :=
  Equiv.ofBijective (y1ToClass (by omega)) ⟨y1ToClass_injective (F := F) (by omega), y1ToClass_surjective hM⟩

theorem card_Y1 {M : ℕ} (hM : 4 ≤ M) : Nat.card (Y1 F M) = Nat.card (PairClass F M) :=
  Nat.card_congr (y1Equiv hM)

/-- Finite-field form (`p = char F ∤ M`; the bijection holds in every characteristic). -/
theorem card_Y1_finite [Finite F] {M : ℕ} (hM : 4 ≤ M) (_hpM : ¬ ringChar F ∣ M) :
    Nat.card (Y1 F M) = Nat.card (PairClass F M) ∧ Finite (PairClass F M) :=
  ⟨card_Y1 hM, Finite.of_equiv _ (y1Equiv hM)⟩

end Field

end RPLib.TateNF


