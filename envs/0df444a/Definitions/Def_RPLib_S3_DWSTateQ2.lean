-- Prove2me | Definitions.Def_RPLib_S3_DWSTateQ2
-- name    : RPLib_S3_DWSTateQ2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:21:20.99728+00:00
-- url     : https://prove2.me/theorems/84570b94-a4d7-4ab2-bffd-5fdb34cfc3bf
-- title:
--   Weight-two Ramanujan-Petersson library: oriented pairs in `ℤ[ω]` and their binary quadratic forms
-- statement:
--   Oriented pairs in `ℤ[ω]` and their binary quadratic forms.
--
--   Pure algebra. `R = QuadraticAlgebra ℤ a b` (`ω² = a + b ω`).
--   * `dt x y = im (x̄ y)` (the determinant of the coordinates), `tr2 x y = Tr (x̄ y)` (polar form of the norm),
--     `lin p r x y = p x + r y` in coordinates; `norm_lin`, `tr2_lin`, `dt_lin`, `dt_mul`, `tr2_mul`.
--   * `HasForm x y f`: `N(X x - Y y) = dt x y · f(X, Y)` coefficientwise.
--   * `HasForm.mul` (scaling by `z`), `HasForm.act` (change of basis by `γ ∈ SL(2, ℤ)` gives `act γ f`),
--     `HasForm.unique`, **`HasForm.mul_eq`** (two pairs with the same form are proportional: `y x' = y' x`),
--     `hasForm_lat` (the pair `(A, ω - k)` has the form `(A, 2k - b, C)`), `det_eq_one_of_bases`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed., Wiley 2013, Sections 2, 7 and 11; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateQ1
import Definitions.Def_RPLib_S3_HurwitzA

/-!
# S3-DWS-Tate, part Q2: oriented pairs in `ℤ[ω]` and their binary quadratic forms

Pure algebra. `R = QuadraticAlgebra ℤ a b` (`ω² = a + b ω`).
* `dt x y = im (x̄ y)` (the determinant of the coordinates), `tr2 x y = Tr (x̄ y)` (polar form of the norm),
  `lin p r x y = p x + r y` in coordinates; `norm_lin`, `tr2_lin`, `dt_lin`, `dt_mul`, `tr2_mul`.
* `HasForm x y f`: `N(X x - Y y) = dt x y · f(X, Y)` coefficientwise.
* `HasForm.mul` (scaling by `z`), `HasForm.act` (change of basis by `γ ∈ SL(2, ℤ)` gives `act γ f`),
  `HasForm.unique`, **`HasForm.mul_eq`** (two pairs with the same form are proportional: `y x' = y' x`),
  `hasForm_lat` (the pair `(A, ω - k)` has the form `(A, 2k - b, C)`), `det_eq_one_of_bases`.
-/

set_option autoImplicit false

namespace RPLib.DWS.QA

open QuadraticAlgebra RamanujanPetersson.Hurwitz MatrixGroups

variable {a b : ℤ}

/-- `im (x̄ y)`: the determinant of the coordinates of `x, y`. -/
def dt (x y : QuadraticAlgebra ℤ a b) : ℤ := x.re * y.im - x.im * y.re

/-- `Tr (x̄ y)`, the polar form of the norm. -/
def tr2 (x y : QuadraticAlgebra ℤ a b) : ℤ :=
  2 * x.re * y.re + b * (x.re * y.im + x.im * y.re) - 2 * a * x.im * y.im

/-- The integer combination `p x + r y`, in coordinates. -/
def lin (p r : ℤ) (x y : QuadraticAlgebra ℤ a b) : QuadraticAlgebra ℤ a b :=
  ⟨p * x.re + r * y.re, p * x.im + r * y.im⟩

theorem lin_eq (p r : ℤ) (x y : QuadraticAlgebra ℤ a b) :
    lin p r x y = (p : QuadraticAlgebra ℤ a b) * x + (r : QuadraticAlgebra ℤ a b) * y := by
  ext <;> simp [lin]

theorem norm_lin (p r : ℤ) (x y : QuadraticAlgebra ℤ a b) :
    (lin p r x y).norm = p ^ 2 * x.norm + p * r * tr2 x y + r ^ 2 * y.norm := by
  simp only [lin, norm_def, tr2]; ring

theorem tr2_lin (p r q s : ℤ) (x y : QuadraticAlgebra ℤ a b) :
    tr2 (lin p r x y) (lin q s x y) =
      2 * p * q * x.norm + (p * s + r * q) * tr2 x y + 2 * r * s * y.norm := by
  simp only [lin, norm_def, tr2]; ring

theorem dt_lin (p r q s : ℤ) (x y : QuadraticAlgebra ℤ a b) :
    dt (lin p r x y) (lin q s x y) = (p * s - r * q) * dt x y := by
  simp only [lin, dt]; ring

theorem dt_mul (z x y : QuadraticAlgebra ℤ a b) : dt (z * x) (z * y) = z.norm * dt x y := by
  simp only [dt, re_mul, im_mul, norm_def]; ring

theorem tr2_mul (z x y : QuadraticAlgebra ℤ a b) : tr2 (z * x) (z * y) = z.norm * tr2 x y := by
  simp only [tr2, re_mul, im_mul, norm_def]; ring

/-- `(x, y)` has the form `f`: `N(X x - Y y) = dt x y · f(X, Y)` coefficientwise. -/
def HasForm (x y : QuadraticAlgebra ℤ a b) (f : BQF) : Prop :=
  x.norm = dt x y * f.a ∧ -tr2 x y = dt x y * f.b ∧ y.norm = dt x y * f.c

theorem HasForm.mul {x y : QuadraticAlgebra ℤ a b} {f : BQF} (h : HasForm x y f)
    (z : QuadraticAlgebra ℤ a b) : HasForm (z * x) (z * y) f := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, dt_mul, h1]; ring
  · rw [tr2_mul, dt_mul]; linear_combination z.norm * h2
  · rw [map_mul, dt_mul, h3]; ring

theorem act_a' (γ : SL(2, ℤ)) (f : BQF) :
    (act γ f).a = f.a * γ 0 0 ^ 2 + f.b * γ 0 0 * γ 1 0 + f.c * γ 1 0 ^ 2 := rfl

theorem act_b' (γ : SL(2, ℤ)) (f : BQF) :
    (act γ f).b = 2 * f.a * γ 0 0 * γ 0 1 + f.b * (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) +
      2 * f.c * γ 1 0 * γ 1 1 := rfl

theorem act_c' (γ : SL(2, ℤ)) (f : BQF) :
    (act γ f).c = f.a * γ 0 1 ^ 2 + f.b * γ 0 1 * γ 1 1 + f.c * γ 1 1 ^ 2 := rfl

/-- Change of basis by `γ ∈ SL(2, ℤ)`. -/
theorem HasForm.act {x y : QuadraticAlgebra ℤ a b} {f : BQF} (h : HasForm x y f) (γ : SL(2, ℤ)) :
    HasForm (lin (γ 0 0) (-γ 1 0) x y) (lin (-γ 0 1) (γ 1 1) x y) (act γ f) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := RamanujanPetersson.Hurwitz.det_eq γ
  have hdt : dt (lin (γ 0 0) (-γ 1 0) x y) (lin (-γ 0 1) (γ 1 1) x y) = dt x y := by
    rw [dt_lin]; linear_combination (dt x y) * hd
  refine ⟨?_, ?_, ?_⟩ <;> rw [hdt]
  · rw [norm_lin, act_a']
    linear_combination (γ 0 0) ^ 2 * h1 + (γ 0 0) * (γ 1 0) * h2 + (γ 1 0) ^ 2 * h3
  · rw [tr2_lin, act_b']
    linear_combination 2 * (γ 0 0) * (γ 0 1) * h1 + ((γ 0 0) * (γ 1 1) + (γ 0 1) * (γ 1 0)) * h2 +
      2 * (γ 1 0) * (γ 1 1) * h3
  · rw [norm_lin, act_c']
    linear_combination (γ 0 1) ^ 2 * h1 + (γ 0 1) * (γ 1 1) * h2 + (γ 1 1) ^ 2 * h3

theorem HasForm.unique {x y : QuadraticAlgebra ℤ a b} {f g : BQF} (h : HasForm x y f)
    (h' : HasForm x y g) (hd : dt x y ≠ 0) : f = g := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨g1, g2, g3⟩ := h'
  ext
  · exact mul_left_cancel₀ hd (h1.symm.trans g1)
  · exact mul_left_cancel₀ hd (h2.symm.trans g2)
  · exact mul_left_cancel₀ hd (h3.symm.trans g3)

theorem im_star_mul (x y : QuadraticAlgebra ℤ a b) : (star x * y).im = dt x y := by
  simp only [im_mul, re_star, im_star, dt]; ring

theorem two_re_star_mul (x y : QuadraticAlgebra ℤ a b) :
    2 * (star x * y).re = tr2 x y - b * dt x y := by
  simp only [re_mul, re_star, im_star, tr2, dt]; ring

theorem intCast_mul_eq_zero {n : ℤ} (hn : n ≠ 0) {z : QuadraticAlgebra ℤ a b}
    (h : (n : QuadraticAlgebra ℤ a b) * z = 0) : z = 0 := by
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp only [re_mul, im_mul, re_intCast, im_intCast, re_zero, im_zero, mul_zero, zero_mul,
    add_zero] at h1 h2
  ext
  · simpa [hn] using h1
  · simpa [hn] using h2

theorem re_intCast_mul (n : ℤ) (z : QuadraticAlgebra ℤ a b) :
    ((n : QuadraticAlgebra ℤ a b) * z).re = n * z.re := by simp

theorem im_intCast_mul (n : ℤ) (z : QuadraticAlgebra ℤ a b) :
    ((n : QuadraticAlgebra ℤ a b) * z).im = n * z.im := by simp

theorem mul_star_eq_norm (x : QuadraticAlgebra ℤ a b) :
    x * star x = (x.norm : QuadraticAlgebra ℤ a b) :=
  (algebraMap_norm_eq_mul_star x).symm.trans (eq_intCast _ _)

/-- **Two pairs with the same form are proportional**: `y x' = y' x`. -/
theorem HasForm.mul_eq {x y x' y' : QuadraticAlgebra ℤ a b} {f : BQF} (h : HasForm x y f)
    (h' : HasForm x' y' f) (ha : f.a ≠ 0) (hd : dt x y ≠ 0) (hd' : dt x' y' ≠ 0) :
    y * x' = y' * x := by
  have key : (dt x' y' : QuadraticAlgebra ℤ a b) * (star x * y) =
      (dt x y : QuadraticAlgebra ℤ a b) * (star x' * y') := by
    have e1 := two_re_star_mul x y
    have e2 := two_re_star_mul x' y'
    have t1 := h.2.1
    have t2 := h'.2.1
    ext
    · rw [re_intCast_mul, re_intCast_mul]
      apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
      linear_combination (dt x' y') * e1 - (dt x y) * e2 - (dt x' y') * t1 + (dt x y) * t2
    · rw [im_intCast_mul, im_intCast_mul, im_star_mul, im_star_mul]
      ring
  have hN : (x.norm : QuadraticAlgebra ℤ a b) = (dt x y : QuadraticAlgebra ℤ a b) * f.a := by
    rw [h.1]; push_cast; ring
  have hN' : (x'.norm : QuadraticAlgebra ℤ a b) = (dt x' y' : QuadraticAlgebra ℤ a b) * f.a := by
    rw [h'.1]; push_cast; ring
  have hx := mul_star_eq_norm x
  have hx' := mul_star_eq_norm x'
  have e : ((dt x' y' * dt x y * f.a : ℤ) : QuadraticAlgebra ℤ a b) * (y * x' - y' * x) = 0 := by
    push_cast
    linear_combination (-((dt x' y' : QuadraticAlgebra ℤ a b) * y * x')) * hN -
      ((dt x' y' : QuadraticAlgebra ℤ a b) * y * x') * hx + (x * x') * key +
      ((dt x y : QuadraticAlgebra ℤ a b) * x * y') * hx' +
      ((dt x y : QuadraticAlgebra ℤ a b) * x * y') * hN'
  exact sub_eq_zero.mp (intCast_mul_eq_zero (mul_ne_zero (mul_ne_zero hd' hd) ha) e)

theorem dt_lat (A k : ℤ) : dt (A : QuadraticAlgebra ℤ a b) ⟨-k, 1⟩ = A := by
  simp [dt]

/-- The pair `(A, ω - k)` has the form `(A, 2k - b, C)` when `a + k b - k² = -A C`. -/
theorem hasForm_lat {A k C : ℤ} (hC : a + k * b - k ^ 2 = -(A * C)) :
    HasForm (A : QuadraticAlgebra ℤ a b) ⟨-k, 1⟩ ⟨A, 2 * k - b, C⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [dt_lat] <;> simp only [norm_def, tr2, re_intCast, im_intCast, Int.cast_id]
  · ring
  · ring
  · linear_combination (-1 : ℤ) * hC

/-- Two oriented bases of one lattice differ by a matrix of determinant `1`. -/
theorem det_eq_one_of_bases {x y x' y' : QuadraticAlgebra ℤ a b} {m1 m2 m3 m4 n1 n2 n3 n4 : ℤ}
    (hx' : x' = lin m1 m2 x y) (hy' : y' = lin m3 m4 x y) (hx : x = lin n1 n2 x' y')
    (hy : y = lin n3 n4 x' y') (hd : 0 < dt x y) (hd' : 0 < dt x' y') : m1 * m4 - m2 * m3 = 1 := by
  have e1 : dt x' y' = (m1 * m4 - m2 * m3) * dt x y := by rw [hx', hy', dt_lin]
  have e2 : dt x y = (n1 * n4 - n2 * n3) * dt x' y' := by
    have := dt_lin n1 n2 n3 n4 x' y'
    rw [← hx, ← hy] at this
    exact this
  have hm : 0 < m1 * m4 - m2 * m3 := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hprod : (m1 * m4 - m2 * m3) * (n1 * n4 - n2 * n3) = 1 := by
    have h2 : ((m1 * m4 - m2 * m3) * (n1 * n4 - n2 * n3) - 1) * dt x y = 0 := by
      rw [e1] at e2; linear_combination -e2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linear_combination h3
    · exact absurd h3 (ne_of_gt hd)
  exact Int.eq_one_of_dvd_one (le_of_lt hm) ⟨_, hprod.symm⟩

end RPLib.DWS.QA


