-- Prove2me | Definitions.Def_PiIrrationality_BaiForms
-- name    : PiIrrationality_BaiForms
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:44:23.073926+00:00
-- url     : https://prove2.me/theorems/5348b987-f71e-4685-855f-bfb35f72e6e0
-- title:
--   Bai's integrals, positive coefficient and normaliser at exponents (1857, 3714, 5570)
-- statement:
--   Objects for Y. Bai's bound μ(π) ≤ 7.101862832357 (arXiv:2609.11276) at the exponents (a,b,c) = (1857, 3714, 5570), laid out like PiIrrationality_ZZEvenForms (the Zeilberger–Zudilin (2,4,6) case): R_n(t) = 5 t^{3714n}(t^4+6t^2+25)^{3714n}/(25-t^2)^{5570n+1}; J_n = -∫_{-2}^{2} R_n(-1+is) ds; A(z) = (1+z)^{3714}(2+6z+9z^2+6z^3+2z^4)^{3714}; coef_n = [z^{5570n}] A(z)^n (1-z)^{-7430n}; P_n = primes with max(5, √(7430n)) < p ≤ 7430n and {1857n/p+1/2} + 2{3714n/p} < {5570n/p}; Φ_n = ∏ P_n; M_n = 2^4 lcm(1..7430n)/(2^{4645n} Φ_n). Formalization note: J along t = -1+is; √(7430n) < p encoded as 7430n < p²; fractional parts in ℚ; Nat.lcmUpto is Mathlib's lcm(1..m). Interval tables (used by the prime-saving leaves): Dd = 7685213070; okRow (A,B,f1,f2,f3) says A < B ≤ D ≤ 7430A, the floors ⌊1857u+1/2⌋ = f1, ⌊3714u⌋ = f2, ⌊5570u⌋ = f3 are constant on [A/D, B/D) and Bai's inequality holds at u = B/D; chainOk says B_k ≤ A_{k+1}; term m t = D/(mD+A) - D/(mD+B); lam L K = Σ_{m<K} Σ_{t∈L} term m t.
-- source:
--   Y. Bai, arXiv:2609.11276 (v2), equations (1.8), (2.14), Proposition 2.7, (4.4)-(4.5), with (a,b,c) = (1857,3714,5570), https://arxiv.org/abs/2609.11276

import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Bai's linear forms for π: objects at exponents (1857, 3714, 5570)

Objects for Y. Bai, "The irrationality measure of π is at most 7.101862832357",
arXiv:2609.11276 (v2), equations (1.8), (2.14), Section 2 and (4.4)-(4.5), at the exponents
(a, b, c) = (1857, 3714, 5570), so d₀ = 2a + 4b - 2c = 7430 and h = 5b - 5c/2 = 4645.
The layout follows `PiIrrationality_ZZEvenForms` (the (2, 4, 6) case).
-/

namespace PiIrrationality.Bai

open Complex Polynomial

/-- `R_n(t) = 5 t^{3714n} (t^4+6t^2+25)^{3714n} / (25-t^2)^{5570n+1}`. -/
noncomputable def R (n : ℕ) (t : ℂ) : ℂ :=
  5 * t ^ (3714 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) / (25 - t ^ 2) ^ (5570 * n + 1)

/-- `J_n = i ∫_{-1-2i}^{-1+2i} R_n(t) dt` along `t = -1 + i s`. -/
noncomputable def J (n : ℕ) : ℂ :=
  -∫ s in (-2 : ℝ)..2, R n (-1 + (s : ℂ) * I)

/-- `A(z) = (1+z)^{3714} (2+6z+9z²+6z³+2z⁴)^{3714}`. -/
noncomputable def A : ℕ[X] :=
  (1 + X) ^ 3714 * (C 2 + C 6 * X + C 9 * X ^ 2 + C 6 * X ^ 3 + C 2 * X ^ 4) ^ 3714

/-- `coef n = [z^{5570n}] A(z)^n (1-z)^{-7430n}`. -/
noncomputable def coef (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (5570 * n + 1),
    (A ^ n).coeff k * Nat.choose (7430 * n - 1 + (5570 * n - k)) (5570 * n - k)

/-- Bai's set of deleted primes (2.14) for `(a,b,c) = (1857,3714,5570)`: primes `p` with
`max(5, √(7430n)) < p ≤ 7430n` and `{1857n/p + 1/2} + 2{3714n/p} < {5570n/p}`. -/
def deletedPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (7430 * n + 1)).filter fun p =>
    p.Prime ∧ 5 < p ∧ 7430 * n < p ^ 2 ∧
      Int.fract (((1857 * n : ℕ) : ℚ) / p + 1 / 2) + 2 * Int.fract (((3714 * n : ℕ) : ℚ) / p) <
        Int.fract (((5570 * n : ℕ) : ℚ) / p)

/-- The product `Φ_n` of the deleted primes. -/
def Phi (n : ℕ) : ℕ := ∏ p ∈ deletedPrimes n, p

/-- The normalising multiplier `M_n = 2^{4 - 4645 n} lcm(1,…,7430n) / Φ_n`. -/
noncomputable def M (n : ℕ) : ℝ :=
  2 ^ 4 * (Nat.lcmUpto (7430 * n) : ℝ) / (2 ^ (4645 * n) * (Phi n : ℝ))

/-! ### Interval tables for Bai's set of deleted primes

The deleted-prime condition depends only on `u = {n/p}` and holds on a periodic set `E ⊂ [0, 1)`.
A row `(A, B, f₁, f₂, f₃)` stands for the interval `[A/D, B/D)` with the common denominator `D = Dd`. -/

/-- The common denominator `D = 7685213070` of the interval tables. -/
def Dd : ℕ := 7685213070

/-- A row `(A, B, f₁, f₂, f₃)` is admissible: `A < B ≤ D ≤ 7430 A`, the floors
`⌊1857u + 1/2⌋ = f₁`, `⌊3714u⌋ = f₂` and `⌊5570u⌋ = f₃` are constant for `u ∈ [A/D, B/D)`,
and Bai's inequality `{1857u + 1/2} + 2{3714u} < {5570u}` holds at the right end `u = B/D`. -/
def okRow (t : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  Nat.blt t.1 t.2.1 && Nat.ble t.2.1 Dd && Nat.ble Dd (7430 * t.1) &&
  Nat.ble (2 * t.2.2.1 * Dd) (2 * 1857 * t.1 + Dd) &&
  Nat.ble (2 * 1857 * t.2.1 + Dd) (2 * (t.2.2.1 + 1) * Dd) &&
  Nat.ble (t.2.2.2.1 * Dd) (3714 * t.1) && Nat.ble (3714 * t.2.1) ((t.2.2.2.1 + 1) * Dd) &&
  Nat.ble (t.2.2.2.2 * Dd) (5570 * t.1) && Nat.ble (5570 * t.2.1) ((t.2.2.2.2 + 1) * Dd) &&
  Nat.ble (2 * 3715 * t.2.1 + Dd + 2 * t.2.2.2.2 * Dd) (2 * t.2.2.1 * Dd + 4 * t.2.2.2.1 * Dd)

/-- Consecutive rows are ordered: `B_k ≤ A_{k+1}`. -/
def chainOk : List (ℕ × ℕ × ℕ × ℕ × ℕ) → Bool
  | x :: y :: rest => Nat.ble x.2.1 y.1 && chainOk (y :: rest)
  | _ => true

/-- `D/(mD + A) - D/(mD + B) = 1/(m + A/D) - 1/(m + B/D)` for the row `(A, B, …)`. -/
noncomputable def term (m : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ) : ℝ :=
  (Dd : ℝ) / ((m : ℝ) * Dd + t.1) - (Dd : ℝ) / ((m : ℝ) * Dd + t.2.1)

/-- `λ_K(L) = Σ_{m<K} Σ_{rows of L} (1/(m + A/D) - 1/(m + B/D))`, the prime-saving exponent of the table `L`
truncated at `K`. -/
noncomputable def lam (L : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (K : ℕ) : ℝ :=
  ∑ m ∈ Finset.range K, (L.map (term m)).sum

end PiIrrationality.Bai


