-- Prove2me | Definitions.Def_PolyEulerFlow_fieldEval
-- name    : PolyEulerFlow_fieldEval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:16.221262+00:00
-- url     : https://prove2.me/theorems/77957fe8-dce9-4a5b-b568-fb1d60871766
-- title:
--   Evaluation of rational polynomial fields, bit lengths and rounded unit-step orbits
-- statement:
--   A **rational polynomial field** $F(h,z)$ on $\mathbb R^N$ is a family of $N$ polynomials with rational coefficients in the variables $h,z_1,\dots,z_N$; it does not see the input $x$. A **rational polynomial initialization** $c(x,h)$ is a family of $N$ polynomials with rational coefficients in $x$ and $h$. Both are evaluated at real arguments.
--
--   A real number has **bit length at most** $B$ when it is a rational whose numerator and denominator are both less than $2^B$ in absolute value.
--
--   A **unit-step orbit rounded to $b$ fractional bits** (proof of Theorem 1, p.44) is a sequence $w$ with $w_0=c(x,h)$ exactly, every later coordinate an integer multiple of $2^{-b}$, and
--   $$\|w_{k+1}-(w_k+F(h,w_k))\|_\infty\le 2^{-b}.$$
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Theorem 1, p.2 (PDF 4); proof of Theorem 1, p.44 (PDF 46)

import Mathlib

namespace PolyEulerFlow

/-- The value `F(h, z)` of a rational polynomial map, with `none` as the variable `h` (Theorem 1, p.2).
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), p.2.
**Formalization Note.** `F` does not see the input `x`, and its coefficients are rational. -/
noncomputable def fieldEval {N : ℕ} (F : Fin N → MvPolynomial (Option (Fin N)) ℚ) (h : ℝ) (z : Fin N → ℝ) : Fin N → ℝ :=
  fun i => MvPolynomial.aeval (fun v : Option (Fin N) => v.elim h z) (F i)

/-- The value `c(x, h)` of a rational polynomial initialization; variable `0` is `x`, variable `1` is `h`. -/
noncomputable def initEval {N : ℕ} (c : Fin N → MvPolynomial (Fin 2) ℚ) (x : ℕ) (h : ℝ) : Fin N → ℝ :=
  fun i => MvPolynomial.aeval ![(x : ℝ), h] (c i)

/-- The real `v` is a rational whose numerator and denominator have fewer than `B` bits. -/
def HasBitLengthLE (v : ℝ) (B : ℕ) : Prop :=
  ∃ r : ℚ, (r : ℝ) = v ∧ r.num.natAbs < 2 ^ B ∧ r.den < 2 ^ B

/-- A unit-step sequence rounded to `b` fractional bits (proof of Theorem 1, p.44): exact start, every later coordinate a
multiple of `2^{-b}`, and each update within `2^{-b}` of the exact unit-step update. -/
def IsRoundedOrbit {N : ℕ} (f : (Fin N → ℝ) → Fin N → ℝ) (z0 : Fin N → ℝ) (b : ℕ) (w : ℕ → Fin N → ℝ) : Prop :=
  w 0 = z0 ∧ ∀ k, (∀ i, ∃ n : ℤ, w (k + 1) i = (n : ℝ) * (2 : ℝ) ^ (-(b : ℤ))) ∧
    ‖w (k + 1) - (w k + f (w k))‖ ≤ (2 : ℝ) ^ (-(b : ℤ))

end PolyEulerFlow


