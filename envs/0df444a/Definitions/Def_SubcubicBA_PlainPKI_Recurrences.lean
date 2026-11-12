-- Prove2me | Definitions.Def_SubcubicBA_PlainPKI_Recurrences
-- name    : SubcubicBA_PlainPKI_Recurrences
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:42:15.177956+00:00
-- url     : https://prove2.me/theorems/fc396164-1653-4d1c-9b78-b0a7039d6dd8
-- title:
--   The bit and round recurrences of §12 with the parameter rule of Theorem 9
-- statement:
--   The complexity recurrences of §12, with explicit constants.
--
--   Let $p=(\sqrt{13}-1)/2$, the positive root of $3-x-x^2=0$. For constants $B,c$ and token size $\kappa$, the parameter rule of p. 33 is
--   $$(m,b)=\begin{cases}(n,1)&n\le B\kappa^4,\\(\lceil c(\kappa n)^{p-1}\rceil,\lceil c(\kappa n)^{p-1}\rceil)&\text{otherwise.}\end{cases}$$
--
--   1. `BitRecurrence C₀ B c κ f`: $f\ge0$ is nondecreasing, $f(1)=0$, and for every $n\ge2$
--   $$f(n)\le2f(\lceil n/2\rceil)+C_0\Big(nm\kappa+\frac{\kappa nb^2}{m}+\frac{\kappa n^{1/3}b^3}{m^{1/3}}+\frac{\kappa n^2\log n}{bm^2}+\frac{\kappa n^{4/3}\log n}{m^{4/3}}\Big)+C_0\Big(\frac{n}{mb}+\Big(\frac nm\Big)^{1/3}\Big)\kappa f(\lceil n/m\rceil).$$
--   2. `RoundRecurrence C₀ B c κ R`: $R\ge0$, $R(1)\le1$, and for every $n\ge2$
--   $$R(n)\le2R(\lceil n/2\rceil)+C_0\Big(\frac nm\Big)^{1/3}\big(b+R(\lceil n/m\rceil)\big).$$
--
--   Logarithms are binary. These are the per-party bit complexity and the round complexity of ByzantineAgreement as derived on pp. 31–35; they state Theorems 9 and 10.
--
--   **Formalization Note** The $O(\cdot)$ terms of the source are replaced by one constant $C_0$, and the parameters are rounded up to integers.
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), §12 (pp. 31–36): recurrence after line 995 (p. 32), parameter rule (p. 33), recurrence after line 1045 (p. 35)

import Mathlib

set_option autoImplicit false

namespace SubcubicBA.PlainPKI

/-! # The complexity recurrences of §12 (pp. 31–36)

`p = (√13 - 1)/2`, the positive root of `3 - x - x² = 0` (p. 34). The parameter rule of the
proof of Theorem 9 (p. 33), used again in Theorem 10 (p. 35): `(m, b) = (n, 1)` if `n ≤ B κ⁴`,
and `(m, b) = (⌈c (κ n)^{p-1}⌉, ⌈c (κ n)^{p-1}⌉)` otherwise (rounded up to integers). Logarithms
are binary. -/

/-- The exponent `p = (√13 - 1)/2`. -/
noncomputable def pExp : ℝ := (Real.sqrt 13 - 1) / 2

/-- The parameter `m(n)` for constants `B`, `c` and token size `κ`. -/
noncomputable def paramM (B c : ℝ) (κ n : ℕ) : ℕ :=
  if (n : ℝ) ≤ B * (κ : ℝ) ^ 4 then n else ⌈c * ((κ : ℝ) * n) ^ (pExp - 1)⌉₊

/-- The parameter `b(n)` for constants `B`, `c` and token size `κ`. -/
noncomputable def paramB (B c : ℝ) (κ n : ℕ) : ℕ :=
  if (n : ℝ) ≤ B * (κ : ℝ) ^ 4 then 1 else ⌈c * ((κ : ℝ) * n) ^ (pExp - 1)⌉₊

/-- `f` satisfies the per-party bit recurrence of p. 32 (display after line 995), with the
explicit constant `C₀` in place of every `O(·)`, at the parameter rule `(B, c)`: `f` is
nonnegative and nondecreasing, `f(1) = 0`, and for every `n ≥ 2`, with `m = m(n)`, `b = b(n)`,

`f(n) ≤ 2 f(⌈n/2⌉) + C₀ (n m κ + κ n b²/m + κ n^{1/3} b³/m^{1/3} + κ n² log n/(b m²)
          + κ n^{4/3} log n/m^{4/3}) + C₀ (n/(m b) + (n/m)^{1/3}) κ f(⌈n/m⌉)`. -/
def BitRecurrence (C₀ B c : ℝ) (κ : ℕ) (f : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ f n) ∧ Monotone f ∧ f 1 = 0 ∧
  ∀ n : ℕ, 2 ≤ n →
    let m : ℝ := paramM B c κ n
    let b : ℝ := paramB B c κ n
    let N : ℝ := n
    let K : ℝ := κ
    f n ≤ 2 * f ⌈N / 2⌉₊ +
      C₀ * (N * m * K + K * N * b ^ 2 / m + K * N ^ ((1 : ℝ) / 3) * b ^ 3 / m ^ ((1 : ℝ) / 3) +
        K * N ^ 2 * Real.logb 2 N / (b * m ^ 2) +
        K * N ^ ((4 : ℝ) / 3) * Real.logb 2 N / m ^ ((4 : ℝ) / 3)) +
      C₀ * (N / (m * b) + (N / m) ^ ((1 : ℝ) / 3)) * K * f ⌈N / m⌉₊

/-- `R` satisfies the round recurrence of p. 35 (display after line 1045), with the explicit
constant `C₀` in place of the `O(·)`, at the parameter rule `(B, c)`: `R ≥ 0`, `R(1) ≤ 1`, and for
every `n ≥ 2`, `R(n) ≤ 2 R(⌈n/2⌉) + C₀ (n/m)^{1/3} (b + R(⌈n/m⌉))`. -/
def RoundRecurrence (C₀ B c : ℝ) (κ : ℕ) (R : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ R n) ∧ R 1 ≤ 1 ∧
  ∀ n : ℕ, 2 ≤ n →
    let m : ℝ := paramM B c κ n
    let b : ℝ := paramB B c κ n
    let N : ℝ := n
    R n ≤ 2 * R ⌈N / 2⌉₊ + C₀ * (N / m) ^ ((1 : ℝ) / 3) * (b + R ⌈N / m⌉₊)

end SubcubicBA.PlainPKI


