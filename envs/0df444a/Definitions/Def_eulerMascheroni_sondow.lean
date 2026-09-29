-- Prove2me | Definitions.Def_eulerMascheroni_sondow
-- name    : eulerMascheroni_sondow
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:04:55.317605+00:00
-- url     : https://prove2.me/theorems/b3aa1aab-7502-4c10-9f7b-e005a6771e56
-- title:
--   Sondow harmonic sums, logarithmic forms and double integrals
-- statement:
--   Let $d_n=\operatorname{lcm}(1,\ldots,n)$ and $H_m=\sum_{j=1}^m1/j$. Define
--   $$A_n=\sum_{i=0}^n\binom ni^2H_{n+i},$$
--   $$L_n=\sum_{k=1}^n\sum_{i=0}^{\min(k-1,n-k)}\sum_{j=i+1}^{n-i}\frac{2\binom ni^2}{j}\log(n+k),$$
--   $$I_n=\int_0^1\int_0^1\frac{[x(1-x)y(1-y)]^n}{(1-xy)(-\log(xy))}\,dy\,dx.$$
--   These are Sondow's explicit quantities. His identity $d_{2n}L_n=\log S_n$ allows the criterion to use $d_{2n}L_n$ directly, without constructing the large integer product $S_n$. Results using the integral require $n>0$.
-- source:
--   Jonathan Sondow, Criteria for Irrationality of Euler's Constant, https://arxiv.org/pdf/math/0209070 (v2, 4 October 2002). Equations (2), (6), (8), pp. 2, 3, 6; Lemma 2, p. 9.

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace EulerMascheroni.Sondow
open Finset

def d (n : ℕ) : ℕ := (Icc 1 n).lcm id

def A (n : ℕ) : ℚ :=
  ∑ i ∈ range (n + 1), (n.choose i : ℚ)^2 * harmonic (n + i)

-- Sondow (2002), equation (8); all three summation ranges are inclusive.
def L (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, ∑ i ∈ Icc 0 (min (k - 1) (n - k)),
    ∑ j ∈ Icc (i + 1) (n - i),
      2 * (n.choose i : ℝ)^2 / (j : ℝ) * Real.log (n + k : ℕ)

def I (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
    (x * (1 - x) * y * (1 - y))^n / ((1 - x*y) * (-Real.log (x*y)))

end EulerMascheroni.Sondow


