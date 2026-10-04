-- Prove2me | Definitions.Def_TaoFivePrimes_Theorem51Scale
-- name    : TaoFivePrimes_Theorem51Scale
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-12T18:18:27.72861+00:00
-- url     : https://prove2.me/theorems/7b97188e-8d91-404d-9639-ba742bc9e86b
-- title:
--   Odd rectangular scale sum for Tao Theorem 5.1
-- statement:
--   For real endpoints A,B, define the finite odd interval through half-indices n with A <= 2n+1 <= B. The scale sum uses odd d in [x/(2W),x/W] and odd w in [W/2,W], with d>U and w>V, Mobius coefficient mu(d), the public centered coefficient g_V(w), and phase e(alpha*d*w). Its norm is the quantity F(W) in Section 5.3. These definitions contain no analytic estimates.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 5.3, equations (5.19)-(5.22) and the pointwise display immediately following (5.22). https://arxiv.org/html/1201.6656v4#S5.SS3

import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Mathlib

namespace TaoFivePrimes
open Finset

noncomputable def oddHalfInterval (A B : ℝ) : Finset ℤ :=
  Icc ⌈(A - 1) / 2⌉ ⌊(B - 1) / 2⌋

noncomputable def oddRealInterval (A B : ℝ) : Finset ℤ :=
  (oddHalfInterval A B).image (fun n => 2 * n + 1)

noncomputable def scaleRowCoefficient (V : ℝ) (w : ℤ) : ℂ :=
  if V < (w : ℝ) then (theorem51Centered V w.toNat : ℂ) else 0

noncomputable def scaleColumnCoefficient (U : ℝ) (n : ℤ) : ℂ :=
  if U < ((2 * n + 1 : ℤ) : ℝ) then
    (ArithmeticFunction.moebius (2 * n + 1).toNat : ℂ) else 0

noncomputable def theorem51ScaleSum (x alpha U V W : ℝ) : ℂ :=
  ∑ w ∈ oddRealInterval (W / 2) W, scaleRowCoefficient V w *
    (∑ n ∈ oddHalfInterval (x / (2 * W)) (x / W),
      expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * scaleColumnCoefficient U n)

end TaoFivePrimes


