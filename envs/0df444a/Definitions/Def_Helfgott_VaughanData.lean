-- Prove2me | Definitions.Def_Helfgott_VaughanData
-- name    : Helfgott_VaughanData
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-06T10:11:27.271798+00:00
-- url     : https://prove2.me/theorems/0832d30e-08db-482e-8f07-62843a3dcac8
-- title:
--   Exact arithmetic cutoff and convolution terms for Vaughan decomposition of Goldbach sums
-- statement:
--   Define the cutoff f_(<=U)(n) = f(n) for n <= U and zero otherwise, and f_(>U) = f - f_(<=U), as real arithmetic functions. Multiplication is Dirichlet convolution. The Vaughan terms are mu_(<=U)*log, mu_(<=U)*Lambda_(<=V)*zeta, and mu_(>U)*Lambda_(>V)*zeta. These are exact full arithmetic functions, with no truncation of a subsequent exponential sum beyond its actual smoothing support. Their identity and the associated smoothed sum decomposition are separate proof obligations. These data organize the type I and type II estimates for the compact eta2 pointwise minor-arc bound.
-- source:
--   Vaughan identity, used in H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, the compact pointwise minor-arc input in section 4. Mathlib arithmetic functions and Dirichlet convolution. Written by Codex.

import Definitions.Def_Helfgott_WeightedCounting
import Definitions.Def_Helfgott_Smoothings
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace Helfgott

noncomputable def arithmeticCutoff (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ U then f n else 0
  map_zero' := by simp

noncomputable def arithmeticTail (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f-arithmeticCutoff U f

noncomputable def vaughanTypeOne (U : ℕ) : ArithmeticFunction ℝ :=
  arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.log

noncomputable def vaughanCorrection (U V : ℕ) : ArithmeticFunction ℝ :=
  arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
    arithmeticCutoff V ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta

noncomputable def vaughanTypeTwo (U V : ℕ) : ArithmeticFunction ℝ :=
  arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
    arithmeticTail V ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta

end Helfgott


