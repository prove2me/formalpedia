-- Prove2me | Definitions.Def_TaoFivePrimes_SmoothedSum
-- name    : TaoFivePrimes_SmoothedSum
-- status  : Definition
-- author  : @Patrick
-- created : 2026-09-07T01:46:59.980724+00:00
-- url     : https://prove2.me/theorems/148b5a7f-3883-4a9b-b998-393f05f0fae1
-- title:
--   Tao's smoothed prime exponential sum
-- statement:
--   For a real cutoff $\eta$, a natural number $q$, a real scale $x$, and a frequency $\alpha\in\mathbb R/\mathbb Z$, define
--
--   $$S_{\eta,q}(x,\alpha)=\sum_{n\geq 1}\Lambda(n)\eta(n/x)\mathbf{1}_{\gcd(n,q)=1}e^{2\pi i n\alpha}.$$
--
--   Here $\Lambda$ is the von Mangoldt function. Under the Section 4 hypotheses $x\geq1$ and $\eta$ supported in $[0,1]$, this is a finite sum. It is the exponential sum used in Tao's circle-method proof that every odd integer greater than one is a sum of at most five primes.
--
--   **Formalization Note** The sum is represented by an unrestricted `tsum` over natural numbers, including the harmless zero term $\Lambda(0)=0$. Mathlib's Fourier characters supply the exponential on the unit additive circle; `smoothedSumReal` evaluates the same function at a real representative. For arbitrary inputs outside the finite-support or summable setting, `tsum` has Lean's usual totalized meaning. Subsequent bounds establish finite support under their stated hypotheses.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, https://arxiv.org/abs/1201.6656, Section 4, equation (4.1); Section 2 summation conventions.

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Smoothed prime exponential sums

Terence Tao, "Every odd number greater than 1 is the sum of at most five primes",
https://arxiv.org/abs/1201.6656, equation (4.1), Sections 2 and 4.

The unrestricted natural-number sum agrees with the paper's positive-integer sum
because the von Mangoldt function vanishes at zero. Frequencies live on the unit
additive circle, whose normalized Haar measure is used for the global L² estimate.
-/

open scoped ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- The smoothed prime exponential sum with the coprimality restriction `(n,q)=1`. -/
noncomputable def smoothedSum (η : ℝ → ℝ) (q : ℕ) (x : ℝ) (α : AddCircle (1 : ℝ)) : ℂ :=
  ∑' n : ℕ, if n.Coprime q then (η ((n : ℝ) / x) * Λ n : ℝ) • fourier (n : ℤ) α else 0

/-- Real-frequency version of the same periodic exponential sum. -/
noncomputable def smoothedSumReal (η : ℝ → ℝ) (q : ℕ) (x α : ℝ) : ℂ :=
  smoothedSum η q x (α : AddCircle (1 : ℝ))

end TaoFivePrimes


