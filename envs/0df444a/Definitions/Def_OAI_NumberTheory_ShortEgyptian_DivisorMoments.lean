-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
-- name    : OAI_NumberTheory_ShortEgyptian_DivisorMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:29:27.320322+00:00
-- url     : https://prove2.me/theorems/9235ba0b-8b17-4c4c-a340-a5aaaac02113
-- title:
--   Smooth prefixes and the exponents in a moment bound for truncated divisor counts
-- statement:
--   Here $\log$ is the natural logarithm, $\lfloor\cdot\rfloor$ is the floor rounded to a natural number, and a positive integer is $y$-smooth if all its prime factors are at most $y$. Let $c_r=\sum_{j\ge 0}(j+2)^r(3/4)^j$ be the series constant and $B(T)=8+4\log\bigl(1+\log T/\log 2\bigr)$ the prime-reciprocal bound.
--
--   1. **Smooth prefixes.** For $R,v,T\in\mathbb{R}$,
--
--      $$\mathcal S(R,v,T)=\bigl\{\,d\in\mathbb{N}:\ 1\le d\le\lfloor R\rfloor,\ d\text{ is }\lfloor T\rfloor\text{-smooth},\ e^{v/5}\le d\,\bigr\}.$$
--
--   2. **Prefix exponent.** For $v,W\in\mathbb{R}$,
--
--      $$\beta(v,W)=\Bigl(1+\log\frac{W}{v}\Bigr)\,v.$$
--
--   3. **Pointwise exponent.** For $r\in\mathbb{N}$ and $v,W,z\in\mathbb{R}$,
--
--      $$E_{\mathrm{pt}}(r,v,W,z)=r\Bigl(z\log\Bigl(1+\frac{W}{\log 2}\Bigr)+\frac{\beta(v,W)}{\log z}\Bigr).$$
--
--   4. **Band exponent.** For $r\in\mathbb{N}$ and $v,W,t\in\mathbb{R}$, with $\lambda=\dfrac{\log(v/t)}{10t}$,
--
--      $$E_{\mathrm{band}}(r,v,W,t)=\frac{r\,\beta(v,W)}{t}-\frac{\lambda v}{5}+c_r\,\bigl(e^{2t}\bigr)^{\lambda}\,B\bigl(e^{2t}\bigr).$$
--
--   These quantities organize a bound for the moments $\sum_{N<n\le N+Y}\tau_{e^v}(n)^r$, where $\tau_X(n)$ counts the divisors of $n$ that are at most $X$ and $\log n\le W$ on the range of summation. Each $n$ is split as $n=de$, where the prefix $d\le\sqrt Y$ has all prime factors at most some prime $p$ and $e$ has all prime factors at least $p$; then $\tau_{e^v}(n)^r\le\tau(d)^r\exp\bigl(r\beta(v,W)/\log p\bigr)$, with $\tau(d)$ the number of divisors of $d$. The exponent $E_{\mathrm{pt}}$ is $r$ times the exponent of a pointwise bound for $\tau_{e^v}(n)$, and $E_{\mathrm{band}}$ is the exponent obtained, via Rankin's trick with parameter $\lambda$ and the constraint $d\ge e^{v/5}$, for prefixes whose prime factors are at most $e^{2t}$. The smooth prefixes are the sets of such $d$ over which these contributions are summed, and the moment bound is derived under hypotheses requiring $E_{\mathrm{band}}\le 0$ on a range of $t$ and $E_{\mathrm{pt}}$ to be sufficiently smaller than $v$.
--
--   **Formalization Note** The Lean names are `smoothPrefixes` (smoothness is expressed as membership in `Nat.factoredNumbers` of the set of primes up to the floor of T), `momentB`, `momentPoint` and `momentBandExp`. Division by zero and logarithms of non-positive numbers follow Lean's conventions, but the exponents are only used with v, t and z positive and v below W.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DivisorMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DivisorMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def smoothPrefixes (R v T : ℝ) : Finset ℕ :=
  (Icc 1 ⌊R⌋₊).filter fun d =>
    d ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) ∧ Real.exp (v/5) ≤ d

noncomputable def momentB (v W : ℝ) : ℝ := (1+Real.log (W/v))*v

noncomputable def momentPoint (r : ℕ) (v W z : ℝ) : ℝ :=
  (r:ℝ)*(z*Real.log (1+W/Real.log 2)+momentB v W/Real.log z)

noncomputable def momentBandExp (r : ℕ) (v W t : ℝ) : ℝ :=
  (r:ℝ)*momentB v W/t - (Real.log (v/t)/(10*t))*v/5 +
    momentSeriesConst r * (Real.exp (2*t)^(Real.log (v/t)/(10*t)) * primeRecipBound (Real.exp (2*t)))

end ShortEgyptian

end OAI


