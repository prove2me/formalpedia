-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
-- name    : OAI_NumberTheory_ShortEgyptian_SmoothBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:29:12.460283+00:00
-- url     : https://prove2.me/theorems/3bdf299c-3dcb-4bb9-aa43-d8ed34b044ac
-- title:
--   An explicit bound for sums of prime reciprocals and the constant $\zeta(41/40)$
-- statement:
--   Here $\log$ is the natural logarithm.
--
--   1. **Prime-reciprocal bound.** For $T\in\mathbb{R}$,
--
--      $$B(T)=8+4\log\Bigl(1+\frac{\log T}{\log 2}\Bigr).$$
--
--   2. **Zeta constant.**
--
--      $$c_{\mathrm{sm}}=\sum_{n=1}^{\infty}n^{-41/40}=\zeta\Bigl(\frac{41}{40}\Bigr),$$
--
--      a finite constant because the exponent exceeds $1$.
--
--   The function $B$ is an explicit Mertens-type majorant: in the surrounding development it is shown that $\sum_{p\le T}1/p\le B(T)$ for every natural number $T\ge 2$, the sum running over primes. It feeds the Euler-product estimates for divisor moments, for instance $\sum_{1\le d\le T}\tau(d)^r/d\le\exp\bigl(c_rB(T)\bigr)$ for real $T\ge 2$, where $\tau(d)$ is the number of divisors of $d$ and $c_r=\sum_{j\ge 0}(j+2)^r(3/4)^j$. The constant $c_{\mathrm{sm}}$ enters the Rankin-type bound for the sum of $1/d$ over $T$-smooth integers $d\ge e^{v/5}$ (integers whose prime factors are all at most $T$), through a term proportional to $T^{1/8}c_{\mathrm{sm}}$.
--
--   **Formalization Note** The Lean names are `primeRecipBound` and `smallSmoothConst`. The latter is the unconditional sum `tsum` over all natural numbers n of the real power of n with exponent -41/40; its n = 0 term is 0 by the convention for real powers of 0, so it equals the series starting at n = 1.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SmoothBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/SmoothBounds.lean by skeleton subtraction
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

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def primeRecipBound (T : ℝ) : ℝ :=
  8+4*Real.log (1+Real.log T/Real.log 2)

noncomputable def smallSmoothConst : ℝ := ∑' n : ℕ, (n:ℝ)^(-41/40:ℝ)

end ShortEgyptian

end OAI


