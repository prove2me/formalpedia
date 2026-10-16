-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
-- name    : OAI_NumberTheory_ShortEgyptian_DivisorWeights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:26:38.47722+00:00
-- url     : https://prove2.me/theorems/ae7fd919-2369-4e09-b837-0881c07e6e01
-- title:
--   A polynomial-geometric series constant and divisor-power weights
-- statement:
--   Write $\tau(n)$ for the number of positive divisors of a natural number $n$.
--
--   1. **Series constant.** For $r\in\mathbb{N}$,
--
--      $$c_r=\sum_{j=0}^{\infty}(j+2)^{r}\Bigl(\frac34\Bigr)^{j},$$
--
--      a finite positive real number, since the series converges by geometric decay.
--
--   2. **Divisor weight.** For $r\in\mathbb{N}$, $\sigma\in\mathbb{R}$ and $n\in\mathbb{N}$,
--
--      $$w_{r,\sigma}(n)=\tau(n)^{r}\,n^{-\sigma}.$$
--
--   The constant $c_r$ linearizes the local factors of Euler products: in the surrounding development it is shown that $\sum_{j\ge 0}(j+1)^r x^j\le\exp(c_r x)$ for $0\le x\le 3/4$. Since $p^{-\sigma}\le 3/4$ for every prime $p$ when $\sigma\ge 1/2$, this gives Rankin-type bounds such as
--
--   $$\sum_{d\in s}w_{r,\sigma}(d)\le\exp\Bigl(c_r\sum_{p\in P,\ p\text{ prime}}p^{-\sigma}\Bigr)$$
--
--   for $\sigma\ge 1/2$, any finite set $P$ of natural numbers, and every finite set $s$ of positive integers all of whose prime factors lie in $P$. Bounds of this kind control the moments of divisor counts in the argument.
--
--   **Formalization Note** The Lean names are `momentSeriesConst`, an unconditional sum `tsum` that equals the convergent series above, and `divisorWeight`, where the power is the real power `Real.rpow`. At n = 0, Mathlib's conventions give $\tau(0)=0$ and make 0 raised to a nonzero real power equal to 0; these values play no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean by skeleton subtraction
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

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def momentSeriesConst (r : ℕ) : ℝ :=
  ∑' j : ℕ, ((j + 2 : ℕ) : ℝ) ^ r * (3 / 4 : ℝ) ^ j

noncomputable def divisorWeight (r : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ)^r * (n : ℝ)^(-σ)

end ShortEgyptian

end OAI


