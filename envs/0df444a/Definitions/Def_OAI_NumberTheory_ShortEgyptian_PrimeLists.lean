-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
-- name    : OAI_NumberTheory_ShortEgyptian_PrimeLists
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:32:24.705436+00:00
-- url     : https://prove2.me/theorems/112fb9d7-2a8c-4a57-9330-8c50873b23b1
-- title:
--   Primes in a dyadic interval and the prime pool at scale $S^{100}$
-- statement:
--   The file defines two finite sets of primes.
--
--   1. **Dyadic primes.** For $n\in\mathbb{N}$,
--
--      $$\mathcal P(n)=\{\,p\ \text{prime}:\ n<p\le 2n\,\}.$$
--
--   2. **Scale primes.** For $S\in\mathbb{R}$,
--
--      $$\mathcal P_S=\mathcal P\bigl(\lfloor S^{100}\rfloor\bigr)=\bigl\{\,p\ \text{prime}:\ \lfloor S^{100}\rfloor<p\le 2\lfloor S^{100}\rfloor\,\bigr\},$$
--
--      where $\lfloor\cdot\rfloor$ is the floor rounded to a natural number ($0$ for negative arguments).
--
--   The dyadic primes are counted through a Chebyshev-type inequality for the central binomial coefficient, $\binom{2n}{n}\le(2n)^{\lfloor\sqrt{2n}\rfloor}\,4^{\lfloor 2n/3\rfloor}\,(2n)^{|\mathcal P(n)|}$ for $n>2$, which forces $(n,2n]$ to contain many primes. In the surrounding development this yields $|\mathcal P_S|\ge S^{99}$ whenever $S\ge 2$, $\log S\ge 1$ and $4000\log S\le S$. The scale primes form the pool from which random lists of primes, all of size about $S^{100}$, are drawn when the denominators of short expansions are constructed.
--
--   **Formalization Note** The Lean names are `dyadicPrimes`, a filter of the integer interval `Ioc n (2*n)` by primality, and `scalePrimes`, which uses the natural floor `Nat.floor`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeLists.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeLists.lean by skeleton subtraction
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments

namespace OAI

namespace ShortEgyptian

open Finset
def dyadicPrimes (n : ℕ) : Finset ℕ := (Ioc n (2*n)).filter Nat.Prime

noncomputable def scalePrimes (S : ℝ) : Finset ℕ := dyadicPrimes ⌊S^100⌋₊

end ShortEgyptian

end OAI


