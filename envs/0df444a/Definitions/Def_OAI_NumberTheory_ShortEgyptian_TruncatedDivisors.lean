-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
-- name    : OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:27:19.990985+00:00
-- url     : https://prove2.me/theorems/e47d1abe-e2ae-4dab-8028-73341153537e
-- title:
--   Divisors of $n$ not exceeding $X$ and their number
-- statement:
--   For a real number $X$ and a natural number $n$ the file defines:
--
--   1. **Truncated divisor set.**
--
--      $$\mathcal D_X(n)=\{\,d\in\mathbb{N}:\ d\mid n,\ d\le X\,\},$$
--
--      the positive divisors of $n$ that are at most $X$; for $n=0$ this set is empty.
--
--   2. **Truncated divisor count.** $\tau_X(n)=|\mathcal D_X(n)|$, which is at most the full divisor count $\tau(n)$.
--
--   The truncated count is the multiplicity bound in a double-counting argument. If the greedy step applied to a fraction $u/N$ with $u\ge 1$ leaves the residue $y=u\lceil N/u\rceil-N$, then $u$ divides $N+y$; hence, for fixed $N$, the number of numerators $u\le X$ producing a given residue $y$ is at most $\tau_X(N+y)$. In the surrounding development, pointwise bounds for $\tau_X(n)$ in terms of the prime factorization of $n$, and moment bounds for $\sum_{N<n\le N+Y}\tau_{e^v}(n)^r$ over short intervals, make this count effective.
--
--   **Formalization Note** The Lean names are `truncatedDivisors`, a filter of Mathlib's `Nat.divisors` (which is empty for 0), and `truncatedDivisorCount`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/TruncatedDivisors.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/TruncatedDivisors.lean by skeleton subtraction
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

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def truncatedDivisors (X : ℝ) (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun a => (a:ℝ) ≤ X

noncomputable def truncatedDivisorCount (X : ℝ) (n : ℕ) : ℕ :=
  (truncatedDivisors X n).card

end ShortEgyptian

end OAI


