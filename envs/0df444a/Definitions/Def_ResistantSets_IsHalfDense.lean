-- Prove2me | Definitions.Def_ResistantSets_IsHalfDense
-- name    : ResistantSets_IsHalfDense
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:20.166656+00:00
-- url     : https://prove2.me/theorems/2574a28c-a6fd-45f9-84b2-c8cb68b62a35
-- title:
--   Half-dense set: $|S|=2^{n-1}$
-- statement:
--   If $S\subseteq\{0,1\}^n$ is non-polar then $|S|\le 2^{n-1}$, and when equality holds $S$ is **half-dense**:
--   $$
--   |S|=2^{n-1}.
--   $$
--
--   Half-dense strictly non-polar sets are the strictly non-polar sets of maximum possible cardinality, the class classified by the main theorem.
--
--   **Formalization Note** The condition is written $2|S|=2^n$ to avoid natural-number subtraction. The paper uses the word for non-polar sets; the predicate is the cardinality condition alone, and every statement using it also assumes non-polarity.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.6, §1.2 ("Observe that if S is non-polar, then |S| ≤ 2ⁿ⁻¹, and if equality holds, we say that S is half-dense")

import Mathlib

namespace ResistantSets

/-- **Half-dense set** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.2, p.6): "Observe that if S is non-polar, then |S| ≤ 2ⁿ⁻¹, and if
equality holds, we say that S is half-dense."

**Formalization Note** `|S| = 2ⁿ⁻¹` is written `2 · |S| = 2ⁿ` to avoid natural-number
subtraction. The page defines the word for non-polar sets; the predicate is the cardinality
condition alone, and every statement that uses it also assumes non-polarity. -/
def IsHalfDense {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  2 * S.card = 2 ^ n

end ResistantSets


