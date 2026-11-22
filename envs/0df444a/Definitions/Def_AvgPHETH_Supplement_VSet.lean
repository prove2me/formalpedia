-- Prove2me | Definitions.Def_AvgPHETH_Supplement_VSet
-- name    : AvgPHETH_Supplement_VSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:40:13.171057+00:00
-- url     : https://prove2.me/theorems/0d562dd0-2c69-4518-832b-871b7036e6ed
-- title:
--   The oracle component $V=(V_k)_k$ as a language
-- statement:
--   Given an assignment to the construction variables, the oracle $V_k$ takes a tuple $(x,y_1,\dots,y_k)$ where $(k,|x|)$ is active and $(y_1,\dots,y_k)$, $y_j\in Y_j(|x|)$, names a leaf of the selector tree $T^k_x$, and outputs $T^k_x(y_1,\dots,y_k)$. Invalid queries are answered with $0$.
--
--   This definition is the language of all encoded valid queries, for all $k$, that are answered $1$.
--
--   **Formalization Note** The paper leaves the layout of a query to "an appropriate encoding" in which valid entries have length $O(|x|)$. Here the query $(x,y_1,\dots,y_k)$ to $V_k$ is the binary tuple code (each bit doubled, each component ended by $01$) of $(1^k,x,y_1,\dots,y_k)$, of length $O(|x|)$ for fixed $k$ and decodable in linear time.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.38–39 (PDF 40–41)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_treeVal
import Definitions.Def_AvgPHETH_Supplement_IsActive
import Definitions.Def_AvgPHETH_Supplement_aPar
import Definitions.Def_AvgPHETH_binTuple
import Definitions.Def_AvgPHETH_unary

namespace AvgPHETH.Supplement

open AvgPHETH

/-- The component `V` of the oracle, as a language: the oracles `V_k`, `k ∈ ℕ`, determined by an
assignment `β` to the construction variables
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.38–39 (PDF 40–41)): "`V_k` takes as input a tuple `(x, y₁, …, y_k)`
where `(k, |x|)` is active and `(y₁, …, y_k)` names a leaf of `T^k_x`, and outputs `T^k_x(y₁, …, y_k)`. …
Invalid queries are answered with `0`."

**Formalization Note** The page leaves the layout of a query to "an appropriate encoding" with valid
entries of length `O(|x|)`. Here the query `(x, y₁, …, y_k)` to `V_k` is the string
`binTuple [1^k, x, y₁, …, y_k]` (the published injective binary tuple code, which doubles each bit and
ends each component with `01`): its length is `2(k + |x| + ∑ a_j(|x|)) + 2(k + 2) = O(|x|)` for fixed
`k`, and it is decoded in linear time. -/
def VSet (ε : ℕ → ℝ) (β : CVar → List Bool) : Set (List Bool) :=
  {q | ∃ (k : ℕ) (x : List Bool) (ys : List (List Bool)),
      q = binTuple (unary k :: x :: ys) ∧ IsActive ε k x.length ∧ ys.length = k ∧
      (∀ (i : ℕ) (h : i < ys.length), (ys[i]).length = aPar ε (i + 1) x.length) ∧
      treeVal β k x ys = true}

end AvgPHETH.Supplement


