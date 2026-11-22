-- Prove2me | Definitions.Def_AvgPHETH_Supplement_ASet
-- name    : AvgPHETH_Supplement_ASet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:40:53.848447+00:00
-- url     : https://prove2.me/theorems/9df4c85f-d8ee-47c4-b578-4e47e704349f
-- title:
--   The oracle component $A$ as a language, with answers in $\{1,0,\bot\}$
-- statement:
--   A valid query to the help oracle $A$ has the form $q=(\langle M,d\rangle,u,1^{T^{16}})$ where $M$ is a deterministic oracle machine taking one input and $d\ge1$ witnesses, $u$ is an input, and $T\ge\max\{2,d|u|\}$. The answer is $1$, $0$ or $\bot$; invalid queries are answered $0$.
--
--   This definition turns a table of answers into a language.
--
--   **Formalization Note** The paper does not say how a three-valued answer is stored. Here each query is asked through two strings: $0q$ is in the language iff $A(q)\ne\bot$, and $1q$ is in it iff $A(q)=1$. The query $q$ is the binary tuple code of $(1^i,1^d,u,1^{T^{16}})$, where $i$ is the index of $M$ in the numbering of machines fixed by the construction.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.40 (PDF 42)

import Mathlib
import Definitions.Def_AvgPHETH_binTuple
import Definitions.Def_AvgPHETH_unary

namespace AvgPHETH.Supplement

open AvgPHETH

/-- The component `A` of the oracle, as a language, from a table `tab i d u T ∈ {1, 0, ⊥}` of answers
(`some true`, `some false`, `none`) to the queries `q = (⟨M, d⟩, u, 1^{T^16})`, where `i` is the index
of the machine `M` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.40 (PDF 42)): "A valid query to `A` has the form
`q = (⟨M, d⟩, u, 1^{T^16})` where `M` is a deterministic oracle TM taking one input and `d ≥ 1`
witnesses, `u ∈ {0,1}*` is an input, and `T ≥ max{2, d|u|}`. … Invalid queries are answered with a `0`."

**Formalization Note** The page does not say how a three-valued answer is stored in an oracle. Here
`A` answers two one-bit questions per query: the string `0 · q` is in the language iff `A(q) ∈ {0, 1}`
(the answer is not `⊥`), and `1 · q` is in it iff `A(q) = 1`, where `q` is the string
`binTuple [1^i, 1^d, u, 1^{T^16}]`. The machine code `⟨M, d⟩` is the pair of the index `i` of `M` in the
numbering of machines fixed by the construction (`OracleData.mach`) and `d`, both in unary. All other
strings are answered `0`. -/
def ASet (tab : ℕ → ℕ → List Bool → ℕ → Option Bool) : Set (List Bool) :=
  {q | ∃ (i d : ℕ) (u : List Bool) (T : ℕ), 1 ≤ d ∧ max 2 (d * u.length) ≤ T ∧
      ((q = false :: binTuple [unary i, unary d, u, unary (T ^ 16)] ∧ (tab i d u T).isSome = true) ∨
        (q = true :: binTuple [unary i, unary d, u, unary (T ^ 16)] ∧ tab i d u T = some true))}

end AvgPHETH.Supplement


