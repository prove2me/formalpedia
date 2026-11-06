-- Prove2me | Definitions.Def_MetricMinTest_Tester_hist
-- name    : MetricMinTest_Tester_hist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:50.893245+00:00
-- url     : https://prove2.me/theorems/2eafdbbe-1b31-4842-a48c-e842b5e2b084
-- title:
--   History of a sequential tester
-- statement:
--   Given $\xi$ and an observation table $\omega$, the history after $n$ steps is the list of (index, observation) pairs produced so far. At each step, if the tester stops the history is unchanged; if it queries $j$, the pair $(j,\omega_{j,c})$ is appended, where $c$ is the number of earlier queries to $j$. Each query therefore receives a fresh entry of the stream of $j$.
--
--   **Formalization Note** Defined by recursion on $n$; the first entry of every stream has index $0$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Tester

namespace MetricMinTest

/-- **History of a sequential tester after `n` steps.** Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2 p.6.

**Formalization Note.** In the stack-of-streams model (`streamLaw`), the history after `n` steps
is built recursively: if `next` stops, the history stays the same; if it queries `j`, the pair
`(j, ω j c)` is appended, where `c` is the number of earlier queries to `j` (0-based). Each
query thus receives a fresh entry of stream `j`. -/
def Tester.hist {ι : Type} [DecidableEq ι] (T : Tester ι) (ξ : T.Ξ) (ω : ι → ℕ → ℝ) :
    ℕ → List (ι × ℝ)
  | 0 => []
  | n + 1 =>
    match T.next ξ (Tester.hist T ξ ω n) with
    | none => Tester.hist T ξ ω n
    | some j => Tester.hist T ξ ω n ++
        [(j, ω j ((Tester.hist T ξ ω n).countP (fun p => decide (p.1 = j))))]

end MetricMinTest


