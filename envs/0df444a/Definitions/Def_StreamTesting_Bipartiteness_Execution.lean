-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Execution
-- name    : StreamTesting_Bipartiteness_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:56:19.569243+00:00
-- url     : https://prove2.me/theorems/422b5353-5231-4bc2-8b23-284d2fe91e15
-- title:
--   Forward-only neighborhood-query execution and transcript
-- statement:
--   Starting from an empty history, execution visits every label exactly once in the supplied order. At each position the policy sees the current label and prior history, then either receives the actual full graph neighborhood or skips it. The corresponding row is appended to the observed history. No skipped answer or future label enters a policy decision.
--
--   The complete history is the transcript used in the analysis. The query count is the number of rows carrying a neighborhood answer, including an empty answer. After the stream ends, execution is frozen.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1 and §4.2, printed p.3 / PDF p.3.

import Definitions.Def_StreamTesting_Bipartiteness_Neighborhood
import Definitions.Def_StreamTesting_Bipartiteness_Policy

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Execute exactly the first t arrivals (frozen after n), consulting G only
in the query branch. Prior history contains no future labels or skipped answers. -/
def runPrefix {n : ℕ} (G : SimpleGraph (Fin n)) (A : Policy n) (σ : Order n) :
    ℕ → History n
  | 0 => fun _ => none
  | t + 1 =>
    let h := runPrefix G A σ t
    if ht : t < n then
      let i : Fin n := ⟨t, ht⟩
      let x := σ i
      let ans := if A.1 h x then some (neighbors G x) else none
      Function.update h i (some (x, ans))
    else h

def execute {n : ℕ} (G : SimpleGraph (Fin n)) (A : Policy n) (σ : Order n) : History n :=
  runPrefix G A σ n

/-- Query count, not the number of labels exposed by answers. -/
def queryCount {n : ℕ} (T : History n) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ∃ x N, T i = some (x, some N)).card

end StreamTesting.Bipartiteness


