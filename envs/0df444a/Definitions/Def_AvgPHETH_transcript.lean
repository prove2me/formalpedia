-- Prove2me | Definitions.Def_AvgPHETH_transcript
-- name    : AvgPHETH_transcript
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:44.296187+00:00
-- url     : https://prove2.me/theorems/073f0f93-606b-46c7-b64d-e95550b94a6f
-- title:
--   The encoded transcript $(\tau_{<i},q_i)$
-- statement:
--   For a query sequence $q_1,\dots,q_R$ and a response function $f$, with $a_j=f(q_j)$, this is the encoding of the transcript $(q_1,a_1,\dots,q_{i-1},a_{i-1},q_i)=(\tau_{<i},q_i)$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.2, p.20 (PDF 22)

import Mathlib
import Definitions.Def_AvgPHETH_binTuple

namespace AvgPHETH

/-- The encoded transcript `(τ_{<i}, q_i) = (q₁, a₁, …, q_{i−1}, a_{i−1}, q_i)`, with `a_j = f(q_j)`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.2, p.20 (PDF 22)). The index `i` counts from `0` here. -/
def transcript {R : ℕ} (f : List Bool → List Bool) (q : Fin R → List Bool) (i : Fin R) : List Bool :=
  binTuple (((List.ofFn q).take (i : ℕ)).flatMap (fun p => [p, f p]) ++ [q i])

end AvgPHETH


