-- Prove2me | Definitions.Def_DRSub4633_Supplement_transcript
-- name    : DRSub4633_Supplement_transcript
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:27:49.622275+00:00
-- url     : https://prove2.me/theorems/ed3a9abc-a9ee-4be6-8acb-ab81f5eda390
-- title:
--   The transcript of a run
-- statement:
--   For an algorithm $A$, oracles $O$ and a seed $\omega$, the transcript after $k$ steps is the list of (query, answer) pairs produced so far. It starts empty. At each step, if $A$ issues a query $q$, then $q$ and its answer are appended; if $A$ outputs a point, the transcript stays unchanged from then on.
--
--   The number of oracle calls of each kind in a run is read off from its transcript.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, p.8, and Theorem 6.3, p.37

import Mathlib
import Definitions.Def_DRSub4633_Supplement_Oracles_answer
import Definitions.Def_DRSub4633_Supplement_Strategy

namespace DRSub4633.Supplement

/-- **The transcript of a run after `k` steps.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, p.8 (oracle model) and
Theorem 6.3, p.37.

`transcript A O ω k` is the list of (query, answer) pairs produced by running the strategy `A`
with seed `ω` against the oracles `O` for `k` steps: at each step `A` either issues a query,
which is appended together with its answer `O.answer q`, or outputs a point, after which the
transcript no longer changes. -/
def transcript {n : ℕ} {Ω : Type} (A : Strategy n Ω) (O : Oracles n) (ω : Ω) :
    ℕ → List (Query n × (ℝ × EuclideanSpace ℝ (Fin n)))
  | 0 => []
  | k + 1 =>
    match A ω (transcript A O ω k) with
    | Sum.inl q => transcript A O ω k ++ [(q, O.answer q)]
    | Sum.inr _ => transcript A O ω k

end DRSub4633.Supplement


