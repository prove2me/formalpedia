-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_CommonSearch
-- name    : StreamTesting_Bipartiteness_Supplement_CommonSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:00:28.380681+00:00
-- url     : https://prove2.me/theorems/90c7cccd-ec0a-497a-96f0-52f2c151ce44
-- title:
--   Common-element search correctness
-- statement:
--   A common-element searcher at length $n$ and parameter $\varepsilon$ is one input-independent forward-only algorithm $T$, selected before the input values, such that every strictly increasing pair $A,B$ satisfying $|I(A,B)|\ge\varepsilon n$ obeys
--
--   $$\Pr[T(A\text{ then }B)\text{ outputs a value in }I(A,B)]\ge2/3.$$
--
--   No correctness requirement is imposed without the intersection promise. Query caps separately range over all sorted input pairs, so the resource bound also holds off the promise.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 22, printed/PDF p.27, proof pp.27–29.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_CommonElement
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceProbability

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def CommonSearcher (n : ℕ) (ε : ℝ) (T : SeqAlgorithm (2 * n) (Option ℝ)) : Prop :=
  ∀ A B : Fin n → ℝ, StrictMono A → StrictMono B →
    ε * (n : ℝ) ≤ ((commonValues A B).card : ℝ) →
    (2 : ℝ) / 3 ≤ seqProb (joinSequences A B) T (CommonValueOutput A B)

end StreamTesting.Bipartiteness.Supplement


