-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceProbability
-- name    : StreamTesting_Bipartiteness_Supplement_SequenceProbability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:59:00.188015+00:00
-- url     : https://prove2.me/theorems/dae8dc0b-dec1-4604-ba19-a4481a176d23
-- title:
--   Sequence output-event probability
-- statement:
--   For a fixed real sequence $f$, an algorithm $A$ and output event $E$, define
--
--   $$\Pr_A[E\mid f]=\sum_s\mu(s)\mathbf1\{E(\mathrm{output}(f,A_s))\}.$$
--
--   The sum is over the finite private seed space. The event is evaluated on actual execution, with no arbitrary success-probability function or integration default. No random arrival order is introduced for sequence problems.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1, printed/PDF p.3; Theorem 22 p.27; Theorem 24 p.29.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceExecution

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def seqProb {m : ℕ} {α : Type} (f : Fin m → ℝ) (A : SeqAlgorithm m α)
    (E : α → Prop) : ℝ := by
  classical
  exact ∑ s : Fin A.seedCount, if E (seqOutput f (A.policy s)) then (A.coins s).toReal else 0

end StreamTesting.Bipartiteness.Supplement


