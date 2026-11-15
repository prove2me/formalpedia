-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_PatternTester
-- name    : StreamTesting_Bipartiteness_Supplement_PatternTester
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:01:56.663031+00:00
-- url     : https://prove2.me/theorems/697ece38-90f9-4258-b75a-207afd75e4b2
-- title:
--   One-sided 132-freeness tester correctness
-- statement:
--   A one-sided tester $A$ accepts every 132-free real sequence with probability one and rejects every $\varepsilon$-far real sequence with probability at least $2/3$:
--
--   $$f\text{ free}\Rightarrow\Pr[\mathrm{accept}]=1,\qquad f\text{ far}\Rightarrow\Pr[\mathrm{accept}]\le1/3.$$
--
--   All real sequences, including those with repeated values, are covered. The index order is fixed and no hidden monotone subsequence, matching, or structural advice is passed to the policy.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 24 and Remark 25, printed/PDF p.29; proof pp.35–36.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_PatternFarness
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceProbability

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def OneSided132Tester {n : ℕ} (ε : ℝ) (A : SeqAlgorithm n Bool) : Prop :=
  ∀ f : Fin n → ℝ,
    (Free132 f → seqProb f A (fun b => b = true) = 1) ∧
    (Far132 f ε → seqProb f A (fun b => b = true) ≤ (1 : ℝ) / 3)

end StreamTesting.Bipartiteness.Supplement


