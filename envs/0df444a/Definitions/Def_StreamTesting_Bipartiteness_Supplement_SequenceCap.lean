-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceCap
-- name    : StreamTesting_Bipartiteness_Supplement_SequenceCap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:59:41.342987+00:00
-- url     : https://prove2.me/theorems/2592d395-8546-401f-906d-02abcaf7c18b
-- title:
--   Worst-run sequence query bound
-- statement:
--   An algorithm $A$ has worst-run cap $q$ on input domain $D$ when
--
--   $$\mathrm{queries}(f,A_s)\le q$$
--
--   for every $f\in D$ and every private seed of positive probability. This bounds actual queries rather than their expectation. It permits truncation of a search while retaining a uniform resource guarantee.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1, printed/PDF p.3; Theorem 22 proof p.29; Theorem 24 proof pp.35–36.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceExecution

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def SeqQueryCap {m : ℕ} {α : Type} (D : (Fin m → ℝ) → Prop)
    (A : SeqAlgorithm m α) (q : ℕ) : Prop :=
  ∀ s : Fin A.seedCount, A.coins s ≠ 0 → ∀ f : Fin m → ℝ, D f →
    seqQueryCount (seqExecute f (A.policy s)) ≤ q

end StreamTesting.Bipartiteness.Supplement


