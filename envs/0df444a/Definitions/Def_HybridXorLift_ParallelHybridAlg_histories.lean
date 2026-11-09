-- Prove2me | Definitions.Def_HybridXorLift_ParallelHybridAlg_histories
-- name    : HybridXorLift_ParallelHybridAlg_histories
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:59.259307+00:00
-- url     : https://prove2.me/theorems/d48e7b76-d84e-4e40-a957-0d68a820e8c7
-- title:
--   Histories of a parallel hybrid algorithm
-- statement:
--   The **histories** of a parallel hybrid algorithm are the sequences of measurement outcomes along paths from the root, internal or terminal:
--   $$
--   \mathcal H(\text{leaf}) = \{\varnothing\}, \qquad \mathcal H(\text{node}) = \{\varnothing\} \cup \{\, y\,h' : y \text{ an outcome},\ h' \in \mathcal H(A_y) \,\}.
--   $$
--   The root is the empty history $\varnothing$, the child $hy$ of $h$ appends $y$, and $v \prec h$ ($v$ is a strict ancestor of $h$) when $v$ is a proper prefix of $h$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.2 "Histories", p.10 (PDF p.12)

import Definitions.Def_HybridXorLift_ParallelHybridAlg
import Definitions.Def_HybridXorLift_encodeStep

namespace HybridXorLift

/-- The histories of a parallel hybrid algorithm (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.2 "Histories", p.10 (PDF p.12)): "A
history h is the sequence of measurement outcomes along a path from the root", internal or
terminal. The root `∅` is the empty list, the child `hy` of `h` is `h ++ [encodeStep y]`, and
`v` is a strict ancestor of `h` (`v ≺ h`) when `v` is a proper prefix of `h`. -/
def ParallelHybridAlg.histories {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} :
    ParallelHybridAlg ι α → Finset (List (Step ι))
  | .halt _ => {[]}
  | .round _ _ _ next =>
      insert [] (Finset.univ.biUnion fun y => (next y).histories.image (List.cons (encodeStep y)))

end HybridXorLift


