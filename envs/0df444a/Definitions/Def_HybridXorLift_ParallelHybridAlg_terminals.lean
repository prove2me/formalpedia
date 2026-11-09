-- Prove2me | Definitions.Def_HybridXorLift_ParallelHybridAlg_terminals
-- name    : HybridXorLift_ParallelHybridAlg_terminals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:56.027433+00:00
-- url     : https://prove2.me/theorems/27395788-2dd4-4968-bcca-094470c46bcf
-- title:
--   Terminal histories (terminal transcripts)
-- statement:
--   The **terminal histories** of a parallel hybrid algorithm are the sequences of measurement outcomes along its root-to-leaf paths. On an input $x$ the algorithm ends at exactly one of them, its **terminal transcript**.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.2, p.10 (PDF p.12); §5.3, p.19 (PDF p.21)

import Definitions.Def_HybridXorLift_ParallelHybridAlg
import Definitions.Def_HybridXorLift_encodeStep

namespace HybridXorLift

/-- The terminal histories (terminal transcripts) of a parallel hybrid algorithm (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.2,
p.10 (PDF p.12), and §5.3, p.19 (PDF p.21)): the sequences of measurement outcomes along the
root-to-leaf paths. -/
def ParallelHybridAlg.terminals {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} :
    ParallelHybridAlg ι α → Finset (List (Step ι))
  | .halt _ => {[]}
  | .round _ _ _ next =>
      Finset.univ.biUnion fun y => (next y).terminals.image (List.cons (encodeStep y))

end HybridXorLift


