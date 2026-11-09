-- Prove2me | Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost
-- name    : HybridXorLift_ParallelHybridAlg_SlotsAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:51.427423+00:00
-- url     : https://prove2.me/theorems/abfe0c22-a886-4d34-85b8-51cf248ce167
-- title:
--   Parallel $q$-query hybrid algorithm
-- statement:
--   A parallel hybrid algorithm is a **parallel $q$-query hybrid algorithm** when every one of its subroutines is parallel with at most $q$ slots.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.2, p.9 (PDF p.11)

import Definitions.Def_HybridXorLift_ParallelHybridAlg

namespace HybridXorLift

/-- A parallel hybrid algorithm is a parallel `q`-query hybrid algorithm (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.2,
p.9 (PDF p.11)): every subroutine is parallel with at most `q` slots. -/
def ParallelHybridAlg.SlotsAtMost {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} (q : ℕ) :
    ParallelHybridAlg ι α → Prop
  | .halt _ => True
  | .round k _ _ next => k ≤ q ∧ ∀ y, (next y).SlotsAtMost q

end HybridXorLift


