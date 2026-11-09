-- Prove2me | Definitions.Def_HybridXorLift_HybridAlg_RoundsAtMost
-- name    : HybridXorLift_HybridAlg_RoundsAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:25.169372+00:00
-- url     : https://prove2.me/theorems/101a6045-505f-4b01-a2aa-e10f57b62dc6
-- title:
--   $q$-query hybrid algorithm
-- statement:
--   A hybrid algorithm is a **$q$-query hybrid algorithm** when every subroutine makes at most $q$ calls to the oracle $O_x$. One-query hybrid algorithms are the case $q = 1$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.1, p.9 (PDF p.11)

import Definitions.Def_HybridXorLift_HybridAlg

namespace HybridXorLift

/-- A hybrid algorithm is a `q`-query hybrid algorithm (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.1, p.9 (PDF p.11)):
every subroutine makes at most `q` calls to the oracle. -/
def HybridAlg.RoundsAtMost {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} (q : ℕ) :
    HybridAlg ι α → Prop
  | .halt _ => True
  | .round T _ _ next => T ≤ q ∧ ∀ z, (next z).RoundsAtMost q

end HybridXorLift


