-- Prove2me | Definitions.Def_HybridXorLift_HybridAlg_cost
-- name    : HybridXorLift_HybridAlg_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:27.060714+00:00
-- url     : https://prove2.me/theorems/01382d4a-532b-4d01-bcfe-21d37bb1e400
-- title:
--   Cost of a hybrid algorithm
-- statement:
--   The **cost** of a hybrid algorithm is the largest total number of oracle calls along a root-to-leaf path:
--   $$
--   \mathrm{cost}(\text{leaf}) = 0, \qquad \mathrm{cost}(\text{node with } T \text{ queries}) = T + \max_z \mathrm{cost}(A_z).
--   $$
--   The maximum ranges over all children, whatever the probability of reaching them.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.1, p.9 (PDF p.11)

import Definitions.Def_HybridXorLift_HybridAlg

namespace HybridXorLift

/-- The cost of a hybrid algorithm (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.1, p.9 (PDF p.11)): "the largest total
number of oracle calls along a root-to-leaf path". The maximum ranges over all root-to-leaf paths
of the tree, whatever their probability. -/
def HybridAlg.cost {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} : HybridAlg ι α → ℕ
  | .halt _ => 0
  | .round T _ _ next => T + Finset.univ.sup fun z => (next z).cost

end HybridXorLift


