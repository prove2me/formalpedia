-- Prove2me | Definitions.Def_ChenPairedDomination_Interval_PrefixData
-- name    : ChenPairedDomination_Interval_PrefixData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T01:26:24.853995+00:00
-- url     : https://prove2.me/theorems/3c1ff6ec-67fa-4472-b1c4-d5b8eed7683f
-- title:
--   Ordered prefixes, earliest neighbors and the last earlier nonneighbor
-- statement:
--   For a graph on Fin n, prefixVertices r is the set of indices strictly below r, hence the paper’s first r vertices. firstNeighbor G i scans the finite vertex list in increasing order and returns the first earlier neighbor; if there is none it returns i. In particular the first vertex returns itself. lastNonneighbor G i scans in decreasing order and returns the last earlier nonneighbor, as an Option index. Its value none represents the paper’s external sentinel u_0, distinct from index 0, which represents u_1. These are searches on the given graph, not arbitrary functions constrained by hypotheses. The fallback for invalid graphs imposes no extra assumption on the source domain.
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, §3, p. 11

import Definitions.Def_ChenPairedDomination_Interval_PairedDomination
import Definitions.Def_ChenPairedDomination_Interval_OrderedRepresentation

namespace ChenPairedDomination.Interval

/-- `prefixVertices r` has the first `r` vertices: paper V_r. -/
def prefixVertices {n : ℕ} (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val < r)

/-- Finite increasing search, returning the vertex itself if no earlier neighbor exists. -/
noncomputable def firstNeighbor {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) : Fin n := by
  classical
  exact ((List.finRange n).filter (fun k => decide (k < i ∧ G.Adj k i))).headD i

/-- Finite decreasing search; `none` is the paper's external sentinel u_0. -/
noncomputable def lastNonneighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (i : Fin n) : Option (Fin n) := by
  classical
  exact (List.finRange n).reverse.find? (fun k => decide (k < i ∧ ¬ G.Adj k i))

end ChenPairedDomination.Interval


