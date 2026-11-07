-- Prove2me | Definitions.Def_OnlineCAP_nodeSet
-- name    : OnlineCAP_nodeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:34.836208+00:00
-- url     : https://prove2.me/theorems/9668306b-dbcd-4e6a-887a-ae62ccc569ef
-- title:
--   The point set S_u of a range-tree node
-- statement:
--   For a node $u=(h,j)$ of the range tree, $S_u\subseteq P$ is the set of points of $P$ whose x-rank lies in $[j2^h,(j+1)2^h)$, i.e. whose x-coordinate lies in the interval represented by $u$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1.2, p.17

import Mathlib
import Definitions.Def_OnlineCAP_xrank

namespace OnlineCAP

/-- **The point set `S_u` of a range-tree node.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1.2, p.17 (PDF p.17): "For a node u of
the range tree, denote the set of points in P whose projection lies in the interval corresponding
to u as Su ⊆ P."

`nodeSet P h j` is the set of points of `P` whose x-rank lies in `[j · 2^h, (j + 1) · 2^h)`. -/
noncomputable def nodeSet (P : Finset (ℝ × ℝ)) (h j : ℕ) : Finset ↥P :=
  Finset.univ.filter (fun p => j * 2 ^ h ≤ xrank P p.1.1 ∧ xrank P p.1.1 < (j + 1) * 2 ^ h)

end OnlineCAP


