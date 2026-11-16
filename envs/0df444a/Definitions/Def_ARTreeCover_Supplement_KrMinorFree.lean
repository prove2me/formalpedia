-- Prove2me | Definitions.Def_ARTreeCover_Supplement_KrMinorFree
-- name    : ARTreeCover_Supplement_KrMinorFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:01:45.940255+00:00
-- url     : https://prove2.me/theorems/d4e0540a-81bc-4eb9-8478-e410445f2822
-- title:
--   $K_r$-minor-free weighted graphs
-- statement:
--   A weighted graph $G$ is **$K_r$-minor-free** if the complete graph $K_r$ on $r$ vertices is not a minor of $G$, where a minor is obtained by vertex deletions, edge deletions and edge contractions.
--
--   $K_r$-minor-free graphs include planar graphs ($r=5$) and graphs of bounded treewidth; Theorems 14, 15, 22, 27 and 41 concern them.
--
--   **Formalization Note** Minors are the mission's published weighted minors (branch-set model). Weights play no role: any weighted graph on $r$ vertices whose underlying graph is complete counts. For $r=0$ no graph is $K_0$-minor-free, and $K_1$-minor-free means that $G$ has no vertex.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), §2, p.9 (PDF p.12); used from Theorem 9, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_WMinor

namespace ARTreeCover.Supplement

open ARTreeCover

/-- `KrMinorFree r G`: the weighted graph `G` is `K_r`-minor-free, i.e. no weighted graph whose
underlying graph is the complete graph on `r` vertices is a minor of `G`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), §2, p.9 (PDF p.12): "A minor of G is a graph
that is obtained from G by a sequence of vertex deletions, edge deletions and edge contractions";
`K_r`-minor-free graphs are used from Theorem 9, p.12 (PDF p.15), on.

**Formalization Note.** Minors are the published weighted minors `ARTreeCover.WMinor` (branch-set
model). Weights play no role here: the complete graph `⊤` on `Fin r` with any weights that are
witnessed by edges of `G` counts. For `r = 0` no graph is `K_0`-minor-free, and `K_1`-minor-free
means `V = ∅`. -/
def KrMinorFree {V : Type} (r : ℕ) (G : WGraph V) : Prop :=
  ¬ ∃ H : WGraph (Fin r), H.graph = ⊤ ∧ WMinor H G

end ARTreeCover.Supplement


