-- Prove2me | Definitions.Def_HeilmanMax3Cut_MaxKCutHardSimple
-- name    : HeilmanMax3Cut_MaxKCutHardSimple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:03.745209+00:00
-- url     : https://prove2.me/theorems/8b70c625-7800-4b74-8749-2fdb6cd61460
-- title:
--   $(c,s)$-hardness of MAX-$k$-CUT on simple graphs
-- statement:
--   For a graph $G$ and a colouring $\chi$ of its vertices with $k$ colours, let $\mathrm{cut}_\chi(G)$ be the number of edges whose endpoints receive different colours, and $|E(G)|$ the number of edges. MAX-$k$-CUT on simple graphs is **$(c,s)$-hard** when it is NP-hard to distinguish simple graphs $G$ with at least one edge and
--
--   $$\max_\chi \mathrm{cut}_\chi(G)\ \ge\ c\,|E(G)|$$
--
--   from simple graphs with at least one edge and $\max_\chi \mathrm{cut}_\chi(G)\le s\,|E(G)|$. NP-hardness of distinguishing is Karp-style promise hardness: every NP language reduces in polynomial time to instances that satisfy the first condition on members and the second on non-members.
--
--   $(c,s)$-hardness implies that MAX-$k$-CUT on graphs is NP-hard to approximate within the ratio $s/c$.
--
--   **Formalization Note** This is the published $(c,s)$-hardness predicate for ℕ-weighted multigraphs, with the simplicity condition added to both promise sets.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.4, p.4 (NP-hard to approximate MAX-3-CUT), for the problem of §1.1, p.3

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_wt
import Definitions.Def_Max3CutHard_maxCutK
import Definitions.Def_HeilmanMax3Cut_IsSimple
open OptInapprox.MaxCut

namespace HeilmanMax3Cut

/-- **`(c, s)`-hardness of MAX-`k`-CUT on simple graphs.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.4, p.4 ("it is NP-hard to
approximate MAX-3-CUT within `α₃ + ε`"), for the unweighted problem of §1.1, p.3.

`MaxKCutHardSimple k c s` says: it is NP-hard (Karp-style promise hardness) to distinguish simple
graphs `G` with `max_χ cut_χ(G) ≥ c·|E(G)|` from simple graphs with `max_χ cut_χ(G) ≤ s·|E(G)|`,
where `χ` ranges over colourings of the vertices with `k` colours and `cut_χ(G)` counts the edges
whose endpoints get different colours. It implies NP-hardness of approximating MAX-`k`-CUT on
graphs within the ratio `s/c`.

**Formalization Note.** This is the published `Max3CutHard.MaxKCutHard` (the same
`SetCoverThreshold.SetCover.GapNPHard` over the unary encoding `OptInapprox.MaxCut.encMaxCut`) with
`IsSimple G` added to both promise sets, so the instances are ordinary graphs. Both sets also keep
`0 < w(G)` (a graph with at least one edge), as in the published definition. -/
def MaxKCutHardSimple (k : ℕ) (c s : ℝ) : Prop :=
  SetCoverThreshold.SetCover.GapNPHard encMaxCut
    (fun G => IsSimple G ∧ 0 < Max3CutHard.wt G ∧
      c * (Max3CutHard.wt G : ℝ) ≤ (Max3CutHard.maxCutK k G : ℝ))
    (fun G => IsSimple G ∧ 0 < Max3CutHard.wt G ∧
      (Max3CutHard.maxCutK k G : ℝ) ≤ s * (Max3CutHard.wt G : ℝ))

end HeilmanMax3Cut


