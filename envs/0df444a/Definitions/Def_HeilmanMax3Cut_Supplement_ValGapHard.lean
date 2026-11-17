-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_ValGapHard
-- name    : HeilmanMax3Cut_Supplement_ValGapHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:04:05.689454+00:00
-- url     : https://prove2.me/theorems/0fab40d4-8c0e-4d2a-b9b1-6f494f888b13
-- title:
--   $(c,s)$-gap NP-hardness of a graph optimization value
-- statement:
--   For a value $\mathrm{val}$ on weighted graphs and constants $c,s$: it is NP-hard to distinguish weighted graphs $G$ with $\mathrm{val}(G)\ge c\,w(G)$ from weighted graphs with $\mathrm{val}(G)\le s\,w(G)$, where $w(G)$ is the total edge weight and both kinds of instance have at least one edge. With $c>0$ this makes it NP-hard to approximate $\mathrm{val}$ within the ratio $s/c$.
--
--   It is the hardness notion of Theorems 1.7 and 1.8, the same as for MAX-3-CUT in the mission's goal.
--
--   **Formalization Note** NP-hardness is Karp-style promise hardness over the unary encoding of weighted graphs used throughout the mission.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorems 1.7, 1.8, p.6

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_wt
open OptInapprox.MaxCut

namespace HeilmanMax3Cut.Supplement

/-- **`(c, s)`-gap hardness of a graph optimization value.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorems 1.7 and 1.8, p.6 ("it is
NP-hard to approximate … within a multiplicative factor `r`"), encoded as for the published goal
`HeilmanMax3Cut.theorem_1_4`: `ValGapHard val c s` says it is NP-hard (Karp-style promise hardness)
to distinguish weighted graphs `G` with `val(G) ≥ c·w(G)` from those with `val(G) ≤ s·w(G)`, where
`w(G)` is the total edge weight. When `0 < c`, this makes approximation within `s/c` NP-hard.

**Formalization Note.** "NP-hard to distinguish" is the published
`SetCoverThreshold.SetCover.GapNPHard` over the published unary encoding
`OptInapprox.MaxCut.encMaxCut` of ℕ-weighted loopless multigraphs `WMaxCut`; `w(G)` is the
published `Max3CutHard.wt`. Both promise sets require `0 < w(G)`, as in `Max3CutHard.MaxKCutHard`:
for the empty graph the two cases coincide. -/
def ValGapHard (val : WMaxCut → ℝ) (c s : ℝ) : Prop :=
  SetCoverThreshold.SetCover.GapNPHard encMaxCut
    (fun G => 0 < Max3CutHard.wt G ∧ c * (Max3CutHard.wt G : ℝ) ≤ val G)
    (fun G => 0 < Max3CutHard.wt G ∧ val G ≤ s * (Max3CutHard.wt G : ℝ))

end HeilmanMax3Cut.Supplement


