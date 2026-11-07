-- Prove2me | Definitions.Def_Max3CutHard_MaxKCutHard
-- name    : Max3CutHard_MaxKCutHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:00.227558+00:00
-- url     : https://prove2.me/theorems/3ebfe9d8-8db7-4880-bb1c-cdeb60b9e676
-- title:
--   $(c,s)$-hardness of Max-$k$-Cut
-- statement:
--   Max-$k$-Cut is **$(c,s)$-hard** if it is NP-hard to distinguish graphs $G$ with
--
--   $$\max_\chi \mathrm{cut}_\chi(G)\ge c\,w(G)\qquad\text{from graphs with}\qquad \max_\chi\mathrm{cut}_\chi(G)\le s\,w(G).$$
--
--   As the source notes, $(c,s)$-hardness implies NP-hardness of approximating Max-$k$-Cut within $s/c$.
--
--   **Formalization Note** "NP-hard to distinguish" is Karp-style promise NP-hardness (the published `SetCoverThreshold.SetCover.GapNPHard`): every NP language over every finite alphabet reduces in polynomial time to the promise problem, members going to the first case and non-members to the second. Graphs are the published $\mathbb N$-weighted loopless multigraphs `WMaxCut` with their unary encoding `encMaxCut`. Both cases require $w(G)>0$; at $w(G)=0$ the two cases coincide.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_wt
import Definitions.Def_Max3CutHard_maxCutK
open OptInapprox.MaxCut

namespace Max3CutHard

/-- **`(c, s)`-hardness of Max-`k`-Cut.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts, p.4: "We say that Max-k-Cut
is `(c, s)`-hard if it is NP-hard to distinguish `max_χ cut_χ(G) ≥ c w(G)` from
`max_χ cut_χ(G) ≤ s w(G)`; this implies NP-hardness of approximation within `s/c`."

**Formalization Note.** "NP-hard to distinguish" is Karp-style promise NP-hardness, the published
`SetCoverThreshold.SetCover.GapNPHard` over the published unary encoding
`OptInapprox.MaxCut.encMaxCut` of ℕ-weighted loopless multigraphs `WMaxCut`. Both promise sets
require `0 < w(G)`: at `w(G) = 0` the two cases coincide (both hold for every `c, s`), and without
the clause a reduction to the empty graph would satisfy both. -/
def MaxKCutHard (k : ℕ) (c s : ℝ) : Prop :=
  SetCoverThreshold.SetCover.GapNPHard encMaxCut
    (fun G => 0 < wt G ∧ c * (wt G : ℝ) ≤ (maxCutK k G : ℝ))
    (fun G => 0 < wt G ∧ (maxCutK k G : ℝ) ≤ s * (wt G : ℝ))

end Max3CutHard


