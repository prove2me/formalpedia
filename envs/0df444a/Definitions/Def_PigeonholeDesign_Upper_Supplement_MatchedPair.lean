-- Prove2me | Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair
-- name    : PigeonholeDesign_Upper_Supplement_MatchedPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:59:19.045294+00:00
-- url     : https://prove2.me/theorems/80344a2e-4a15-4289-968a-a259896bc292
-- title:
--   Definition 1, p. 12 — the matched-pair design's discrepancy $\min_{|A|=|B|=T/2} d_{A,B}$
-- statement:
--   $T$ subjects arrive one at a time, $T$ even (p. 9). Subject $t$ carries a covariate $x_t\in\mathcal S=[0,1]^{p+q}$: $p$ continuous coordinates in $[0,1]$ and $q$ discrete coordinates, the $i$-th taking values in a finite support $S_i\subseteq[0,1]$ whose size does not depend on $T$ (pp. 10, 21). The sequence $x=(x_1,\dots,x_T)$ is chosen in advance by an adversary. For a split of the subjects into a control group $A$ and a treated group $B$ with $|A|=|B|$, the **discrepancy** $d_{A,B}$ is the minimum total Euclidean length of a perfect matching between $A$ and $B$ (display (1), p. 11).
--
--   The **matched-pair design** (Definition 1, p. 12) knows all covariates in advance and uses the best balanced split, so its discrepancy is
--   $$d^{\mathrm{MP}}(x)=\min_{|A|=|B|=T/2} d_{A,B};$$
--   randomly swapping the two subjects of each matched pair does not change it.
--
--   This is the benchmark the paper compares every online design against: no design can have a smaller discrepancy on the same arrival sequence.
--
--   **Formalization Note** `mpdDisc x` is the infimum of the published `PigeonholeDesign.Upper.discrepancy x w` over the assignments `w : Fin T → Bool` with exactly $T/2$ control subjects (`w t = false`). It works over any pseudometric covariate space. The infimum ranges over balanced splits only: over all `w` it would be the junk value $0$ of an unbalanced split, for which no bijection between the groups exists.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 12, Definition 1 and display (2)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper.Supplement

/-- Definition 1 and display (2), p. 12: the discrepancy of the matched-pair design,
`d_{A*,B*} = min_{(A,B) ∈ M} d_{A,B}`, the minimum of the discrepancy (display (1)) over the balanced
splits, those with exactly `T/2` control subjects (`w t = false`). The random swap inside each
matched pair does not change it. The infimum ranges over balanced splits only: over all `w` it
would be the junk value `0` of an unbalanced split. -/
noncomputable def mpdDisc {E : Type*} [PseudoMetricSpace E] {T : ℕ} (x : Fin T → E) : ℝ :=
  ⨅ w : {w : Fin T → Bool // (Finset.univ.filter (fun t => w t = false)).card = T / 2},
    PigeonholeDesign.Upper.discrepancy x w.1

end PigeonholeDesign.Upper.Supplement


