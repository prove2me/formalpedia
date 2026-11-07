-- Prove2me | Definitions.Def_Max3CutHard_maxCutK
-- name    : Max3CutHard_maxCutK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:27.889026+00:00
-- url     : https://prove2.me/theorems/11c3d26b-5dcd-46db-9fba-5911d803bea5
-- title:
--   Maximum $k$-cut $\max_\chi\mathrm{cut}_\chi(G)$
-- statement:
--   For an $\mathbb N$-weighted loopless multigraph $G$ on $n$ vertices,
--
--   $$\max_{\chi}\mathrm{cut}_\chi(G),$$
--
--   the maximum over all $k^n$ colourings $\chi:\{0,\dots,n-1\}\to[k]$ of the cut weight.
--
--   This is the optimum value of Max-$k$-Cut.
--
--   **Formalization Note** A maximum over a finite set, computed with `Finset.sup` in $\mathbb N$.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_cutK
open OptInapprox.MaxCut

namespace Max3CutHard

/-- **Maximum `k`-cut `max_χ cut_χ(G)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts, p.4: "`max_χ cut_χ(G)`".

**Formalization Note.** A maximum over the finitely many colourings `χ : Fin G.n → Fin k`
(`Finset.sup` in `ℕ`; there is always at least one colouring when `k ≥ 1` or `G.n = 0`, and the
value for `k = 0`, `G.n > 0` is `0`, which no theorem of the mission uses). -/
def maxCutK (k : ℕ) (G : WMaxCut) : ℕ :=
  Finset.univ.sup fun χ : Fin G.n → Fin k => cutK k G χ

end Max3CutHard


