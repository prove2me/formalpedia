-- Prove2me | Definitions.Def_Max3CutHard_maxCutR
-- name    : Max3CutHard_maxCutR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:32.765297+00:00
-- url     : https://prove2.me/theorems/37ddbd02-538b-4100-885a-beb0ed0a63ac
-- title:
--   Maximum $k$-cut of a real-weighted graph
-- statement:
--   For a weighted graph $G$ on a finite vertex set $V$ and $k\ge1$,
--
--   $$\max_{\chi:V\to[k]}\mathrm{cut}_\chi(G).$$
--
--   **Formalization Note** A maximum over the finite nonempty set of colourings (`Finset.sup'`); $k\ge1$ is the instance `NeZero k`.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib
import Definitions.Def_Max3CutHard_cutR

namespace Max3CutHard

/-- **Maximum `k`-cut `max_χ cut_χ(G)` of a real-weighted graph.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts, p.4.

**Formalization Note.** A maximum over the finite nonempty set of colourings `χ : V → Fin k`
(`Finset.sup'`; `NeZero k` gives nonemptiness). -/
noncomputable def maxCutR (k : ℕ) [NeZero k] {V : Type} [Fintype V] [DecidableEq V] (G : RGraph V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun χ : V → Fin k => cutR χ G

end Max3CutHard


