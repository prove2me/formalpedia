-- Prove2me | Definitions.Def_Max3CutHard_cutR
-- name    : Max3CutHard_cutR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:06.248774+00:00
-- url     : https://prove2.me/theorems/3b1729d9-2d68-4e5a-8e6b-869c06e4c0cb
-- title:
--   Cut weight $\mathrm{cut}_\chi(G)$ of a colouring of a real-weighted graph
-- statement:
--   For a weighted graph $G$ on $V$ and a colouring $\chi:V\to[k]$,
--
--   $$\mathrm{cut}_\chi(G)=\sum_{\{u,v\}\in E}w_{uv}\,[\chi(u)\ne\chi(v)].$$
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib
import Definitions.Def_Max3CutHard_RGraph

namespace Max3CutHard

/-- **Cut weight `cut_χ(G)` of a colouring of a real-weighted graph.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts,
p.4: "`cut_χ(G) = Σ_{u,v}∈E w_uv [χ(u) ≠ χ(v)]`". Colours `[k]` are `Fin k`. -/
noncomputable def cutR {V : Type} {k : ℕ} (χ : V → Fin k) (G : RGraph V) : ℝ :=
  (G.map fun e => if χ e.1.1 ≠ χ e.1.2 then e.2 else 0).sum

end Max3CutHard


