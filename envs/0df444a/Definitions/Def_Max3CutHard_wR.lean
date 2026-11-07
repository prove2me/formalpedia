-- Prove2me | Definitions.Def_Max3CutHard_wR
-- name    : Max3CutHard_wR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:08.822785+00:00
-- url     : https://prove2.me/theorems/99d4e768-7039-4a9c-a192-4a571d54a460
-- title:
--   Total weight $w(G)$ of a real-weighted graph
-- statement:
--   For a weighted graph $G$,
--
--   $$w(G)=\sum_{\{u,v\}\in E}w_{uv}.$$
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib
import Definitions.Def_Max3CutHard_RGraph

namespace Max3CutHard

/-- **Total weight `w(G)` of a real-weighted graph.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts, p.4:
"`w(G) = Σ_{u,v}∈E w_uv`". -/
noncomputable def wR {V : Type} (G : RGraph V) : ℝ := (G.map Prod.snd).sum

end Max3CutHard


