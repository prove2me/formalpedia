-- Prove2me | Definitions.Def_LNTopology_Hermetization_gAvgDeg
-- name    : LNTopology_Hermetization_gAvgDeg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:23.871828+00:00
-- url     : https://prove2.me/theorems/c6d91e4b-9042-441b-811d-31353ee6a970
-- title:
--   Average degree of a finite simple graph
-- statement:
--   The **average degree** of a finite simple graph $G=(V,E)$ is
--
--   $$\bar d(G)=\frac{1}{|V|}\sum_{v\in V}\deg_G(v)=\frac{2|E|}{|V|},$$
--
--   and $0$ on the empty vertex set (division by zero returns $0$).
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemma B.4, p. 12 (PDF p. 13), with Definition 3.4, p. 7 (PDF p. 8)

import Mathlib

namespace LNTopology.Hermetization

/-- **Average degree of a finite simple graph.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemma B.4, p. 12 ("Every graph G with average degree 2d"), with the average degree of
Definition 3.4, p. 7.

`gAvgDeg G = (Σ_v deg v) / |V|`; on the empty vertex type Lean's `x / 0 = 0` gives `0`. -/
noncomputable def gAvgDeg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (∑ v, (G.degree v : ℝ)) / Fintype.card V

end LNTopology.Hermetization


