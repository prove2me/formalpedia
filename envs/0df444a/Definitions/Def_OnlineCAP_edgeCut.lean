-- Prove2me | Definitions.Def_OnlineCAP_edgeCut
-- name    : OnlineCAP_edgeCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:33.10407+00:00
-- url     : https://prove2.me/theorems/e1e63399-933a-4012-918c-2a1edf4205b9
-- title:
--   The edge cut δ_E(C) of a multigraph
-- statement:
--   The base graph is a finite **multigraph** on the vertices $v_0,\dots,v_{n-1}$: a finite set $E$ of edges, each with an unordered pair of ends. For a vertex set $C$,
--
--   $$\delta_E(C)=\{e\in E : e\text{ has exactly one end in } C\}.$$
--
--   **Formalization Note** Vertices are `Fin n`; parallel edges are distinct elements of $E$ and loops are allowed (they never cross a cut). Simple graphs are a special case.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2, p.9

import Mathlib
import Definitions.Def_OnlineCAP_crosses

namespace OnlineCAP

/-- **The edge cut `δE(C)`.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2, p.9 (PDF p.9): "we denote by δE(C) the set of edges in E
with exactly one endpoint in C".

The base graph is a finite multigraph on the vertices `Fin n`: a finite edge type `E` and the
ends `ends e : Sym2 (Fin n)` of each edge. `edgeCut ends C` is the set of edges crossing `C`.

**Formalization Note.** Parallel edges are distinct elements of `E`; loops are allowed and never
cross a cut. A simple graph is the case where `ends` is injective and loop-free. -/
noncomputable def edgeCut {n : ℕ} {E : Type} [Fintype E] (ends : E → Sym2 (Fin n))
    (C : Finset (Fin n)) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => crosses (ends e) C)

end OnlineCAP


