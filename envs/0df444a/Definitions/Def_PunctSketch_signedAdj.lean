-- Prove2me | Definitions.Def_PunctSketch_signedAdj
-- name    : PunctSketch_signedAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:50.632805+00:00
-- url     : https://prove2.me/theorems/9ab58a5a-a31b-4357-9e19-ef83843545d1
-- title:
--   The signed adjacency matrix (2)
-- statement:
--   The signed adjacency matrix of $G$:
--   $$A^{\pm}(G)[x,y]=\mathbf 1_{\{x,y\}\in E}\,\mathrm{sgn}(y-x).$$
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.4 (PDF p.5), eq. (2)

import Mathlib
import Definitions.Def_PunctSketch_sgn

namespace PunctSketch

open Classical in
/-- **The signed adjacency matrix (2).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.4, eq. (2):
`A±(G)[x, y] = 1_{{x,y}∈E} sgn(y − x)`. -/
noncomputable def signedAdj {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Fin n) : ℤ :=
  if G.Adj x y then sgn y x else 0

end PunctSketch


