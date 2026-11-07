-- Prove2me | Definitions.Def_PunctSketch_puncturePoly
-- name    : PunctSketch_puncturePoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:33.95007+00:00
-- url     : https://prove2.me/theorems/4a33068c-bf34-4c64-b2f3-318925d7c753
-- title:
--   The vanishing polynomial (5)
-- statement:
--   For a set $F$ of vertices,
--   $$P_F(X)=\prod_{z\in F}(X-\alpha_z)=\sum_{i=0}^{|F|}b_{F,i}X^i ,$$
--   which vanishes at $\alpha_z$ for each $z\in F$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), proof of Theorem 4, p.11 (PDF p.12), eq. (5)

import Mathlib
open Polynomial

namespace PunctSketch

/-- **The vanishing polynomial (5).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Theorem 4, p.11, eq. (5):
`P_F(X) = Π_{z∈F} (X − α_z) = Σ_{i=0}^{|F|} b_{F,i} X^i`. The coefficient `b_{F,i}` is
`(puncturePoly α F).coeff i`. -/
noncomputable def puncturePoly {n Q : ℕ} (α : Fin n → ZMod Q) (F : Finset (Fin n)) :
    (ZMod Q)[X] :=
  ∏ z ∈ F, (X - C (α z))

end PunctSketch


