-- Prove2me | Definitions.Def_PunctSketch_nbrMask
-- name    : PunctSketch_nbrMask
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:31.726196+00:00
-- url     : https://prove2.me/theorems/a6eba191-ac22-47a2-b69b-9ff48f9b596d
-- title:
--   The neighbourhood as a bit mask
-- statement:
--   For a graph $G$ on $\{0,\dots,n-1\}$ and a vertex $v$, the bit string of length $n$ whose position $u$ says whether $\{v,u\}$ is an edge. This is the input $N(v)$ of the node player $v$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.5 (PDF p.6)

import Mathlib

namespace PunctSketch

open Classical in
/-- **The neighbourhood of `v` as a bit string.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.5: `N(x) = {y : {x, y} ∈ E}`.

Position `u` of `nbrMask G v` is `true` exactly when `{v, u}` is an edge of `G`. -/
noncomputable def nbrMask {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : List Bool :=
  List.ofFn (fun u => decide (G.Adj v u))

end PunctSketch


