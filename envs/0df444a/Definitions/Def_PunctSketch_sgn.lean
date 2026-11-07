-- Prove2me | Definitions.Def_PunctSketch_sgn
-- name    : PunctSketch_sgn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:57.416648+00:00
-- url     : https://prove2.me/theorems/ab586257-7222-4ab3-9113-21c1a434eb90
-- title:
--   $\mathrm{sgn}(x-y)$ on vertices
-- statement:
--   For two vertices $x,y$, the sign of the difference of their labels, as an integer in $\{-1,0,1\}$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.4 (PDF p.5), eq. (2)

import Mathlib

namespace PunctSketch

/-- **`sgn(x − y)` on vertices.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.4, eq. (2). The sign of the difference of the labels
in `Fin n`, as an integer: `1`, `0` or `-1`. -/
def sgn {n : ℕ} (x y : Fin n) : ℤ := Int.sign ((x : ℤ) - (y : ℤ))

end PunctSketch


