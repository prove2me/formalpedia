-- Prove2me | Definitions.Def_TractableComposite_vertQ
-- name    : TractableComposite_vertQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:40.803436+00:00
-- url     : https://prove2.me/theorems/47216ca3-1a02-4f57-bae5-9e8dbcdc2e3b
-- title:
--   The vertex set $\operatorname{vert}(Q)$
-- statement:
--   $\operatorname{vert}(Q)$ is the set of points $(v_{1j_1},\dots,v_{dj_d})$, $(j_1,\dots,j_d)\in\{0,\dots,n\}^d$, with $v_{ij}$ as in (3). Since each row's vertices form a chain $v_{i0}\le\dots\le v_{in}$, it is a lattice under the componentwise order.
--
--   **Formalization Note.** The vertex set is given by its explicit list, as the paper defines $Q$ by these extreme points.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (3), p.4, and p.10

import Mathlib
import Definitions.Def_TractableComposite_vtx
import Definitions.Def_TractableComposite_prodVert

namespace TractableComposite

/-- **vert(Q)**, p.10: the points `(v_{1 j₁}, …, v_{d j_d})` with `vᵢⱼ` as in (3), i.e. the
grid `∏ᵢ {vᵢ₀, …, vᵢₙ}`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (3), p.4, and p.10.

**Formalization Note.** vert(Q) is encoded by its explicit list of extreme points, as the paper defines
`Q` by them in (3); for strictly increasing `a` these are exactly the extreme points of `Q`. -/
def vertQ {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) : Set (Fin d → Fin (n + 1) → ℝ) :=
  prodVert (vtx a)

end TractableComposite


