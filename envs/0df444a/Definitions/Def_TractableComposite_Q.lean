-- Prove2me | Definitions.Def_TractableComposite_Q
-- name    : TractableComposite_Q
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:40.003021+00:00
-- url     : https://prove2.me/theorems/bd6c0783-0581-4f48-97e0-4c2fc4f07845
-- title:
--   The polytope $Q=\prod_i Q_i$
-- statement:
--   For $a$ with strictly increasing rows, $Q=\prod_{i=1}^d Q_i$, where $Q_i$ is the simplex in $\mathbb R^{n+1}$ with extreme points $v_{i0},\dots,v_{in}$ of (3). It is a subset of $P$ and the domain on which the staircase triangulation describes $\operatorname{conc}_Q(\bar\phi)$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (3), p.4

import Mathlib
import Definitions.Def_TractableComposite_vtx
import Definitions.Def_TractableComposite_prodSimplex

namespace TractableComposite

/-- **The polytope Q**, (3), p.4: `Q = ∏ᵢ Qᵢ`, where `Qᵢ` is the simplex in ℝ^{n+1} with extreme
points `vᵢ₀, …, vᵢₙ` of (3). He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (3), p.4. -/
def Q {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) : Set (Fin d → Fin (n + 1) → ℝ) :=
  prodSimplex (vtx a)

end TractableComposite


