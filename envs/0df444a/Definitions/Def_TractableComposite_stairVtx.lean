-- Prove2me | Definitions.Def_TractableComposite_stairVtx
-- name    : TractableComposite_stairVtx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:40.842048+00:00
-- url     : https://prove2.me/theorems/5ffe2b9f-0412-4870-bdbf-164a8ddc4703
-- title:
--   The staircase vertex $\operatorname{ext}(S,\Pi(\pi,k))$
-- statement:
--   Given vertex lists $\upsilon_{i0},\dots,\upsilon_{in}$ of a product of simplices and a movement vector $\pi$, the $k$-th staircase vertex is $(\upsilon_{1,\Pi(\pi,k)_1},\dots,\upsilon_{d,\Pi(\pi,k)_d})$. For the vertices of $Q$ this is the paper's $\mathcal V(\pi,k)$, and its last column $(a_{i,\Pi(\pi,k)_i})_i$ is $\mathcal V_{\cdot n}(\pi,k)$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), §2.2, p.7, and p.11

import Mathlib
import Definitions.Def_TractableComposite_gridPt

namespace TractableComposite

/-- **The staircase vertex ext(S, Π(π,k))**, p.7 (and `𝒱(π,k) = ext(Q, Π(π,k))`, p.11): the vertex of
the product of simplices with vertices `υ` that sits at the grid point `Π(π,k)`, i.e.
`(υ_{1, Π(π,k)₁}, …, υ_{d, Π(π,k)_d})`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), pp.7, 11.

**Formalization Note.** With `υ = vtx a` this is the paper's `𝒱(π,k)`; its last column
`(a_{i, Π(π,k)ᵢ})ᵢ` is `𝒱·ₙ(π,k)`. -/
def stairVtx {d n : ℕ} (υ : Fin d → Fin (n + 1) → (Fin (n + 1) → ℝ)) (π : Fin (d * n) → Fin d)
    (k : ℕ) : Fin d → Fin (n + 1) → ℝ :=
  fun i => υ i (gridPt π k i)

end TractableComposite


