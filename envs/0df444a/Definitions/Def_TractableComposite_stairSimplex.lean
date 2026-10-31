-- Prove2me | Definitions.Def_TractableComposite_stairSimplex
-- name    : TractableComposite_stairSimplex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:49.75751+00:00
-- url     : https://prove2.me/theorems/4c311bb8-b4d8-4df6-960b-62cc0640061b
-- title:
--   The staircase simplex $\Xi_\pi$ (or $\Upsilon_\pi$)
-- statement:
--   For a movement vector $\pi$, the staircase simplex is the convex hull of the $dn+1$ staircase vertices $\operatorname{ext}(S,\Pi(\pi,0)),\dots,\operatorname{ext}(S,\Pi(\pi,dn))$. Over all movement vectors these simplices form the staircase triangulation (Definition 3). For $Q$ it is $\Upsilon_\pi=\operatorname{conv}(\mathcal V(\pi,0),\dots,\mathcal V(\pi,dn))$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), §2.2, p.7, Definition 3, p.7, and p.11

import Mathlib
import Definitions.Def_TractableComposite_stairVtx

namespace TractableComposite

/-- **The staircase simplex Ξ_π / Υ_π**, pp.7, 11: `conv{ext(S,Π(π,0)), …, ext(S,Π(π,dn))}`. The family
of these simplices over all movement vectors is the staircase triangulation (Definition 3, p.7).
He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.7 (Ξ_π), p.11 (Υ_π = conv(𝒱(π,0), …, 𝒱(π,dn))). -/
def stairSimplex {d n : ℕ} (υ : Fin d → Fin (n + 1) → (Fin (n + 1) → ℝ))
    (π : Fin (d * n) → Fin d) : Set (Fin d → Fin (n + 1) → ℝ) :=
  convexHull ℝ (Set.range (fun k : Fin (d * n + 1) => stairVtx υ π k))

end TractableComposite


