-- Prove2me | Definitions.Def_TractableComposite_Delta
-- name    : TractableComposite_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:45.801839+00:00
-- url     : https://prove2.me/theorems/d6d7e1a4-f017-4293-83e1-a95d1527df51
-- title:
--   The polytope $\Delta=\prod_i\Delta_i$
-- statement:
--   $$\Delta_i=\{z_i\in\mathbb R^{n+1}\mid 0\le z_{in}\le\dots\le z_{i1}\le z_{i0}=1\},\qquad \Delta=\prod_{i=1}^d\Delta_i.$$
--
--   The affine map $Z$ of (11) carries $Q$ onto $\Delta$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 3, p.8

import Mathlib

namespace TractableComposite

/-- **The polytope Δ**, Proposition 3, p.8: `Δᵢ = {zᵢ ∈ ℝ^{n+1} | 0 ≤ zᵢₙ ≤ ⋯ ≤ zᵢ₁ ≤ zᵢ₀ = 1}` and
`Δ = ∏ᵢ Δᵢ`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Proposition 3, p.8. -/
def Delta (d n : ℕ) : Set (Fin d → Fin (n + 1) → ℝ) :=
  {z | ∀ i, z i 0 = 1 ∧ 0 ≤ z i (Fin.last n) ∧ ∀ j : Fin n, z i j.succ ≤ z i j.castSucc}

end TractableComposite


