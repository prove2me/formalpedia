-- Prove2me | Definitions.Def_TractableComposite_Zmap
-- name    : TractableComposite_Zmap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:47.183986+00:00
-- url     : https://prove2.me/theorems/a1e60b2e-204e-43f1-9d4b-83b54427a2fd
-- title:
--   The affine map $Z:Q\to\Delta$
-- statement:
--   For $s\in\mathbb R^{d\times(n+1)}$,
--
--   $$z_{i0}=1,\qquad z_{ij}=\frac{s_{ij}-s_{i,j-1}}{a_{ij}-a_{i,j-1}}\quad(j=1,\dots,n).$$
--
--   For $s\in Q$ the slopes $z_{ij}$ are non-increasing in $j$ (10); sorting them yields the staircase simplex that contains $s$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (11), p.9

import Mathlib

namespace TractableComposite

/-- **The affine map Z : Q → Δ**, (11), p.9: `zᵢ₀ = 1` and `zᵢⱼ = (sᵢⱼ − s_{i,j−1})/(aᵢⱼ − a_{i,j−1})` for
`j = 1,…,n`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (11), p.9.

**Formalization Note.** Column `j−1` is `⟨j − 1, _⟩`; the denominator is positive for strictly
increasing `a`. -/
noncomputable def Zmap {d n : ℕ} (a s : Fin d → Fin (n + 1) → ℝ) : Fin d → Fin (n + 1) → ℝ :=
  fun i j => if h : j.val = 0 then 1 else
    (s i j - s i ⟨j.val - 1, by omega⟩) / (a i j - a i ⟨j.val - 1, by omega⟩)

end TractableComposite


