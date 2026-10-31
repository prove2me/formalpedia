-- Prove2me | Definitions.Def_TractableComposite_vtx
-- name    : TractableComposite_vtx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:42.793851+00:00
-- url     : https://prove2.me/theorems/6e17f818-9a29-442b-a433-8d05ec752f31
-- title:
--   The vertices $v_{ij}=(a_{i0},\dots,a_{ij},a_{ij},\dots,a_{ij})$ of $Q_i$
-- statement:
--   For a row $a_i=(a_{i0},\dots,a_{in})$ and $j\in\{0,\dots,n\}$,
--
--   $$v_{ij}=(a_{i0},\dots,a_{ij},a_{ij},\dots,a_{ij}),$$
--
--   that is, the $l$-th coordinate of $v_{ij}$ is $a_{i,\min(l,j)}$. These are the extreme points of the simplex $Q_i$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (3), p.4

import Mathlib

namespace TractableComposite

/-- **The vertices vᵢⱼ of Qᵢ**, (3), p.4: `vᵢⱼ = (aᵢ₀, …, aᵢⱼ, aᵢⱼ, …, aᵢⱼ)`, i.e. the `l`-th
coordinate of `vᵢⱼ` is `a_{i, min(l, j)}`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (3), p.4. -/
def vtx {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (i : Fin d) (j : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  fun l => a i (min l j)

end TractableComposite


