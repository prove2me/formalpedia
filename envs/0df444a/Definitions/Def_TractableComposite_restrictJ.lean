-- Prove2me | Definitions.Def_TractableComposite_restrictJ
-- name    : TractableComposite_restrictJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:47.54095+00:00
-- url     : https://prove2.me/theorems/6086b49e-1d9f-473b-b809-6b0f0d8b22b2
-- title:
--   The restriction $y\mapsto y_J$
-- statement:
--   For $J\in\mathcal J$ and $y\in\mathbb R^{d\times(n+1)}$, $y_J=(y_{1J_1},\dots,y_{dJ_d})$ keeps the coordinates of $y_i$ indexed by $J_i$. On $F_J$ it inverts the map $A$ of (18).
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), pp.5 and 14

import Mathlib

namespace TractableComposite

/-- **The restriction y ↦ y_J**, p.5: `y_J = (y_{1J₁}, …, y_{dJ_d})` keeps the coordinates of `yᵢ` in `Jᵢ`;
it is also the inverse of the map `A` of (18) ("a map which transforms s to s_J", p.14). He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), pp.5, 14. -/
def restrictJ {d n : ℕ} (J : Fin d → Finset (Fin (n + 1))) (y : Fin d → Fin (n + 1) → ℝ) : (i : Fin d) → J i → ℝ :=
  fun i j => y i j.1

end TractableComposite


