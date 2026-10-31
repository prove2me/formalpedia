-- Prove2me | Definitions.Def_TractableComposite_FJ
-- name    : TractableComposite_FJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:45.976295+00:00
-- url     : https://prove2.me/theorems/08c454cc-604c-46bf-bac3-279059e77872
-- title:
--   The face $F_J$ of $Q$
-- statement:
--   For $J\in\mathcal J$, $F_J=F_{1J_1}\times\dots\times F_{dJ_d}$ with $F_{iJ_i}=\operatorname{conv}\{v_{ij}\mid j\in J_i\}$, a face of $Q$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), p.5

import Mathlib
import Definitions.Def_TractableComposite_vtx

namespace TractableComposite

/-- **The face F_J of Q**, p.5: `F_J = F_{1J₁} × ⋯ × F_{dJ_d}` with `F_{iJᵢ} = conv{vᵢⱼ | j ∈ Jᵢ}`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.5. -/
def FJ {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (J : Fin d → Finset (Fin (n + 1))) : Set (Fin d → Fin (n + 1) → ℝ) :=
  {s | ∀ i, s i ∈ convexHull ℝ (vtx a i '' (J i : Set (Fin (n + 1))))}

end TractableComposite


