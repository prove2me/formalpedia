-- Prove2me | Definitions.Def_TractableComposite_QJ
-- name    : TractableComposite_QJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:49.420989+00:00
-- url     : https://prove2.me/theorems/f2120d7e-671b-46e9-8dc6-2b642eea04eb
-- title:
--   The polytope $Q_J$
-- statement:
--   For $J\in\mathcal J$, $Q_J=Q_{1J_1}\times\dots\times Q_{dJ_d}$, where $Q_{iJ_i}$ is the simplex whose extreme points are given by (3) with the parameter vector $a_{iJ_i}\in\mathbb R^{|J_i|}$. Its points are vectors $y_J$ indexed by the pairs $(i,j)$ with $j\in J_i$; $Q_J$ is the projection of $Q$ onto these coordinates.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (7), pp.5–6

import Mathlib

namespace TractableComposite

/-- **The polytope Q_J**, (7), pp.5–6: `Q_J = Q_{1J₁} × ⋯ × Q_{dJ_d}`, where `Q_{iJᵢ}` is the simplex whose
extreme points are defined in (3) with the parameter vector `a_{iJᵢ} ∈ ℝ^{|Jᵢ|}`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (7), pp.5–6.

**Formalization Note.** A point `y_J` is `(i : Fin d) → J i → ℝ` (block `i` indexed by the subtype
`Jᵢ`). The vertex of `Q_{iJᵢ}` attached to `j ∈ Jᵢ` has coordinate `a_{i, min(l, j)}` at `l ∈ Jᵢ`, which is
(3) for the increasing vector `a_{iJᵢ}`. -/
def QJ {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (J : Fin d → Finset (Fin (n + 1))) : Set ((i : Fin d) → J i → ℝ) :=
  {y | ∀ i, y i ∈ convexHull ℝ (Set.range (fun j : J i => fun l : J i => a i (min l.1 j.1)))}

end TractableComposite


