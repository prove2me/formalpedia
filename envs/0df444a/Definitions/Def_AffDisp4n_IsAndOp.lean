-- Prove2me | Definitions.Def_AffDisp4n_IsAndOp
-- name    : AffDisp4n_IsAndOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:36.859907+00:00
-- url     : https://prove2.me/theorems/610e778f-b9c8-485c-97f9-eb7c27fcbba1
-- title:
--   AND-type operation
-- statement:
--   An operation $h : \mathbb F_2 \times \mathbb F_2 \to \mathbb F_2$ is **AND-type** if $h(t_1, t_2) = (t_1 + \alpha)(t_2 + \beta) + \gamma$ for some $\alpha, \beta, \gamma \in \mathbb F_2$. Of the sixteen operations, eight are AND-type and the other eight are affine.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.1, p.12

import Mathlib

namespace AffDisp4n

/-- An **AND-type operation** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.1, p.12): `h(t₁, t₂) = (t₁ + α)(t₂ + β) + γ` with
`α, β, γ ∈ 𝔽₂`. Every one of the sixteen operations is affine or AND-type. -/
def IsAndOp (h : ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  ∃ α β γ : ZMod 2, ∀ t₁ t₂, h t₁ t₂ = (t₁ + α) * (t₂ + β) + γ

end AffDisp4n


