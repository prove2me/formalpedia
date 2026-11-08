-- Prove2me | Definitions.Def_AffDisp4n_IsAffineOp
-- name    : AffDisp4n_IsAffineOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:29.899897+00:00
-- url     : https://prove2.me/theorems/d4288f68-23d5-4ef9-a61d-884058dde69a
-- title:
--   Affine operation
-- statement:
--   An operation $h : \mathbb F_2 \times \mathbb F_2 \to \mathbb F_2$ is **affine** if $h(t_1, t_2) = b_1 t_1 + b_2 t_2 + c$ for some $b_1, b_2, c \in \mathbb F_2$; either coefficient may vanish. Constant, unary and XOR-type operations are affine, and a gate labelled by one is an **affine gate**.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.1, pp.12–13

import Mathlib

namespace AffDisp4n

/-- An **affine operation** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.1, p.12): `h(t₁, t₂) = b₁ t₁ + b₂ t₂ + c` with `b₁, b₂, c ∈ 𝔽₂`
(either coefficient may vanish). Constant, unary and XOR-type operations are affine. -/
def IsAffineOp (h : ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  ∃ b₁ b₂ c : ZMod 2, ∀ t₁ t₂, h t₁ t₂ = b₁ * t₁ + b₂ * t₂ + c

end AffDisp4n


