-- Prove2me | Definitions.Def_BBPSSW_Distill_Axis
-- name    : BBPSSW_Distill_Axis
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:32.4788+00:00
-- url     : https://prove2.me/theorems/461d44cd-e70b-4f6a-8df8-0a40e4029f3a
-- title:
--   Rotation axes $x$, $y$, $z$
-- statement:
--   A label for the three coordinate axes $x$, $y$, $z$ about which a spin is rotated. It indexes the Pauli matrices $\sigma_x,\sigma_y,\sigma_z$ (rotations by $\pi$) and the bilateral $\pi/2$ rotations $B_x,B_y,B_z$.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered bullets (unilateral Pauli rotations; bilateral π/2 rotations Bx, By, Bz)

import Mathlib

namespace BBPSSW.Distill

/-- **The three rotation axes `x`, `y`, `z`.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered bullets: "rotations by π radians about the x, y, or z axis",
"Bilateral π/2 rotations Bx, By, and Bz … about the x, y, or z axis respectively").

A label for the coordinate axis of a spin rotation; it indexes the Pauli matrices and the
bilateral π/2 rotations. -/
inductive Axis
  | x
  | y
  | z
  deriving DecidableEq

instance : Fintype Axis where
  elems := {.x, .y, .z}
  complete := fun a => by cases a <;> decide

end BBPSSW.Distill


