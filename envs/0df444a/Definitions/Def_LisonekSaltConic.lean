-- Prove2me | Definitions.Def_LisonekSaltConic
-- name    : LisonekSaltConic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:43:06.15917+00:00
-- url     : https://prove2.me/theorems/8be4e4af-84a6-4cd2-a2f1-6d53af7b7fb2
-- title:
--   Conic
-- statement:
--   Definitions and structural lemmas for Conic, from Vijaykumar Singh's pinned Lisoněk–Salt conic lemmas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean

import Mathlib
set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]
def row12_orig (x : ZMod p) : Fin 4 → ZMod p :=
  ![(x^2 + x) * 2⁻¹, -(x^2 + 2*x), 0, 0]
def row34_orig (n y : ZMod p) : Fin 4 → ZMod p :=
  ![(y^2 - y) * (2 * n)⁻¹, (y - y^2) * n⁻¹, 1 - y, y]
def M_canon (n : ZMod p) : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  !![4, 1, 0, n⁻¹; -2, -1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]


