-- Prove2me | Definitions.Def_ChipFiringWithLean
-- name    : ChipFiringWithLean
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:54:49.090197+00:00
-- url     : https://prove2.me/theorems/1ab0f531-5d11-4aa5-b71a-33b709153048
-- title:
--   Chip Firing With Lean
-- statement:
--   Definitions and structural lemmas for Chip Firing With Lean, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean.lean

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_CFGraphExample
public import Definitions.Def_ChipFiringWithLean_Config
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Algorithms
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
set_option autoImplicit true
@[expose] public section


