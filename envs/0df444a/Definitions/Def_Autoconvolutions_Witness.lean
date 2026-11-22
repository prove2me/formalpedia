-- Prove2me | Definitions.Def_Autoconvolutions_Witness
-- name    : Autoconvolutions_Witness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:48:57.613798+00:00
-- url     : https://prove2.me/theorems/43ff2001-ae1e-41d7-aab8-3c62430c0440
-- title:
--   Witness
-- statement:
--   Definitions and structural lemmas for Witness, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Witness.lean

module
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_Flat
public import Definitions.Def_Autoconvolutions_PolyStep
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Polynomial
open scoped BigOperators
namespace Autoconvolutions.Construction
noncomputable def witness {m : ℕ} (D n K : ℕ) (I J : Finset (Fin m)) : Polynomial ℝ :=
  family Flat.P (Blocks.gen D I) (Blocks.gen D J) n K
end Autoconvolutions.Construction


