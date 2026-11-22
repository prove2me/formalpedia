-- Prove2me | Definitions.Def_Autoconvolutions_Main
-- name    : Autoconvolutions_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:49:20.20595+00:00
-- url     : https://prove2.me/theorems/e631e434-158f-46d7-91bd-87f2ca552500
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Main.lean

module
public import Definitions.Def_Autoconvolutions_Witness
public import Definitions.Def_Autoconvolutions_Coefficients
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Definitions.Def_Autoconvolutions_Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Filter Finset Polynomial
open scoped BigOperators Topology
namespace Autoconvolutions.Construction
end Autoconvolutions.Construction
namespace Autoconvolutions.Parameters
end Autoconvolutions.Parameters


