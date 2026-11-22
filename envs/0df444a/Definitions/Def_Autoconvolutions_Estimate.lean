-- Prove2me | Definitions.Def_Autoconvolutions_Estimate
-- name    : Autoconvolutions_Estimate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:48:13.407032+00:00
-- url     : https://prove2.me/theorems/5a7e3c6b-c0ab-472e-93d2-97ded1d9aff2
-- title:
--   Estimate
-- statement:
--   Definitions and structural lemmas for Estimate, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Estimate.lean

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Definitions.Def_Autoconvolutions_Parameters
public import Definitions.Def_Autoconvolutions_Digits
public import Definitions.Def_Autoconvolutions_Levels
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace Autoconvolutions.Estimate
def height (n s : ℕ) : ℝ :=
  ((2*n-s).factorial : ℝ) * ((2*n+s).factorial : ℝ)
def count (n r b s : ℕ) : ℝ :=
  (r.choose (2*n-s) : ℝ) * (b.choose (2*n+s) : ℝ)
end Autoconvolutions.Estimate


