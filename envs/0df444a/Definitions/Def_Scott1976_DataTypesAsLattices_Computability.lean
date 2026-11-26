-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Computability
-- name    : Scott1976_DataTypesAsLattices_Computability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:54:29.515777+00:00
-- url     : https://prove2.me/theorems/1b0b08a1-2017-439b-bac9-ffb6b3cea5f8
-- title:
--   Computability
-- statement:
--   Definitions and structural lemmas for Computability, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Computability.lean

import Mathlib.Computability.RE
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def IsRE (u : Pomega) : Prop :=
  REPred fun n : ℕ => n ∈ u
def IsComputable (f : Pomega → Pomega) : Prop :=
  IsScottContinuous f ∧ IsRE (graph f)
def IsLambdaDefinable (u : Pomega) : Prop :=
  ∃ t : Term, interp t (fun _ => botElem) = u
end Scott1976.DataTypesAsLattices


