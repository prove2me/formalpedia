-- Prove2me | Definitions.Def_BondySimonovitsLib_BSBasic
-- name    : BondySimonovitsLib_BSBasic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:02:29.938043+00:00
-- url     : https://prove2.me/theorems/1b6b97a4-85c9-44bb-bc68-12cf1f1811ed
-- title:
--   BSBasic
-- statement:
--   Definitions and structural lemmas for BSBasic, from Juan Pablo Traverso Gianini (jtraverso/bondy-simonovits; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bondy-Simonovits even cycle theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BondySimonovits
section Cycle
variable {V : Type*}
end Cycle
section Degenerate
variable {V : Type*}
def ecount (K : SimpleGraph V) [DecidableRel K.Adj] (A B : Finset V) : ℕ :=
  ∑ a ∈ A, (B.filter (K.Adj a)).card
end Degenerate
section MaxCut
variable {V : Type*} [Fintype V]
end MaxCut
end BondySimonovits


