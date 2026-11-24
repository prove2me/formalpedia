-- Prove2me | Definitions.Def_BondySimonovitsLib_BSGrowth
-- name    : BondySimonovitsLib_BSGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:04:18.716937+00:00
-- url     : https://prove2.me/theorems/962c02db-e9c0-43ff-b1dd-ad7780341a3e
-- title:
--   BSGrowth
-- statement:
--   Definitions and structural lemmas for BSGrowth, from Juan Pablo Traverso Gianini (jtraverso/bondy-simonovits; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bondy-Simonovits even cycle theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BondySimonovits
section EdgeCount
variable {V : Type*} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
end EdgeCount
section Growth
end Growth
section Layers
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
noncomputable def layer (x : V) (i : ℕ) : Finset V :=
  univ.filter (fun v => K.Reachable x v ∧ K.dist x v = i)
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf
end Layers
end BondySimonovits


