-- Prove2me | Definitions.Def_BondySimonovitsLib_BSCycle
-- name    : BondySimonovitsLib_BSCycle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:03:28.736233+00:00
-- url     : https://prove2.me/theorems/844cf3fb-9705-4f7a-8485-a3605358cfc6
-- title:
--   BSCycle
-- statement:
--   Definitions and structural lemmas for BSCycle, from Juan Pablo Traverso Gianini (jtraverso/bondy-simonovits; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bondy-Simonovits even cycle theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSCycle.lean

module
public import Definitions.Def_BondySimonovitsLib_BSLayers
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BondySimonovits
section KeyLemma
variable {V : Type*} (K : SimpleGraph V) [DecidableRel K.Adj]
end KeyLemma
end BondySimonovits


