-- Prove2me | Definitions.Def_RamseyReservoir
-- name    : RamseyReservoir
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:35:33.989351+00:00
-- url     : https://prove2.me/theorems/82d52904-a7bf-544c-b7ae-842e6905b64f
-- title:
--   Ramsey Reservoir
-- statement:
--   Definitions and structural lemmas for Ramsey Reservoir, from Brian Sanders (Egly443/lean-ramsey-reservoir; see pinned Apache-2.0 LICENSE and source headers)'s pinned Reservoir and book calculus for greedy Ramsey arguments development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir.lean

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Definitions.Def_RamseyReservoir_Book
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
set_option autoImplicit true
@[expose] public section


