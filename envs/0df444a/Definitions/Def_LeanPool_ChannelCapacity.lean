-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity
-- name    : LeanPool_ChannelCapacity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:49:28.750178+00:00
-- url     : https://prove2.me/theorems/48a8ff9f-607d-4be7-9faf-4fbb68c61bf5
-- title:
--   Channel Capacity
-- statement:
--   Definitions and structural lemmas for Channel Capacity, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity.lean

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Definitions.Def_LeanPool_ChannelCapacity_DischargedExample
public import Definitions.Def_LeanPool_ChannelCapacity_Counterexample
set_option autoImplicit true
@[expose] public section
@[expose] public section


