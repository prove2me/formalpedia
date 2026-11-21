-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_ChainRule
-- name    : LeanPool_ChannelCapacity_ChainRule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:39:35.79855+00:00
-- url     : https://prove2.me/theorems/918a4640-2fe1-49bf-951c-41c71c50cf28
-- title:
--   Chain Rule
-- statement:
--   Definitions and structural lemmas for Chain Rule, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/ChainRule.lean

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Posterior
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ChannelCapacity
open InformationTheory
end ChannelCapacity


