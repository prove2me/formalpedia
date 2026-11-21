-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
-- name    : LeanPool_ChannelCapacity_StrictConcavity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:39:58.665913+00:00
-- url     : https://prove2.me/theorems/d94a8145-e6ca-4ed1-a0bc-03c88a4a965d
-- title:
--   Strict Concavity
-- statement:
--   Definitions and structural lemmas for Strict Concavity, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.Probability.Kernel.Composition.MeasureComp
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
namespace ProbabilityMeasure
variable {α : Type*} [MeasurableSpace α]
end ProbabilityMeasure
namespace ChannelCapacity
open ProbabilityMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
namespace Kernel
end Kernel
end ChannelCapacity


