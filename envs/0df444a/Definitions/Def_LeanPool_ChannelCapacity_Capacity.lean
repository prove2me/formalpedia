-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_Capacity
-- name    : LeanPool_ChannelCapacity_Capacity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:40:28.941506+00:00
-- url     : https://prove2.me/theorems/a8c31d80-e9f5-4f4b-8c02-3d027b069908
-- title:
--   Capacity
-- statement:
--   Definitions and structural lemmas for Capacity, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Capacity.lean

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
namespace ChannelCapacity
open ProbabilityMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
noncomputable def channelCapacity (k : Kernel α β) [IsMarkovKernel k] : ℝ :=
  sSup (Set.range fun p : ProbabilityMeasure α => mutualInformation p k)
def IsCapacityAchievingPrior (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) : Prop :=
  mutualInformation p k = channelCapacity k
end ChannelCapacity


