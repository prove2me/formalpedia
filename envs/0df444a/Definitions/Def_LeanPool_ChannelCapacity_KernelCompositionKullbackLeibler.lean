-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
-- name    : LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:39:15.562848+00:00
-- url     : https://prove2.me/theorems/a1bff268-166d-4608-b346-0bc4da9d00d7
-- title:
--   Kernel Composition Kullback Leibler
-- statement:
--   Definitions and structural lemmas for Kernel Composition Kullback Leibler, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/KernelCompositionKullbackLeibler.lean

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CompProdEqIff
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace InformationTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
end InformationTheory
namespace ProbabilityTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
end ProbabilityTheory


