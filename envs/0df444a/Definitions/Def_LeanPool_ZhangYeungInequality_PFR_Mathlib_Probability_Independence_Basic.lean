-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:22:14.122108+00:00
-- url     : https://prove2.me/theorems/9ca71fab-cde7-4cad-89f5-411df871e530
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
namespace ProbabilityTheory
variable {Ω ι β β' γ : Type*} {κ : ι
  → Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β}
  {g : Ω → β'}
end ProbabilityTheory
namespace ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}
section IndepFun
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω
  → β} {g : Ω → β'}
section iIndepFun
variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  [n : ∀ i, MeasurableSpace (α i)]
  [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → α i}
  {μ : Measure Ω}
universe u
end iIndepFun
variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
variable {f : Ω → α} {g : Ω → β}
end IndepFun
end ProbabilityTheory
namespace ProbabilityTheory
variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i,
  κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}
variable [Fintype ι] [∀ i, Fintype (κ i)]
variable {ι : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
  {α : ∀ i, κ i → Type*} {f : ∀ i j, Ω → α i j} [m : ∀ i j, MeasurableSpace (α i j)]
variable {ι ι' : Type*} {α : ι → Type*}
    {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}
variable {β β' Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
end ProbabilityTheory


