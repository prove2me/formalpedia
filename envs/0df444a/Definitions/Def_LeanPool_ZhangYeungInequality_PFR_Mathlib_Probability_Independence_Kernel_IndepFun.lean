-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:21:55.594882+00:00
-- url     : https://prove2.me/theorems/3b13fa1d-5f24-4f0d-a207-02c8610e8747
-- title:
--   Indep Fun
-- statement:
--   Definitions and structural lemmas for Indep Fun, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Kernel/IndepFun.lean

module
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory MeasurableSpace
open scoped MeasureTheory ENNReal
namespace ProbabilityTheory.Kernel
variable {ι α β β' γ γ' Ω : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}
section iIndepFun
variable {β γ : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {mγ : ∀ i,
  MeasurableSpace (γ i)}
  {f : ∀ i, Ω → β i}
end ProbabilityTheory.Kernel.iIndepFun


