-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:22:40.684139+00:00
-- url     : https://prove2.me/theorems/c937f740-5fd2-409c-b33a-2fbde72ebba7
-- title:
--   Ident Distrib
-- statement:
--   Definitions and structural lemmas for Ident Distrib, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
noncomputable section
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal
attribute [symm] ProbabilityTheory.IdentDistrib.symm
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]
namespace ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}
attribute [mk_iff] IdentDistrib
end ProbabilityTheory
open MeasureTheory ProbabilityTheory Function Set
namespace ProbabilityTheory
section IdentDistrib
universe u u' v
variable {Ω Ω' α ι β β' T : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω
    → β} {f' g' : Ω' → β}
variable [MeasurableSpace α] [MeasurableSpace β]
end IdentDistrib
end ProbabilityTheory


