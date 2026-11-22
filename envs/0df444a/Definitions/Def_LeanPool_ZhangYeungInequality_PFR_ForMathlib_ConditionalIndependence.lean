-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
-- name    : LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:23:16.704971+00:00
-- url     : https://prove2.me/theorems/77847c37-ca6c-4402-970a-cdaa610c8b08
-- title:
--   Conditional Independence
-- statement:
--   Definitions and structural lemmas for Conditional Independence, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/ConditionalIndependence.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Measure Set
open scoped ENNReal ZhangYeungPFR
namespace ProbabilityTheory
section
variable {Ω α β : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α} {_ :
  MeasurableSpace β}
  {μ : Measure Ω} {A : Ω → α} {B : Ω → β}
end
section defs
variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω
    → β} {h : Ω → γ}
def _root_.ProbabilityTheory.CondIndepFun
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) (μ : Measure Ω :=
  by volume_tac) : Prop :=
  ∀ᵐ z ∂ (μ.map h), IndepFun f g (μ[|h ← z])
variable [MeasurableSingletonClass γ]
end defs
section copy
universe u
variable {Ω : Type*} {α β :
  Type u} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
variable [Countable β]
open Function Set Measure
end copy
end ProbabilityTheory


