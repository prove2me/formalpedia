-- Prove2me | Definitions.Def_BicausalOT_Defs
-- name    : BicausalOT_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T07:58:36.104611+00:00
-- url     : https://prove2.me/theorems/7e65201a-579d-421d-9c34-f8135f5f77da
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Defs.lean

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
def CouplingSet₀ (μ₀ : Measure X₀) (ν₀ : Measure Y₀) :
    Set (Measure (X₀ × Y₀)) :=
  { γ | γ.map Prod.fst = μ₀ ∧ γ.map Prod.snd = ν₀ }
def FeasibleSet₀
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀) : Set (Measure (X₁ × Y₁)) :=
  { γ | γ.map Prod.fst = κ_μ z₀.1 ∧ γ.map Prod.snd = κ_ν z₀.2 }
structure KernelDecomp
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁))) where
  γ₀ : Measure (X₀ × Y₀)
  γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁)
  γ₁_measurable : Measurable γ₁
  decomp : ∀ ⦃s : Set ((X₀ × X₁) × (Y₀ × Y₁))⦄,
    MeasurableSet s →
    π s = ∫⁻ z₀, (γ₁ z₀) {z₁ | ((z₀.1, z₁.1), (z₀.2, z₁.2)) ∈ s} ∂γ₀
def IsBicausal₂
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁))) : Prop :=
  ∃ (kd : KernelDecomp π),
    kd.γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
    ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
def V₀ (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀) : ENNReal :=
  c₀ z₀ + ⨅ (γ : Measure (X₁ × Y₁)) (_ : γ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
    ∫⁻ z₁, c₁ (z₀, z₁) ∂γ
def totalCost (kd_γ₀ : Measure (X₀ × Y₀))
    (kd_γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁)) : ENNReal :=
  ∫⁻ z₀, (c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂(kd_γ₁ z₀)) ∂kd_γ₀
end


