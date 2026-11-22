-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
-- name    : LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:22:56.844946+00:00
-- url     : https://prove2.me/theorems/e0d3dbe6-d1a7-4496-85df-2a88f974002d
-- title:
--   Uniform
-- statement:
--   Definitions and structural lemmas for Uniform, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Function MeasureTheory Measure Set
open scoped ENNReal
namespace ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
structure IsUniform (H : Set S) (X : Ω → S) (μ : Measure Ω := by volume_tac) : Prop where
  eq_of_mem ⦃x⦄ (hx : x ∈ H) ⦃y⦄ (hy : y ∈ H) : μ (X ⁻¹' {x}) = μ (X ⁻¹' {y})
  measure_preimage_compl : μ (X ⁻¹' Hᶜ) = 0
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]
end ProbabilityTheory


