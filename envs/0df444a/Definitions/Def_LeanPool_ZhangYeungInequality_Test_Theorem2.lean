-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Test_Theorem2
-- name    : LeanPool_ZhangYeungInequality_Test_Theorem2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:14:21.126548+00:00
-- url     : https://prove2.me/theorems/f5460320-5140-4914-9e0b-0f825a6bca80
-- title:
--   Theorem2
-- statement:
--   Definitions and structural lemmas for Theorem2, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Test/Theorem2.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem2
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_comm
public import Theorems.Thm_ProbabilityTheory_mutualInfo_comm
public import Theorems.Thm_ZhangYeung_theorem2

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeungTest
open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR
universe u
section Signature
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y; μ] = 0)
    (h₂ : I[X : Y|Z;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[Z : U | ⟨X, Y⟩; μ] + I[X : Y | U; μ] :=
  theorem2 hX hY hZ hU μ h₁ h₂
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y; μ] = 0)
    (h₂ : I[X : Y|Z;μ] = 0)
    (h₃ : I[Z : U|⟨X, Y⟩;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[X : Y | U; μ] := by
  have h := theorem2 hX hY hZ hU μ h₁ h₂
  linarith [h, h₃]
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[Y : X; μ] = 0)
    (h₂ : I[Y : X|Z;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[Z : U | ⟨X, Y⟩; μ] + I[X : Y | U; μ] :=
  theorem2 hX hY hZ hU μ ((mutualInfo_comm hY hX μ).symm.trans h₁)
    ((condMutualInfo_comm hY hX Z μ).symm.trans h₂)
end Signature
section ConcreteFintype
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 3} {Z : Ω → Fin 4} {U : Ω → Fin 5}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h₁ : I[X : Y; μ] = 0)
    (h₂ : I[X : Y|Z;μ] = 0) :
    I[X : Y | ⟨Z, U⟩; μ] ≤ I[Z : U | ⟨X, Y⟩; μ] + I[X : Y | U; μ] :=
  theorem2 hX hY hZ hU μ h₁ h₂
end ConcreteFintype
end ZhangYeungTest


