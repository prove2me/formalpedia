-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Test_Theorem3
-- name    : LeanPool_ZhangYeungInequality_Test_Theorem3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:20:09.393318+00:00
-- url     : https://prove2.me/theorems/2165e708-11a7-4910-9cda-f13dc99a3c6b
-- title:
--   Theorem3
-- statement:
--   Definitions and structural lemmas for Theorem3, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Test/Theorem3.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ZhangYeung_delta_form23_iff
public import Theorems.Thm_ZhangYeung_delta_form23_of_form21_form22
public import Theorems.Thm_ZhangYeung_delta_le_mutualInfo
public import Theorems.Thm_ZhangYeung_zhangYeung
public import Theorems.Thm_ZhangYeung_zhangYeung_averaged
public import Theorems.Thm_ZhangYeung_zhangYeung_dual

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeungTest
open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR
universe u
section Signatures
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ]) :=
  zhangYeung hX hY hZ hU μ
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]
        - I[Z : U | X; μ] + I[Z : U | Y; μ]) :=
  zhangYeung_dual hX hY hZ hU μ
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]) :=
  zhangYeung_averaged hX hY hZ hU μ
end Signatures
section IndependentSmokeTest
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 2} {Z : Ω → Fin 2} {U : Ω → Fin 2}
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) (hZU : I[Z : U; μ] = 0) :
    delta Z U X Y μ ≤ 0 := by
  have h := delta_le_mutualInfo (X := X) (Y := Y) hZ hU μ
  linarith [hZU]
end IndependentSmokeTest
section AveragedFromAsymmetric
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
example
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]) := by
  have h21 := zhangYeung hX hY hZ hU μ
  have h22 := zhangYeung_dual hX hY hZ hU μ
  have h21' : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ] := by linarith
  have h22' : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]
        - I[Z : U | X; μ] + I[Z : U | Y; μ] := by linarith
  exact (delta_form23_iff Z U X Y μ).mp (delta_form23_of_form21_form22 h21' h22')
end AveragedFromAsymmetric
section DownstreamUsage
example {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Fin 2} {Y : Ω → Fin 2} {Z : Ω → Fin 2} {U : Ω → Fin 2}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ] := by
  have h := zhangYeung hX hY hZ hU μ
  linarith
end DownstreamUsage
end ZhangYeungTest


