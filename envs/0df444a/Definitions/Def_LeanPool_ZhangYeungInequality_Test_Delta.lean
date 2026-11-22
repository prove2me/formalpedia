-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Test_Delta
-- name    : LeanPool_ZhangYeungInequality_Test_Delta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:11:34.641385+00:00
-- url     : https://prove2.me/theorems/c15f10fe-58c5-4831-bd01-afee60d81919
-- title:
--   Delta
-- statement:
--   Definitions and structural lemmas for Delta, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Test/Delta.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_ZhangYeung_delta_comm_cond
public import Theorems.Thm_ZhangYeung_delta_comm_main
public import Theorems.Thm_ZhangYeung_delta_def
public import Theorems.Thm_ZhangYeung_delta_eq_entropy
public import Theorems.Thm_ZhangYeung_delta_form21_iff
public import Theorems.Thm_ZhangYeung_delta_form22_iff
public import Theorems.Thm_ZhangYeung_delta_form23_iff
public import Theorems.Thm_ZhangYeung_delta_form23_of_form21_form22
public import Theorems.Thm_ZhangYeung_delta_le_mutualInfo
public import Theorems.Thm_ZhangYeung_delta_self
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] ProbabilityTheory.Kernel.entropy_compProd_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_const
attribute [local simp] ProbabilityTheory.Kernel.entropy_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_prod
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkLeft
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkRight
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteRight_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_snd_reverse
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeungTest
open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR
section PureAlgebra
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = I[Z : U; μ] - I[Z : U|X;μ] - I[Z : U|Y;μ] := by
  simpa using delta_def Z U X Y μ
example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta Z U Y X μ := by
  simpa using delta_comm_cond Z U X Y μ
example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (μ : Measure Ω) :
    delta Z U X X μ = I[Z : U; μ] - 2 * I[Z : U|X;μ] := by
  simpa using delta_self Z U X μ
example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    (2 * delta Z U X Y μ
        ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
          + I[Z : U|X;μ] - I[Z : U|Y;μ]) ↔
      (2 * I[Z : U; μ] - 3 * I[Z : U|X;μ] - I[Z : U|Y;μ]
        ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]) := by
  simpa using delta_form21_iff Z U X Y μ
example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    (2 * delta Z U X Y μ
        ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]
          - I[Z : U|X;μ] + I[Z : U|Y;μ]) ↔
      (2 * I[Z : U; μ] - I[Z : U|X;μ] - 3 * I[Z : U|Y;μ]
        ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]) := by
  simpa using delta_form22_iff Z U X Y μ
example (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω)
    (h21 : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] + I[Z : U|X;μ] - I[Z : U|Y;μ])
    (h22 : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ] - I[Z : U|X;μ] + I[Z : U|Y;μ]) :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]) := by
  apply (delta_form23_iff Z U X Y μ).mp
  exact delta_form23_of_form21_form22 h21 h22
end PureAlgebra
section FiniteAlphabet
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
example {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta U Z X Y μ := by
  simpa using delta_comm_main hZ hU μ
example {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄}
    (hZ : Measurable Z) (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      = (H[Z; μ] + H[U; μ] - H[⟨Z, U⟩; μ])
        - (H[Z | X; μ] + H[U | X; μ] - H[⟨Z, U⟩ | X; μ])
        - (H[Z | Y; μ] + H[U | Y; μ] - H[⟨Z, U⟩ | Y; μ]) := by
  simpa using delta_eq_entropy hZ hU hX hY μ
example {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    delta Z U X Y μ ≤ I[Z : U; μ] := by
  simpa using delta_le_mutualInfo hZ hU μ
end FiniteAlphabet
end ZhangYeungTest


