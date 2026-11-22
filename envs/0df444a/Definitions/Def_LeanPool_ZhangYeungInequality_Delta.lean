-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Delta
-- name    : LeanPool_ZhangYeungInequality_Delta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:51:14.924346+00:00
-- url     : https://prove2.me/theorems/3a43d092-543d-4c8a-812d-84fa4f3fc90f
-- title:
--   Delta
-- statement:
--   Definitions and structural lemmas for Delta, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
noncomputable def delta
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄)
    (μ : Measure Ω := by volume_tac) : ℝ :=
  I[Z : U; μ] - I[Z : U | X; μ] - I[Z : U | Y; μ]
section MeasuredFinite
variable [Finite S₁] [Finite S₂]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
section AllFinite
variable [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
end AllFinite
end MeasuredFinite
end ZhangYeung


