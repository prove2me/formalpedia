-- Prove2me | Definitions.Def_MazurN13_scratch_TateZ2xZ10Reduction_p0
-- name    : MazurN13_scratch_TateZ2xZ10Reduction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:45:48.165335+00:00
-- url     : https://prove2.me/theorems/266dc24a-7a4e-465a-9eaf-fcd8a88ac7fd
-- title:
--   scratch.TateZ2xZ10Reduction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:scratch.TateZ2xZ10Reduction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: scratch.TateZ2xZ10Reduction
Original leading source comments and nonproject imports are retained below. -/
import Mathlib
import Definitions.Def_MazurN13_KeystoneInterface

set_option autoImplicit false

open scoped WeierstrassCurve.Affine
namespace Scratch.TateZ2xZ10Reduction
noncomputable section
/-- The Tate normal form `y^2 + (1-c)xy - by = x^3 - bx^2`. -/
def tateNormalFormCurve (b c : ℚ) : WeierstrassCurve ℚ where
  a₁ := 1 - c
  a₂ := -b
  a₃ := -b
  a₄ := 0
  a₆ := 0

@[simp] lemma tateNormalFormCurve_a₁ (b c : ℚ) :
    (tateNormalFormCurve b c).a₁ = 1 - c := rfl

@[simp] lemma tateNormalFormCurve_a₂ (b c : ℚ) :
    (tateNormalFormCurve b c).a₂ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₃ (b c : ℚ) :
    (tateNormalFormCurve b c).a₃ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₄ (b c : ℚ) :
    (tateNormalFormCurve b c).a₄ = 0 := rfl

@[simp] lemma tateNormalFormCurve_a₆ (b c : ℚ) :
    (tateNormalFormCurve b c).a₆ = 0 := rfl
end
end Scratch.TateZ2xZ10Reduction


