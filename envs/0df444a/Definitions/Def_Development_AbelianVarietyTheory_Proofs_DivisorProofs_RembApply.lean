-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:46.46358+00:00
-- url     : https://prove2.me/theorems/059fe1a4-41d5-4b7d-b840-fd4810688807
-- title:
--   Remb Apply
-- statement:
--   Definitions and structural lemmas for Remb Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RembApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
namespace GlobalTheory.LipschitzTR
variable (F : Type) [Field F] [NumberField F]
abbrev RSp := EuclideanSpace ℝ (F →+* ℝ)
def remb : F →+ RSp F where
  toFun a := WithLp.toLp 2 (fun τ : F →+* ℝ => τ a)
  map_zero' := by ext τ; simp
  map_add' a b := by ext τ; simp
variable {F}
def latOf (N : FractionalIdeal (𝓞 F)⁰ F) : Submodule ℤ (RSp F) :=
  Submodule.map (remb F).toIntLinearMap ((N : Submodule (𝓞 F) F).restrictScalars ℤ)
def phi1 (k : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w)
  else 0
def Phi (k : ℕ) (z : (F →+* ℝ) → ℂ) (ξ : RSp F) : ℂ :=
  ∏ τ : F →+* ℝ, phi1 k (z τ) (ξ τ)
example : phi1 2 Complex.I 1 ≠ 0 := by
  simp [phi1, Complex.exp_ne_zero]
end GlobalTheory.LipschitzTR


