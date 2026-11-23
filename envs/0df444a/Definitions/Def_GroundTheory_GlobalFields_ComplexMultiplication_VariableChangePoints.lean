-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:42.788209+00:00
-- url     : https://prove2.me/theorems/1724e7c5-1ab4-46db-9f8c-c0c6740a6ac4
-- title:
--   Variable Change Points
-- statement:
--   Definitions and structural lemmas for Variable Change Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/VariableChangePoints.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open WeierstrassCurve
variable {F : Type*} [Field F]
section VariableChangePoint
theorem nonsingular_variableChange (C : VariableChange F) (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (↑C.u⁻¹ ^ 2 * (x - C.r))
      (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  rw [Affine.nonsingular_iff'] at h ⊢
  obtain ⟨he, hd⟩ := h
  rw [Affine.equation_iff'] at he ⊢
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆]
  set v : F := ↑C.u⁻¹
  refine ⟨?_, ?_⟩
  · linear_combination v ^ 6 * he
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hY : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have : v ^ 3 * (2 * y + W.a₁ * x + W.a₃) = 0 := by linear_combination h2
      simpa [hv] using this
    have hX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 := by
      have : v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 0 := by
        linear_combination h1 - v ^ 4 * C.s * hY
      simpa [hv] using this
    rcases hd with hd | hd
    · exact hd hX
    · exact hd hY
def variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F} (hC : C • W = W') :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
      (by subst hC; exact nonsingular_variableChange C W h)
end VariableChangePoint
end GroundTheory.Global


