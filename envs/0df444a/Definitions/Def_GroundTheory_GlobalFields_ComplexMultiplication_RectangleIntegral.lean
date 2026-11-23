-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:51.201162+00:00
-- url     : https://prove2.me/theorems/1ea7867d-9391-45a3-bc03-d5972b21dacd
-- title:
--   Rectangle Integral
-- statement:
--   Definitions and structural lemmas for Rectangle Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean

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
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def rectIntegral (f : ℂ → E) (z w : ℂ) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))
def rectBoundary (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    {w.re} ×ℂ [[z.im, w.im]]
section Edges
variable {z w : ℂ}
variable {f g : ℂ → E}
end Edges
section Linearity
variable {z w : ℂ} {f g : ℂ → E}
end Linearity
section Derivative
variable {z w : ℂ}
end Derivative
section Inverse
def invPrimitive (c x : ℝ) : ℂ :=
  ((Real.log (x ^ 2 + c ^ 2) / 2 : ℝ) : ℂ) - I * ((Real.arctan (x / c) : ℝ) : ℂ)
end Inverse
section Cauchy
end Cauchy
section Periodic
end Periodic
end Elliptic
end GroundTheory.Global


