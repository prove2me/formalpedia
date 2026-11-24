-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
-- name    : ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:00.555251+00:00
-- url     : https://prove2.me/theorems/6bd250d5-a6cb-4c0c-aacf-9b78bfed558b
-- title:
--   Bergman Defs
-- statement:
--   Definitions and structural lemmas for Bergman Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
variable {X : Type*} [MeasurableSpace X]
def bGram (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ∫ x, starRingEnd ℂ (s i x) * s j x * (w x : ℂ) ∂μ
def bNormSq (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (c : Fin r → ℂ) : ℝ :=
  ∫ x, ‖∑ i, c i * s i x‖ ^ 2 * w x ∂μ
def bergmanDensity (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (x : X) : ℝ :=
  w x * (∑ i, ∑ j, (bGram μ s w)⁻¹ i j * s i x * starRingEnd ℂ (s j x)).re
end ReciprocityTheory.GeometryOfNumbersTheory


