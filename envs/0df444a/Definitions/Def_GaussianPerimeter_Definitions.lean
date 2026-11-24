-- Prove2me | Definitions.Def_GaussianPerimeter_Definitions
-- name    : GaussianPerimeter_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:05:57.506117+00:00
-- url     : https://prove2.me/theorems/2b030dc5-b099-48ad-bfe5-96d28ca77e9d
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Definitions.lean

module
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Filter MeasureTheory
open scoped ENNReal
namespace GaussianPerimeter
noncomputable def gaussianPerimeter : {n : ℕ} → Set (EuclideanSpace ℝ (Fin n)) → ℝ≥0∞
  | 0, _ => 0
  | k + 1, K =>
    let normalization := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k
    let density (x : EuclideanSpace ℝ (Fin (k + 1))) :=
      ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
    normalization * (∫⁻ x in frontier K, density x ∂μH[(k : ℝ)])
noncomputable def Γ (n : ℕ) : ℝ≥0∞ :=
  ⨆ (K : Set (EuclideanSpace ℝ (Fin n))) (_ : Convex ℝ K), gaussianPerimeter K
end GaussianPerimeter


