-- Prove2me | solution 1 for Auto.iteratedDeriv_gaussian_conv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:04:50.374735+00:00
-- url     : https://prove2.me/submissions/3cd1f872-91f1-42c3-a94c-7709dd3c536d

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hasDerivAt_gaussianD_conv

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
open Real
namespace Auto
theorem _root_.solution (i : ℕ) {σ : ℝ} (hσ : 0 < σ) {G : ℝ → ℝ} (hG : Integrable G) :
    iteratedDeriv i (fun t => ∫ d, gaussian σ (t - d) * G d) = fun t => ∫ d, gaussianD i σ (t -
      d) * G d := by
  induction i with
  | zero => simp [gaussianD_zero]
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_gaussianD_conv i hσ hG t).deriv
end Auto
