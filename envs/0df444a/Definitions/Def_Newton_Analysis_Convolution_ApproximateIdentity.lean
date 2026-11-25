-- Prove2me | Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
-- name    : Newton_Analysis_Convolution_ApproximateIdentity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:42:45.445624+00:00
-- url     : https://prove2.me/theorems/43c1a96c-5063-47ae-8fec-503e2fd583c3
-- title:
--   Approximate Identity
-- statement:
--   Definitions and structural lemmas for Approximate Identity, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
namespace Newton
variable {n : ℕ}
structure IsApproximateIdentity (ψ : (Fin n → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ
  compact_support : HasCompactSupport ψ
  normalized : ∫ x, ψ x = 1
  nonneg : ∀ x, 0 ≤ ψ x
  support_subset : tsupport ψ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1
noncomputable def scaledMollifier (ψ : (Fin n → ℝ) → ℝ) (η : ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)
section ScaledMollifierFacts
variable {ψ : (Fin n → ℝ) → ℝ}
end ScaledMollifierFacts
end Newton


