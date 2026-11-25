-- Prove2me | Definitions.Def_DiscreteStability_Basic
-- name    : DiscreteStability_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:26:16.706123+00:00
-- url     : https://prove2.me/theorems/2e0330f7-960c-4df1-91fa-e241f38121f5
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from B. J. Ridenhour (magbenji/discrete-modified-gradient-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Stability of equilibria in discrete-time modified-gradient systems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basic.lean

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit true
open scoped RealInnerProductSpace
namespace DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
structure StepBound (P : E →L[ℝ] E) (lo hi : ℝ) : Prop where
  symm : ∀ u v, ⟪P u, v⟫ = ⟪u, P v⟫
  lo_nonneg : 0 ≤ lo
  lo_le_hi : lo ≤ hi
  lower : ∀ u, lo * ‖u‖ ^ 2 ≤ ⟪P u, u⟫
  upper : ∀ u, ⟪P u, u⟫ ≤ hi * ‖u‖ ^ 2
def IsOrbit (P : ℕ → E →L[ℝ] E) (g : E → E) (k₀ : ℕ) (x : ℕ → E) : Prop :=
  ∀ k ≥ k₀, x (k + 1) = x k + P k (g (x k))
namespace StepBound
variable {P : E →L[ℝ] E} {lo hi : ℝ}
end StepBound
end DiscreteStability


