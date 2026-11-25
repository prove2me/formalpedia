-- Prove2me | Definitions.Def_DiscreteStability_Stability
-- name    : DiscreteStability_Stability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:38:03.590861+00:00
-- url     : https://prove2.me/theorems/5e636c96-33ca-4a70-a802-37f6694c4e1c
-- title:
--   Stability
-- statement:
--   Definitions and structural lemmas for Stability, from B. J. Ridenhour (magbenji/discrete-modified-gradient-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Stability of equilibria in discrete-time modified-gradient systems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean

import Definitions.Def_DiscreteStability_Ascent
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
namespace DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
structure LocalHyp (f : E → ℝ) (g : E → E) (xbar : E) (r₀ L : ℝ) : Prop where
  r₀_pos : 0 < r₀
  L_nonneg : 0 ≤ L
  grad : ∀ z ∈ closedBall xbar r₀, HasFDerivAt f (innerSL ℝ (g z)) z
  lip : ∀ u ∈ closedBall xbar r₀, ∀ v ∈ closedBall xbar r₀, ‖g u - g v‖ ≤ L * ‖u - v‖
def IsolatedMax (f : E → ℝ) (xbar : E) : Prop :=
  ∃ r > 0, ∀ x, x ≠ xbar → dist x xbar ≤ r → f x < f xbar
def IsolatedCrit (g : E → E) (xbar : E) : Prop :=
  ∃ r > 0, ∀ x, x ≠ xbar → dist x xbar ≤ r → g x ≠ 0
def UniformlyStable (P : ℕ → E →L[ℝ] E) (g : E → E) (xbar : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x →
    dist (x k₀) xbar < δ → ∀ k ≥ k₀, dist (x k) xbar < ε
def UniformlyAsympStable (P : ℕ → E →L[ℝ] E) (g : E → E) (xbar : E) : Prop :=
  UniformlyStable P g xbar ∧
    ∃ δ > 0, ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x →
      dist (x k₀) xbar < δ → Tendsto x atTop (𝓝 xbar)
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
variable [FiniteDimensional ℝ E]
end DiscreteStability


