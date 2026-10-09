-- Prove2me | Definitions.Def_ModernOnlineLearning_OGD_Defs
-- name    : ModernOnlineLearning_OGD_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:43.437257+00:00
-- url     : https://prove2.me/theorems/16459b7d-5d0c-4fa5-84e2-9991165154dd
-- title:
--   Regret against a fixed comparator and Algorithm 2.1 run
-- statement:
--   For losses $\ell_t$, decisions $x_t$, a fixed competitor $u$, and rounds $1,\ldots,T$, regret is
--   $$\operatorname{Regret}_T(u)=\sum_{t=1}^T(\ell_t(x_t)-\ell_t(u)).$$
--
--   A run of projected online gradient descent uses a nonempty closed convex set $V$ and positive step sizes $\eta_t$. Each loss $\ell_t$ is convex and differentiable on an open set containing $V$; since losses are real-valued in Lean, convexity is required on some open set containing $V$ (the interior of the book's effective domain), not on the whole space. The run begins at $x_1\in V$; in each round $t\le T$, $g_t$ is the gradient of $\ell_t$ at $x_t$, and $x_{t+1}$ is a nearest point in $V$ to $x_t-\eta_tg_t$. A relative subgradient on $V$ is a vector satisfying $f(y)\ge f(x)+\langle g,y-x\rangle$ for all $y\in V$.
--
--   These definitions fix the book's one-based time convention and permit any valid projection or gradient choice. The ambient complete real inner-product space includes the book's Euclidean setting.
-- source:
--   Orabona, arXiv:1912.13213v10, §1 p. 2, Algorithm 2.1 p. 12, Definition 2.20 p. 16

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

namespace ModernOnlineLearning.OGD

/-- Regret against one fixed comparator, with the book's rounds numbered from one. -/
def regret {E : Type*} (loss : ℕ → E → ℝ) (x : ℕ → E) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (loss t (x t) - loss t u)

/-- A run of Algorithm 2.1 through round `T`, including the conditions in its
`Require` line and on its losses. A convex `ℓ_t : ℝ^d → (−∞, +∞]` differentiable on an
open set containing `V` is finite and convex on the open convex set `int (dom ℓ_t) ⊇ V`,
so the real-valued loss is required to be convex on some open set containing `V`, not on
the whole space. The gradient and projection may be any
admissible choices, and index zero is unused. -/
def IsOGDRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (loss : ℕ → E → ℝ) (η : ℕ → ℝ)
    (x g : ℕ → E) (T : ℕ) : Prop :=
  V.Nonempty ∧ IsClosed V ∧ Convex ℝ V ∧ x 1 ∈ V ∧
    ∀ t ∈ Finset.Icc 1 T,
      0 < η t ∧
      (∃ C : Set E, IsOpen C ∧ V ⊆ C ∧ ConvexOn ℝ C (loss t)) ∧
      (∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ DifferentiableOn ℝ (loss t) U) ∧
      HasGradientAt (loss t) (g t) (x t) ∧
      OnlineConvexOpt.FirstOrder.IsMetricProjection V (x t - η t • g t) (x (t + 1))

/-- Relative subgradient inequality on the decision set. -/
def IsSubgradientOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Set E) (f : E → ℝ) (x g : E) : Prop :=
  ∀ y ∈ V, f x + inner ℝ g (y - x) ≤ f y

end ModernOnlineLearning.OGD


