-- Prove2me | Definitions.Def_ModernOnlineLearning_Reductions_Setting
-- name    : ModernOnlineLearning_Reductions_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:31.458606+00:00
-- url     : https://prove2.me/theorems/99b4af1e-934f-42b9-9caf-4d4eeab3e1f4
-- title:
--   Definition 12.1 and Algorithm 12.1 — distance, generalized projection, and surrogate losses
-- statement:
--   Let $V$ be a nonempty subset of a finite-dimensional real normed space. Its distance function and generalized projection are
--   $$d_V(z)=\inf_{y\in V}\|z-y\|,\qquad \Pi_V(z)=\{x\in V:\|z-x\|=d_V(z)\}.$$
--   When $V$ is closed, the infimum is attained; the projection may contain more than one point. A full-space subgradient of $f$ at $x$ is a continuous linear functional $g$ satisfying $f(y)\ge f(x)+g(y-x)$ for every $y$. For original losses, the comparator form uses this inequality for every $y\in V$.
--
--   A projected run chooses $z_t\in W$, $x_t\in\Pi_V(z_t)$, a loss subgradient $g_t$ at $x_t$ on $V$, and a full-space subgradient $q_t$ of $d_V$ at $z_t$. Regret against fixed $u$ is $\sum_{t=1}^{T}(\ell_t(x_t)-\ell_t(u))$. The four surrogate losses are precisely the four formulas of Theorem 12.5, indexed from zero in their printed order.
--
--   These definitions let the reduction apply to every valid choice of the unconstrained learner and of a generalized projection.
--
--   **Formalization Note** The dual pairing is evaluation of a continuous linear functional, and its norm is the operator norm. The index zero of each sequence is unused.
-- source:
--   Orabona, arXiv:1912.13213v10, Definition 12.1, p. 193; Algorithm 12.1 and Theorem 12.5, pp. 195–196; §1, p. 2

import Mathlib
import Definitions.Def_ModernOnlineLearning_OGD_Defs
import Definitions.Def_ModernOnlineLearning_OMD_Defs

namespace ModernOnlineLearning.Reductions

/-- Definition 12.1: the distance from a point to a nonempty set, in the ambient norm. -/
noncomputable def distance {E : Type*} [NormedAddCommGroup E] (V : Set E) (z : E) : ℝ :=
  Metric.infDist z V

/-- Definition 12.1: any nearest point, allowing nonunique projections. -/
def IsProjection {E : Type*} [NormedAddCommGroup E]
    (V : Set E) (z x : E) : Prop :=
  x ∈ V ∧ ‖z - x‖ = distance V z

/-- The full-space subgradient used for the distance function and surrogate losses. -/
def IsSubgradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (g : E →L[ℝ] ℝ) : Prop :=
  ∀ y : E, f x + g (y - x) ≤ f y

/-- Algorithm 12.1, abstracting the unconstrained learner's choice of `z`. -/
def IsProjectedRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V W : Set E) (loss : ℕ → E → ℝ) (z x : ℕ → E)
    (g q : ℕ → E →L[ℝ] ℝ) (T : ℕ) : Prop :=
  (∀ t ∈ Finset.Icc 1 T, z t ∈ W ∧ IsProjection V (z t) (x t) ∧
    ModernOnlineLearning.OMD.IsSubgradientOn V (loss t) (x t) (g t) ∧
    IsSubgradient (distance V) (z t) (q t))

/-- The four losses in Theorem 12.5, indexed in their printed order by `0,1,2,3`. -/
noncomputable def surrogate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : Fin 4) (V : Set E) (g q : E →L[ℝ] ℝ) (x z w : E) : ℝ := by
  classical
  let c : ℝ := g ((‖x - z‖)⁻¹ • (x - z))
  exact if k.val = 0 then
    g w + ‖g‖ * distance V w
  else if k.val = 1 then
    g w + ‖g‖ * q w
  else if k.val = 2 then
    g w + (if g (x - z) ≤ 0 then 0 else c * distance V w)
  else
    g w + (if g (x - z) ≤ 0 then 0 else c * q w)

/-- Regret incurred by the unconstrained learner on one chosen surrogate sequence. -/
noncomputable def surrogateRegret {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : Fin 4) (V : Set E) (z x : ℕ → E) (g q : ℕ → E →L[ℝ] ℝ)
    (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T,
    (surrogate k V (g t) (q t) (x t) (z t) (z t) -
      surrogate k V (g t) (q t) (x t) (z t) u)

end ModernOnlineLearning.Reductions


