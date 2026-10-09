-- Prove2me | Definitions.Def_ModernOnlineLearning_Adaptive_Defs
-- name    : ModernOnlineLearning_Adaptive_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:13.550833+00:00
-- url     : https://prove2.me/theorems/1ba7d194-308c-4b75-82a8-9ad29a55f7af
-- title:
--   Adaptive online subgradient descent, regret, and self-bounded losses
-- statement:
--   Let $V$ be a subset of a Euclidean space and let $\ell_t$ be real-valued losses. A vector $g$ is a subgradient of $f$ at $x$ when $f(y)\ge f(x)+\langle g,y-x\rangle$ for every point $y$ of the whole space. Regret against a fixed competitor $u$ through round $T$ is
--
--   $$\operatorname{Regret}_T(u)=\sum_{t=1}^T(\ell_t(x_t)-\ell_t(u)).$$
--
--   An adaptive OSD run uses a nonempty closed convex set $V$ with diameter at most $D>0$, begins at $x_1\in V$, and requires each loss to be subdifferentiable throughout $V$. At round $t$ it selects a subgradient $g_t$ and, if $g_t\ne0$, projects $x_t-\eta_tg_t$ onto $V$, where $\eta_t=\sqrt2D/(2\sqrt{\sum_{i=1}^t\|g_i\|_2^2})$. When $g_t=0$, it leaves $x_{t+1}=x_t$. Every permitted subgradient and projection choice is included.
--
--   A lower-bounded function $f$ is $s$-self-bounded on $V$ when it has a subgradient at every $x\in V$ and every such $g$ satisfies
--
--   $$\|g\|_2^2\le 2s\left(f(x)-\inf_{y\in\mathbb R^d}f(y)\right).$$
--
--   These definitions supply the shared objects for the adaptive regret bounds of Chapter 4.
--
--   **Formalization Note** Losses are real-valued; the book also permits $+\infty$ outside the feasible region. The infimum is taken over the full Euclidean space and is guarded by boundedness below. Rounds are numbered from one, and the run is restricted to a finite horizon. The condition $D>0$ ensures the positive step size required by Algorithm 2.2 whenever an update occurs.
-- source:
--   Orabona, arXiv:1912.13213v10, Definition 2.20, p. 16; Algorithm 2.2, p. 20; Theorem 4.14, p. 40; Definition 4.26, p. 43

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

namespace ModernOnlineLearning.Adaptive

/-- The Euclidean decision space of Chapter 4. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A full-space subgradient, as in Definition 2.20. -/
def IsSubgradient {d : ℕ} (f : Vec d → ℝ) (x g : Vec d) : Prop :=
  ∀ y : Vec d, f x + inner ℝ g (y - x) ≤ f y

/-- Regret against one fixed competitor, with rounds numbered from one. -/
def regret {d : ℕ} (ℓ : ℕ → Vec d → ℝ) (x : ℕ → Vec d)
    (u : Vec d) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)

/-- The sum of squared subgradient norms through the current round. -/
noncomputable def gradientEnergy {d : ℕ} (g : ℕ → Vec d) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 t, ‖g i‖ ^ 2

/-- The adaptive step size from Theorems 4.14 and 4.30. Its value on an
all-zero prefix is unused: the algorithm does not update on a zero gradient. -/
noncomputable def adaptiveStep {d : ℕ} (D : ℝ) (g : ℕ → Vec d) (t : ℕ) : ℝ :=
  Real.sqrt 2 * D / (2 * Real.sqrt (gradientEnergy g t))

/-- Algorithm 2.2 with the step size of Theorem 4.14, through round `T`.
The feasible-set and subdifferentiability conditions are included. The strict
positivity of `D` makes the printed step size positive whenever the gradient is
nonzero. Every admissible choice of a subgradient and projection is allowed. -/
def IsAdaptiveOSDRun {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D : ℝ) (T : ℕ) (x g : ℕ → Vec d) : Prop :=
  V.Nonempty ∧ IsClosed V ∧ Convex ℝ V ∧ 0 < D ∧
    (∀ a ∈ V, ∀ b ∈ V, ‖a - b‖ ≤ D) ∧ x 1 ∈ V ∧
    ∀ t ∈ Finset.Icc 1 T,
      (∀ z ∈ V, ∃ q : Vec d, IsSubgradient (ℓ t) z q) ∧
      IsSubgradient (ℓ t) (x t) (g t) ∧
      (g t = 0 → x (t + 1) = x t) ∧
      (g t ≠ 0 → OnlineConvexOpt.FirstOrder.IsMetricProjection V
        (x t - adaptiveStep D g t • g t) (x (t + 1)))

/-- Definition 4.26 for real-valued losses. The infimum is over the whole
Euclidean space, not just `V`; boundedness below prevents a junk infimum. -/
def IsSelfBounded {d : ℕ} (V : Set (Vec d)) (s : ℝ) (f : Vec d → ℝ) : Prop :=
  BddBelow (Set.range f) ∧
    (∀ x ∈ V, ∃ g : Vec d, IsSubgradient f x g) ∧
    ∀ x ∈ V, ∀ g : Vec d, IsSubgradient f x g →
      ‖g‖ ^ 2 ≤ 2 * s * (f x - sInf (Set.range f))

end ModernOnlineLearning.Adaptive


