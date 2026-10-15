-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Caps
-- name    : OAI_Probability_GaussianRegression_Caps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:15:21.479888+00:00
-- url     : https://prove2.me/theorems/17b09fd1-7ba9-46b2-81c1-8ba8af8ae257
-- title:
--   Indicator weight of a closed ball around an estimate
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra. For a point $y\in E$ and a radius $\varepsilon\in\mathbb{R}$, the cap weight is the indicator function of the closed ball of radius $\varepsilon$ around $y$, taken with values in $[0,\infty]$:
--   $$\kappa_{y,\varepsilon}(s)=\begin{cases}1, & \|s-y\|\le\varepsilon,\\ 0, & \text{otherwise},\end{cases}\qquad s\in E .$$
--   It vanishes identically when $\varepsilon<0$.
--
--   For a unit vector $y$ (an estimate) and a unit vector $s$ (the unknown direction), $\kappa_{y,\varepsilon}(s)=1$ exactly when $s$ lies in the spherical cap of chordal radius $\varepsilon$ around $y$. Since the chord $\|s-y\|$ never exceeds the angle $\arccos\langle s,y\rangle$, an angular error at most $\varepsilon$ implies $\kappa_{y,\varepsilon}(s)=1$. Used as terminal weights of continuation values, cap weights express the success probability of a sequential learner as an integral of a weight bounded by $1$, and the polynomial ball-mass bounds of the cap-weighted sphere law are then propagated along the stream of observations.
--
--   **Formalization Note** The Lean name is `capWeight y ε`, defined as `(Metric.closedBall y ε).indicator (fun _ => 1)` with values in `ℝ≥0∞`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Caps.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Caps.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Definitions.Def_OAI_Probability_GaussianRegression_Stream

namespace OAI

/-!
Spherical cap mass bounds along sequential routes.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

def capWeight (y : E) (ε : ℝ) : E → ℝ≥0∞ :=
  (Metric.closedBall y ε).indicator (fun _ => 1)

end StreamCaps

end NoiselessRegression

end

end OAI


