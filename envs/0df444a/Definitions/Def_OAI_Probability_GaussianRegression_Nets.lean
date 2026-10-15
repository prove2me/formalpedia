-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Nets
-- name    : OAI_Probability_GaussianRegression_Nets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:02:31.831064+00:00
-- url     : https://prove2.me/theorems/68c0eb53-61b9-41e7-b899-74b8000a013e
-- title:
--   Local mass bound: a Frostman-type ball condition at support points
-- statement:
--   Let $E$ be a finite-dimensional real normed space equipped with a $\sigma$-algebra, let $\nu$ be a measure on $E$, and let $a\in\mathbb{R}$. The support $\operatorname{supp}\nu$ is the set of points $t\in E$ all of whose open neighbourhoods have positive $\nu$-measure, and $\bar B(t,r)=\{x\in E:\|x-t\|\le r\}$ denotes the closed ball.
--
--   The measure $\nu$ has a *local mass bound with exponent $a$* if
--   $$\nu\big(\bar B(t,r)\big)\le r^{a}\qquad\text{for every } t\in\operatorname{supp}\nu \text{ and every } r>0 .$$
--
--   This is an upper Frostman (upper Ahlfors-regularity) condition with constant $1$, required only for balls centered in the support. For a large exponent $a$ it prevents the measure from concentrating near points or near low-dimensional affine subspaces. This is the regularity property used to control inverse Gram–Schmidt moments of independent samples from $\nu$ in the lower-bound analysis of noiseless Gaussian regression; for example, the normalized Lebesgue measure on the unit ball of $E$ satisfies it with $a=\dim E$.
--
--   **Formalization Note** The Lean name is `HasLocalMassBound ν a`. The right-hand side is `ENNReal.ofReal (r ^ a)` with the real power $r^{a}$ of $r>0$, and $\nu$ of a closed ball is evaluated in $[0,\infty]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Nets.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Nets.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model

namespace OAI

/-!
Local mass bounds and quantitative finite Euclidean nets.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

universe u

namespace NoiselessRegression

section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def HasLocalMassBound (ν : Measure E) (a : ℝ) : Prop :=
  ∀ t ∈ ν.support, ∀ r : ℝ, 0 < r →
    ν (Metric.closedBall t r) ≤ ENNReal.ofReal (r ^ a)

end FrostmanGeometry

section FiniteNets

variable {E : Type*} [PseudoMetricSpace E]

end FiniteNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end NoiselessRegression

end

end OAI


