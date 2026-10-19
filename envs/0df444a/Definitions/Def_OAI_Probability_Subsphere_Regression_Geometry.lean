-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
-- name    : OAI_Probability_Subsphere_Regression_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:28:51.443349+00:00
-- url     : https://prove2.me/theorems/97d8d2ff-766b-4436-8f5d-3ae6e1c0e640
-- title:
--   Local mass bound: closed balls centred on the support of a measure have mass at most $r^a$
-- statement:
--   Let $(E,\|\cdot\|)$ be a normed abelian group (in applications a finite-dimensional real normed space) equipped with a $\sigma$-algebra, let $\nu$ be a measure on $E$ and let $a\in\mathbb{R}$. The support $\operatorname{supp}\nu$ is the set of points $t\in E$ every neighbourhood of which has positive $\nu$-measure, and $\overline B(t,r)=\{x\in E:\|x-t\|\le r\}$ denotes the closed ball.
--
--   The measure $\nu$ *has a local mass bound with exponent $a$* if
--
--   $$
--   \nu\bigl(\overline B(t,r)\bigr)\le r^{a}\qquad\text{for every } t\in\operatorname{supp}\nu \text{ and every real } r>0 .
--   $$
--
--   This is a Frostman-type (upper Ahlfors-regularity) condition with constant $1$, required only at centres lying in the support: it says that $\nu$ is spread out at dimension at least $a$ around each of its points. In the regression lower bound it is the regularity hypothesis on the distribution $\nu$ of the hidden vector under which moment bounds for the resulting observation laws are proved.
--
--   **Formalization Note** `HasLocalMassBound ν a`; the right-hand side is `ENNReal.ofReal (r ^ a)` with the real power $r^a$, and the support is Mathlib's `Measure.support`. The definition uses only the metric and the measurable structure of $E$; the finite-dimensionality, normed-space and Borel assumptions of the surrounding section are not arguments of the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Geometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Geometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
section InverseMoments

variable {X : Type*} [MeasurableSpace X]

end InverseMoments

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

section EuclideanNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end EuclideanNets

section AffineTubes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open EuclideanGeometry

end AffineTubes

open InnerProductSpace

end SubsphereRegression
end
end

end OAI


