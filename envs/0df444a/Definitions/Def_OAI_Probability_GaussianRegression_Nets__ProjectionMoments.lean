-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Nets__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:32:54.499446+00:00
-- url     : https://prove2.me/theorems/af0d758f-ebf3-43a4-a261-119c3381ed3f
-- title:
--   Local mass bounds for measures
-- statement:
--   For a measure $\nu$ on a finite-dimensional real normed space and an exponent $a$, $\nu$ has a local mass bound with exponent $a$ if every closed ball centred at a point of its support has mass at most its radius to the power $a$:
--   $$
--   \nu\bigl(\bar B(t,r)\bigr)\le r^{a}\qquad(t\in\operatorname{supp}\nu,\ r>0).
--   $$
--
--   Such Frostman-type bounds control how concentrated $\nu$ can be, and they are the input to the finite net arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Nets.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Nets.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model

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


