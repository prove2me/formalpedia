-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_Seeded
-- name    : OAI_Probability_ProjectionMoments_Seeded
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:30:50.552732+00:00
-- url     : https://prove2.me/theorems/085bc1f4-90f0-458c-8216-6c7031033657
-- title:
--   Memory lower bound for seeded finite-kernel learners
-- statement:
--   The subquadratic-memory statement for seeded families of finite-kernel learners: there is $c>0$ such that for every memory budget $M(d)=o(d^2)$, eventually in $d$, for every $T$ and $0<\varepsilon\le\frac1{10}$, every probability space of seeds $\xi\sim\rho$ and every family of finite-kernel learners $K_\xi$ with $M(d)$ bits whose rules are almost surely completed (measurable in the observation),
--   $$
--   \mathrm{succ}_\varepsilon\ge\tfrac23\ \Longrightarrow\ T\ge c\,d\log(1/\varepsilon),
--   $$
--   where the success is averaged over seeds and the uniform sphere.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Seeded.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Seeded.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner

section
open Learner
variable {d M T : ℕ}

end

universe u
variable {d M T : ℕ}

def SubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d:ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
    ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
    (2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε →
    c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)

end FiniteKernelLearner

end NoiselessRegression

end

end OAI


