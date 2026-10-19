-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
-- name    : OAI_Probability_ProjectionMoments_Kernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:23:58.726218+00:00
-- url     : https://prove2.me/theorems/8ff472d2-e343-47de-b6a3-a8e6516318c6
-- title:
--   Measurable kernel rules and coin-driven runs
-- statement:
--   Notions for finite-kernel learners, whose transitions and outputs are probability kernels on states.
--
--   1. **Borel rules.** A finite-kernel learner has Borel rules if each transition kernel is a measurable function of the observation.
--   2. **Coin runs.** For update maps $F_n(j,o,u)$ driven by observations $o$ and auxiliary coins $u$, the coin run applies them in order:
--   $$
--   \mathrm{run}_{n+1}(j,o,u)=F_{n+1}\bigl(\mathrm{run}_n(j,o_{<n},u_{<n}),o_n,u_n\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Kernels.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Kernels.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

namespace FiniteKernelLearner
variable {d M T : ℕ}

structure BorelRules (K : FiniteKernelLearner d M T) : Prop where
  transition : ∀ t j, Measurable (K.transition t j)

end FiniteKernelLearner

variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

def coinRun (F : ℕ → J → O → I → J) :
    (n : ℕ) → J → (Fin n → O) → (Fin n → I) → J
  | 0, j, _, _ => j
  | n+1, j, obs, u => F (n+1) (coinRun F n j (Fin.init obs) (Fin.init u)) (obs (Fin.last n)) (u (Fin.last n))

end NoiselessRegression

end

end OAI


