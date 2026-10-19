-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_Realization
-- name    : OAI_Probability_ProjectionMoments_Realization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:25:46.311987+00:00
-- url     : https://prove2.me/theorems/59646c7f-ce3f-4a3d-85bd-fe6aada5c4b4
-- title:
--   Realizing kernel learners by measurable rules on tapes
-- statement:
--   A realizer of a finite-kernel learner replaces each probability kernel by a measurable deterministic rule driven by an auxiliary uniform variable.
--
--   1. **Realizers.** A realizer consists of measurable transition rules $(t,j,\mathrm{obs},u)\mapsto(\text{stop},j')$ and output rules $(t,j,u)\mapsto s$ whose laws in $u$ are the learner's transition and output kernels.
--   2. **Tapes.** The tape law draws the initial (stop flag, state) from the learner's initial law, independent uniform coins for each time, and one more coin for the output; it is a probability measure.
--   3. **The realized learner.** On tapes, the realized learner starts from the tape's initial state, uses coin $t$ at time $t\in[1,T]$, and outputs with the final coin. Tagged transitions record stopping times, and terminal outputs pair the stop tag with the output:
--   $$
--   \mathrm{law}_u\bigl(\mathrm{trans}_t(j,\mathrm{obs},u)\bigr)=K_t(j,\mathrm{obs}).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Realization.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Realization.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

structure Realizer (K : FiniteKernelLearner d M T) where
  transition : ℕ → State M → (Vector d × ℝ) → I → Bool × State M
  transition_measurable : ∀ t j, Measurable (Function.uncurry (transition t j))
  transition_law : ∀ t j obs, volume.map (transition t j obs) = K.transition t j obs
  output : ℕ → State M → I → UnitSphere d
  output_measurable : ∀ t j, Measurable (output t j)
  output_law : ∀ t j, volume.map (output t j) = K.output t j

def tapeLaw (K : FiniteKernelLearner d M T) : Measure (Tape M T) :=
  K.initial.prod ((Measure.pi (fun _ => (volume : Measure I))).prod volume)

instance tapeLaw_probability (K : FiniteKernelLearner d M T) : IsProbabilityMeasure K.tapeLaw := by
  let := K.initial_probability
  unfold tapeLaw
  infer_instance

def Realizer.toLearner {K : FiniteKernelLearner d M T} (R : K.Realizer) : Learner d M T (Tape M T) where
  initialChoice := Prod.fst
  transition := fun t ω j obs => if ht : 0 < t ∧ t ≤ T then
    R.transition t j obs (ω.2.1 ⟨t-1,by omega⟩) else (false,j)
  output := fun t ω j => R.output t j ω.2.2

def Realizer.taggedTransition {K : FiniteKernelLearner d M T} (R : K.Realizer) (t : ℕ) :
    TaggedState M T → (Vector d × ℝ) → I → TaggedState M T
  | .inr a, _, _ => .inr a
  | .inl j, obs, u => if ht : t ≤ T then destination t ht (R.transition t j obs u) else .inl j

def Realizer.terminalOutput {K : FiniteKernelLearner d M T} (R : K.Realizer) :
    TaggedState M T → I → UnitSphere d
  | .inl j => R.output T j
  | .inr (t,j) => R.output t j

end FiniteKernelLearner

namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

def Realizer.terminalJointOutput {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) (u : I) : Result d M := (terminalTag j,R.terminalOutput j u)

end FiniteKernelLearner
end NoiselessRegression

end

end OAI


