-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
-- name    : OAI_Probability_ProjectionMoments_Stopping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:18:49.550906+00:00
-- url     : https://prove2.me/theorems/108514c6-b943-4220-bb6d-483e52a5f860
-- title:
--   Tagged run states for learners that may stop
-- statement:
--   A learner with $M$ bits of memory has $2^M$ states; at each time $t\le T$ it reads the observation $(x_t,\langle x_t,s\rangle)$ with Gaussian $x_t\in\mathbb R^d$, may stop (a boolean flag) and moves to a new state; on stopping at time $t$ (or at time $T$) it outputs a unit vector from its state. A tagged state is either a running state $j$ or a stopped record $(t,j)$ of the stopping time $t\le T$ and the final state.
--
--   1. **Decoding.** Tagged states decode to run statuses (running, or stopped at time $t$ in state $j$).
--   2. **Tagged step.** At time $t\le T$, a running state applies the transition; if it signals stopping it becomes the record $(t,j')$, otherwise it continues in $j'$. Stopped records never change.
--   3. **Output.** A running state at the end outputs the learner's output at time $T$, and a stopped record $(t,j)$ outputs the output at time $t$:
--   $$
--   \mathrm{out}(t,j)=\mathrm{output}_t(\omega,j).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Stopping.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Stopping.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

variable [Nontrivial E] [Nonempty J]

end

namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u}

instance taggedMeasurableSingletonClass : MeasurableSingletonClass (TaggedState M T) :=
  ⟨fun _ => trivial⟩

def decodeTagged : TaggedState M T → RunStatus M
  | .inl j => .inl j
  | .inr (t,j) => .inr (t.val,j)

def taggedStep (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M)
    (t : ℕ) : TaggedState M T → (Vector d × ℝ) → TaggedState M T
  | .inr done, _ => .inr done
  | .inl j, obs =>
    if ht : t ≤ T then
      let a := τ t j obs
      if a.1 then .inr (⟨t,by omega⟩,a.2) else .inl a.2
    else .inl j

def taggedOutput (L : Learner d M T Ω) (ω : Ω) : TaggedState M T → UnitSphere d
  | .inl j => L.output T ω j
  | .inr (t,j) => L.output t ω j

end Learner
end NoiselessRegression

end

end OAI


