-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
-- name    : OAI_Probability_ProjectionMoments_StoppingKernel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:28:43.521139+00:00
-- url     : https://prove2.me/theorems/ada029e0-3ddc-4d5b-8e49-eb19d83d4b00
-- title:
--   Routes and continuations for learners that may stop
-- statement:
--   A learner with $M$ bits of memory has $2^M$ states; at each time $t\le T$ it reads the observation $(x_t,\langle x_t,s\rangle)$ with Gaussian $x_t\in\mathbb R^d$, may stop (a boolean flag) and moves to a new state; on stopping at time $t$ (or at time $T$) it outputs a unit vector from its state. The bookkeeping for propagating mass bounds through stopping decisions.
--
--   1. **Shifts and routes.** Stopping records are shifted by one time step when prepended. The halt route from time $n$ follows the transitions on $k$ observations and records the first stop, if any.
--   2. **Children.** The child weight of a tagged state is the continuation weight $v(j)$ if still running, or the stopped weight $w_{n+t}(j)$ if it stopped at relative time $t$.
--   3. **Stopped continuation.** The stopped continuation integrates over one Gaussian observation, using the stopped weight if the learner stops and recursing otherwise:
--   $$
--   c_{n,k+1}(j,s)=\int\begin{cases}w_{n+1}(j',s)&\text{stop}\\c_{n+1,k}(j',s)&\text{continue}\end{cases}\,d\gamma(x),\quad(\text{stop},j')=\tau_{n+1}(j,(x,\langle s,x\rangle)).
--   $$
--   4. **Tagged weights** evaluate $w_n(j)$ on running states and $w_t(j)$ on records $(t,j)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/StoppingKernel.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/StoppingKernel.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end

namespace Learner

section
variable {d M : ℕ}

def haltShift {k : ℕ} : TaggedState M k → TaggedState M (k+1)
  | .inl j => .inl j
  | .inr (t,j) => .inr (t.succ,j)

def haltRoute (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M) (n : ℕ) :
    (k : ℕ) → State M → ((Fin k → Vector d) × (Fin k → ℝ)) → TaggedState M k
  | 0, j, _ => .inl j
  | k+1, j, X =>
    let a := τ (n+1) j (X.1 0,X.2 0)
    if a.1 then .inr (⟨1,by omega⟩,a.2)
    else haltShift (haltRoute τ (n+1) k a.2 (Fin.tail X.1,Fin.tail X.2))

def haltChild (w : ℕ → State M → Vector d → ℝ≥0∞)
    (v : State M → Vector d → ℝ≥0∞) (n : ℕ) {k : ℕ} : TaggedState M k → Vector d → ℝ≥0∞
  | .inl j => v j
  | .inr (t,j) => w (n+t) j

def stoppedContinuation (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M)
    (w : ℕ → State M → Vector d → ℝ≥0∞) (n : ℕ) : ℕ → State M → Vector d → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, let a := τ (n+1) j (x,⟪s,x⟫)
      if a.1 then w (n+1) a.2 s else stoppedContinuation τ w (n+1) k a.2 s ∂stdGaussian (Vector d)

end

variable {d M T : ℕ}

def taggedWeight (w : ℕ → State M → Vector d → ℝ≥0∞) (n : ℕ) : TaggedState M T → Vector d → ℝ≥0∞
  | .inl j => w n j
  | .inr (t,j) => w t j

variable [NeZero d]

end Learner
end NoiselessRegression

end

end OAI


