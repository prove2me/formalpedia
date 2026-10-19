-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Execution__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:49:18.473112+00:00
-- url     : https://prove2.me/theorems/bd569444-dce2-46fa-a57b-216257d1573f
-- title:
--   Forced runs of a finite-state learner
-- statement:
--   For a learner with $2^M$ memory states, a seed $\omega$, a target $s$ and samples $x_1,\dots,x_T$, the forced run is the sequence of memory states obtained by starting from the initial state chosen by $\omega$ and applying the transition at each step to the observation:
--   $$
--   \sigma_{n+1}=\mathrm{trans}_{n+1}\bigl(\omega,\sigma_n,(x_{n+1},\langle x_{n+1},s\rangle)\bigr)\quad(n<T),
--   $$
--   after which the state stays constant. It records the terminal state used by the estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Execution.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Execution.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite-state sequential execution and terminal-state witnesses.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

def forcedRun (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → State M
  | 0 => (L.initialChoice ω).2
  | n+1 =>
    if hn : n < T then
      (L.transition (n+1) ω (L.forcedRun s ω x n) (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)).2
    else L.forcedRun s ω x n

end Learner

end NoiselessRegression

end

end OAI


