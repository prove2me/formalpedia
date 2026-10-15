-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Execution
-- name    : OAI_Probability_GaussianRegression_Execution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:16:45.485279+00:00
-- url     : https://prove2.me/theorems/6eff17ce-76cf-4e6c-adfa-7f2948949931
-- title:
--   Forced run of a finite-memory learner that ignores its stopping decisions
-- statement:
--   Fix $d,M,T\in\mathbb{N}$ and a set $\Omega$ of random seeds. Let $[2^M]=\{0,\dots,2^M-1\}$ be the set of memory states and $S^{d-1}\subseteq\mathbb{R}^{d}$ the unit sphere. A learner $L$ with these parameters consists of an initial choice $\iota(\omega)=\big(b_0(\omega),j_0(\omega)\big)\in\{\mathrm{true},\mathrm{false}\}\times[2^M]$, transition maps $\tau_t\big(\omega,j,(x,y)\big)\in\{\mathrm{true},\mathrm{false}\}\times[2^M]$ for times $t\in\mathbb{N}$, states $j$ and observations $(x,y)\in\mathbb{R}^{d}\times\mathbb{R}$, and output maps $o_t(\omega,j)\in S^{d-1}$. The Boolean component is a stop flag. For an unknown $s\in S^{d-1}$ and samples $x=(x_0,\dots,x_{T-1})\in(\mathbb{R}^{d})^{T}$, the observation read at time $n+1$ is the noiseless pair $(x_n,\langle x_n,s\rangle)$.
--
--   The forced run is the sequence of memory states obtained by following the transitions while ignoring every stop flag. Writing $\pi_2$ for the projection onto the memory-state component,
--   $$F_0=j_0(\omega),\qquad F_{n+1}=\begin{cases}\pi_2\,\tau_{n+1}\big(\omega,F_n,(x_n,\langle x_n,s\rangle)\big), & n<T,\\ F_n, & n\ge T.\end{cases}$$
--
--   The genuine run of $L$ halts at the first time a stop flag is raised, or at time $T$ if none is, and outputs $o_t(\omega,j)$ for its terminal pair $(t,j)$. Up to its stopping time it visits the same memory states as the forced run, so its terminal pair is always $(t,F_t)$ for some $t\le T$. This removes the data-dependent stopping rule from the analysis: the learner's output is determined by one of the deterministic routes $n\mapsto F_n$, which are stream routes of the transition maps.
--
--   **Formalization Note** The Lean name is `Learner.forcedRun L s ω x n` for a `Learner d M T Ω` of the base definitions, with fields `initialChoice`, `transition` and `output`; memory states are `Fin (2^M)` and vectors live in `EuclideanSpace ℝ (Fin d)`. The description of the terminal pair is the lemma `terminal_forced_witness` of the same file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Execution.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Execution.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianRegression_Caps

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


