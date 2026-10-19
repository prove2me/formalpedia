-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Models
-- name    : OAI_Probability_Subsphere_Models
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:28:00.542921+00:00
-- url     : https://prove2.me/theorems/71c07d30-53a2-4e84-ac82-acb2513a1ea9
-- title:
--   Borel measurability of all transition probabilities of a finite-memory kernel learner
-- statement:
--   Fix natural numbers $d$, $M$ and $T$, and let $Q_M=\{0,1,\dots,2^M-1\}$ be the set of memory states. A *kernel learner* $L$ in dimension $d$ with $M$ bits of memory and $T$ samples consists of
--
--   - an initial probability distribution on $\{0,1\}\times Q_M$, where the first coordinate is a stop flag;
--   - for every time $t\in\mathbb{N}$ and state $q\in Q_M$, a transition kernel assigning to each observation $(x,y)\in\mathbb{R}^d\times\mathbb{R}$ a probability distribution $P_t(q;x,y)$ on $\{0,1\}\times Q_M$ (whether to stop, and which state to move to); in a run, the observation is a Gaussian sample row $x$ together with its label $y=\langle x,s\rangle$ for the unknown unit vector $s$;
--   - for every time $t$ and state $q$, an output probability measure on the unit sphere $S^{d-1}\subset\mathbb{R}^d$.
--
--   The learner has *Borel rules* if every single transition probability is a Borel function of the observation:
--
--   $$
--   (x,y)\longmapsto P_t(q;x,y)\bigl(\{a\}\bigr)\ \text{ is Borel measurable on } \mathbb{R}^d\times\mathbb{R}\qquad\text{for all } t\in\mathbb{N},\ q\in Q_M,\ a\in\{0,1\}\times Q_M .
--   $$
--
--   The requirement is imposed at every time index and in every state, including states and times that a run can never reach ("counterfactual" states). It strengthens the condition built into the admissibility hypothesis of the main lower bound, where these functions are only required to be almost everywhere measurable with respect to the product of the standard Gaussian law on $\mathbb{R}^d$ and Lebesgue measure on $\mathbb{R}$. Borel rules are what make it possible to rewrite a randomized learner as a deterministic procedure driven by an explicit random tape while keeping all success probabilities measurable.
--
--   **Formalization Note** This is `KernelLearner.BorelRules L` for `L : KernelLearner d M T`. A transition is a `PMF (Bool × State M)` with values in `ℝ≥0∞`, and measurability refers to the product Borel σ-algebra on `EuclideanSpace ℝ (Fin d) × ℝ`. The sample bound $T$ plays no role in the condition, which quantifies over all `t : ℕ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Models.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Models.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

namespace KernelLearner

/-- Borel probabilities, including counterfactual states. -/
def BorelRules {d M T : ℕ} (L : KernelLearner d M T) : Prop :=
  ∀ t q dest, Measurable (fun obs => L.transition t q obs dest)

end KernelLearner

namespace SeededLearner

end SeededLearner

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe v
namespace SubsphereCurrent.Weighted

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe v
namespace SubsphereCurrent.Weighted

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent
namespace Fixed

namespace Stream
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J]
  {T : ℕ}

end Stream

end Fixed
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
end

end OAI


