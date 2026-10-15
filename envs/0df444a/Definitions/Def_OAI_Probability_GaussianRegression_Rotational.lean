-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Rotational
-- name    : OAI_Probability_GaussianRegression_Rotational
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:19:59.886328+00:00
-- url     : https://prove2.me/theorems/f024a485-c5e2-4be1-8190-d2194154c582
-- title:
--   The Gaussian sample law and the uniform sphere law are probability measures
-- statement:
--   Let $d,T\in\mathbb{N}$, let $\mathbb{R}^{d}$ carry its Euclidean structure and Lebesgue measure $\mathrm{vol}_d$, and let $S^{d-1}=\{s\in\mathbb{R}^{d}:\|s\|=1\}$. The file records two laws of the noiseless regression model as probability measures.
--
--   1. **Sample law.** The measure
--      $$\mathrm{P}_{d,T}=\mathcal N(0,I_d)^{\otimes T}\quad\text{on }(\mathbb{R}^{d})^{T},$$
--      the law of $T$ independent sample rows $x_0,\dots,x_{T-1}$, each a standard Gaussian vector in $\mathbb{R}^{d}$. It is a probability measure for all $d$ and $T$; for $T=0$ it is the unit mass on the empty sample.
--
--   2. **Uniform law on the sphere.** The normalized surface measure $\mathrm{Unif}_{S^{d-1}}=\sigma(S^{d-1})^{-1}\,\sigma$ on $S^{d-1}$, where $\sigma(A)=d\cdot\mathrm{vol}_d(\{rx:0<r<1,\ x\in A\})$. It is a probability measure whenever $d\ge1$.
--
--   In the regression model the unknown direction $s$ is drawn from $\mathrm{Unif}_{S^{d-1}}$ and the sample rows from $\mathrm{P}_{d,T}$. Knowing that both have total mass $1$ is what allows success probabilities to be computed with Fubini's theorem as averages of conditional probabilities, and constant bounds to be integrated against these laws.
--
--   **Formalization Note** The instances are `sampleLaw_probability d T` and `uniformSphere_probability d`, the latter under `[NeZero d]`. Here `sampleLaw d T` is `Measure.pi` of `stdGaussian (EuclideanSpace ℝ (Fin d))`, and `uniformSphere d` coincides with the normalized sphere law of $\mathbb{R}^{d}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Rotational.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Rotational.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianRegression_Execution

namespace OAI

/-!
Fubini bounds and rotational lower bounds for sequential estimation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) := by
  unfold sampleLaw
  infer_instance
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) := by
  change IsProbabilityMeasure (sphereLaw (E := Vector d))
  infer_instance

namespace Learner
end Learner

end NoiselessRegression

end

end OAI


