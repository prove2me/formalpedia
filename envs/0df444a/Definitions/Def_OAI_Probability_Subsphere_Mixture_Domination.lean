-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Mixture_Domination
-- name    : OAI_Probability_Subsphere_Mixture_Domination
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T06:01:51.554587+00:00
-- url     : https://prove2.me/theorems/8b8e9a52-d853-43a1-871d-6f202cf157c0
-- title:
--   Unnormalized beta density on the open unit interval
-- statement:
--   For real parameters $a,b$ the unnormalized beta density is the function $b_{a,b}:\mathbb{R}\to[0,\infty]$
--   $$b_{a,b}(x)=\begin{cases}x^{a-1}(1-x)^{b-1}, & 0<x<1,\\ 0, & \text{otherwise},\end{cases}$$
--   where the powers are real powers of positive numbers. No condition on $a$ and $b$ is imposed in the definition.
--
--   For $a,b>0$ its Lebesgue integral is the beta function, $\int_{\mathbb{R}}b_{a,b}(x)\,dx=B(a,b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)$, and $b_{a,b}/B(a,b)$ is the density of the law $\mathrm{Beta}(a,b)$. The module uses it to compare beta functions directly through their integrands: since $x^{A-1}\le x^{a-1}$ for $x\in(0,1)$ and $A\ge a$, the beta function is nonincreasing in each argument. This is a step towards the two-component domination of beta laws, $\mathrm{Beta}(a,b)\le2^{D}\bigl(\mathrm{Beta}(A,b)+\mathrm{Beta}(a,B)\bigr)$ for $0<a\le A\le a+D$ and $0<b\le B\le b+D$, which, transferred to spherical mixture laws, bounds the law of a Haar-rotated subspace direction by a multiple of the uniform sphere law plus a latitude law.
--
--   **Formalization Note** The definition is `betaRaw a b x := if 0 < x ∧ x < 1 then ENNReal.ofReal (x ^ (a - 1) * (1 - x) ^ (b - 1)) else 0`, with `Real.rpow` powers and values in `ℝ≥0∞`; the comparison with Mathlib's `betaPDF` and `beta` is made in the source module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Domination.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Domination.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

 def betaRaw (a b x : ℝ) : ℝ≥0∞ :=
  if 0 < x ∧ x < 1 then ENNReal.ofReal (x ^ (a - 1) * (1 - x) ^ (b - 1)) else 0

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory Set
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end

end OAI


