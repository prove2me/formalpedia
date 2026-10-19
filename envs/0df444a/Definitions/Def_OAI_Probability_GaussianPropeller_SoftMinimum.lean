-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
-- name    : OAI_Probability_GaussianPropeller_SoftMinimum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:18:28.945863+00:00
-- url     : https://prove2.me/theorems/22d5327e-a61b-478a-a3e2-7b59aa631929
-- title:
--   The soft minimum of linear functions
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   For finitely many vectors $v_i$ in a Euclidean space:
--
--   1. **Partition function and weights.** $Z(x)=\sum_ie^{-\langle v_i,x\rangle}$ and $w_i(x)=e^{-\langle v_i,x\rangle}/Z(x)$.
--   2. **Soft minimum.** $-\log Z(x)$, a smooth concave lower approximation of $\min_i\langle v_i,x\rangle$.
--   3. **Derivatives.** The gradient $\sum_iw_i(x)\,v_i$ and the Hessian
--   $$
--   \sum_iw_i(x)\,\bigl(\nabla-v_i\bigr)\otimes v_i,
--   $$
--   with $\nabla$ the gradient, which is negative semidefinite. Scaling $v$ up turns the soft minimum into the minimum, which approximates the indicator of a cone.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/SoftMinimum.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/SoftMinimum.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianPropeller mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal

open Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace GaussianPropeller.SoftMin

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

noncomputable def Z (v : ι → E) (x : E) : ℝ := ∑ i, Real.exp (-⟪v i,x⟫)
noncomputable def weight (v : ι → E) (x : E) (i : ι) : ℝ := Real.exp (-⟪v i,x⟫)/Z v x
noncomputable def value (v : ι → E) (x : E) : ℝ := -Real.log (Z v x)
noncomputable def grad (v : ι → E) (x : E) : E := ∑ i, weight v x i • v i
noncomputable def hess (v : ι → E) (x : E) : E →L[ℝ] E :=
  ∑ i, (weight v x i) • ((innerSL ℝ (grad v x-v i)).smulRight (v i))

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end GaussianPropeller.SoftMin

end OAI


