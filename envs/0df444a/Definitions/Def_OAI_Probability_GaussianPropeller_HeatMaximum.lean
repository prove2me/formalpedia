-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
-- name    : OAI_Probability_GaussianPropeller_HeatMaximum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:15:06.355149+00:00
-- url     : https://prove2.me/theorems/dd040b58-7949-464c-a451-6cc62cc84a6d
-- title:
--   The concavity deficit used in a maximum principle
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Deficit.** For a function $v$ on $\mathbb R^\iota$, weights $a,b$, a slack $\sigma$ and points $x,y$,
--   $$
--   \delta(x,y)=v(ax+by)-a\,v(x)-b\,v(y)+\sigma\bigl(1+a|x|^2+b|y|^2\bigr).
--   $$
--   For $a,b\ge0$ with $a+b=1$, concavity of $v$ means $\delta\ge0$ when $\sigma=0$. A maximum-principle argument shows that a negative minimum of $\delta$ cannot occur along the heat flow, so the heat flow preserves this concavity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/HeatMaximum.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/HeatMaximum.lean by skeleton subtraction
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

namespace GaussianPropeller.HeatMaximum

section Spatial
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def deficit (v : E → ℝ) (a b σ : ℝ) (x y : E) : ℝ :=
  v (a • x+b • y)-a*v x-b*v y+σ*(1+a*‖x‖^2+b*‖y‖^2)

end Spatial
end GaussianPropeller.HeatMaximum

end OAI


