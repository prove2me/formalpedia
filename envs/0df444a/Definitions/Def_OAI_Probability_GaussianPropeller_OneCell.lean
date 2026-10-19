-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
-- name    : OAI_Probability_GaussianPropeller_OneCell
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:21:20.380227+00:00
-- url     : https://prove2.me/theorems/b3227104-1ccc-43e3-a65a-e81a03709fa7
-- title:
--   Polynomial bounds for the Gaussian density and tail
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Tail.** The unnormalized density $e^{-x^2/2}$, the constant $1/\sqrt{2\pi}$, and the tail
--   $$
--   T(a)=\int_a^\infty e^{-x^2/2}\,dx .
--   $$
--   2. **Taylor bounds.** The polynomials $1-\frac{x^2}2+\frac{x^4}8-\frac{x^6}{48}$ and the same with $+\frac{x^8}{384}$, which bound $e^{-x^2/2}$ from below and above, and their primitives.
--   3. **A concave comparison polynomial.** $P(x)=0.398943\,Q(x)-x^2/2$, where $Q(x)=x+\frac{x^3}2-\frac{x^5}{24}+\frac{x^7}{240}-\frac{x^9}{2688}+\frac{x^{11}}{3456}$, with its first and second derivatives. These control the contribution of a single cell.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/OneCell.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/OneCell.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity

namespace OAI

universe uE

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

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.OneCell

noncomputable def Q (x : ℝ) : ℝ := x+x^3/2-x^5/24+x^7/240-x^9/2688+x^11/3456
noncomputable def P (x : ℝ) : ℝ := (398943/1000000:ℝ)*Q x-x^2/2
noncomputable def P' (x : ℝ) : ℝ := (398943/1000000:ℝ)*
  (1+3*x^2/2-5*x^4/24+7*x^6/240-9*x^8/2688+11*x^10/3456)-x
noncomputable def P'' (x : ℝ) : ℝ := (398943/1000000:ℝ)*
  (3*x-5*x^3/6+7*x^5/40-3*x^7/112+55*x^9/1728)-1

noncomputable def density (x : ℝ) : ℝ := Real.exp (-x^2/2)
noncomputable def gaussianConst : ℝ := (Real.sqrt (2*Real.pi))⁻¹
noncomputable def tail (a : ℝ) : ℝ := ∫ x in Ioi a, density x

noncomputable def densityUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/8-x^6/48+x^8/384
noncomputable def densityLower (x : ℝ) : ℝ := 1-x^2/2+x^4/8-x^6/48
noncomputable def densityPrimitive (x : ℝ) : ℝ := x-x^3/6+x^5/40-x^7/336+x^9/3456
noncomputable def densityLowerPrimitive (x : ℝ) : ℝ := x-x^3/6+x^5/40-x^7/336

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GeneralCell
end GaussianPropeller.OneCell

end OAI


