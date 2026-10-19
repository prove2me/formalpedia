-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Mills
-- name    : OAI_Probability_GaussianPropeller_Mills
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:23:13.304861+00:00
-- url     : https://prove2.me/theorems/eefce1b2-6464-4fed-9a80-91f5e3968c90
-- title:
--   The inverse Mills ratio and a barrier
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   With $T(x)=\int_x^\infty e^{-t^2/2}\,dt$:
--
--   1. **Inverse Mills ratio.** $\lambda(x)=e^{-x^2/2}/T(x)$, the hazard rate of the standard normal.
--   2. **Barrier.** $\beta(x)=\frac{3x+\sqrt{x^2+8}}4$ and its derivative; $\lambda\ge\beta$.
--   3. **Product.**
--   $$
--   G(x)=\lambda(x)\bigl(\lambda(x)-x\bigr),
--   $$
--   which is increasing, with values in $[0,1]$; $1-G(x)$ is the variance of a standard normal variable conditioned to exceed $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Mills.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Mills.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell

namespace OAI

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

namespace GaussianPropeller.Mills
open OneCell

noncomputable def barrier (x : ℝ) : ℝ := (3*x+Real.sqrt (x^2+8))/4
noncomputable def barrier' (x : ℝ) : ℝ := (3+x/Real.sqrt (x^2+8))/4

noncomputable def lambda (x : ℝ) : ℝ := density x / tail x
noncomputable def G (x : ℝ) : ℝ := lambda x * (lambda x-x)

end GaussianPropeller.Mills

end OAI


