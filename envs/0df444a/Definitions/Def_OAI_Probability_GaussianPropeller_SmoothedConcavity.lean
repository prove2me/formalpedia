-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
-- name    : OAI_Probability_GaussianPropeller_SmoothedConcavity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:16:44.849176+00:00
-- url     : https://prove2.me/theorems/a73fd540-d299-4d41-b1f0-1bf276264587
-- title:
--   Gaussian quantile of a heat-smoothed function
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Smoothed quantile transform.** For a function $f$ on $\mathbb R^\iota$ and $t\ge0$,
--   $$
--   q_t f(x)=\Phi^{-1}\bigl(P_t(\Phi\circ f)(x)\bigr),
--   $$
--   where $P_t$ is the Gaussian heat semigroup. If $f$ is concave, so is $q_tf$, which is an Ehrhard-type statement. It is used to prove that $\Phi^{-1}$ of the Gaussian measure of a shifted cone is concave in the shift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/SmoothedConcavity.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/SmoothedConcavity.lean by skeleton subtraction
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

namespace OAI

universe uι

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
namespace GaussianPropeller.EhrhardSmooth
-- [generator] trimmed: open GaussianPropeller.Quantile GaussianPropeller.QuantilePDE GaussianPropeller.HeatConvolution
open GaussianPropeller.Quantile GaussianPropeller.HeatConvolution
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

noncomputable def qheat (f : E → ℝ) (t : ℝ) (x : E) : ℝ := q (heat (fun y => Φ (f y)) t x)

end GaussianPropeller.EhrhardSmooth

end OAI


