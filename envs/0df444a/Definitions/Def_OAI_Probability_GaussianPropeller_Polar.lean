-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Polar
-- name    : OAI_Probability_GaussianPropeller_Polar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:33:41.844147+00:00
-- url     : https://prove2.me/theorems/1662bbf6-9d93-4728-bdf8-6a3c57448ae9
-- title:
--   Radial Gaussian integrals
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Radial integral.** For $n\in\mathbb N$ and $b>0$,
--   $$
--   R(n,b)=\int_0^\infty r^n\,e^{-br^2}\,dr=\frac{\Gamma\bigl(\frac{n+1}2\bigr)}{2\,b^{(n+1)/2}} .
--   $$
--   Together with polar coordinates on the Euclidean space and its unit sphere, it evaluates Gaussian integrals of homogeneous functions such as $|x|^m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Polar.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Polar.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds

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
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open Metric
namespace GaussianPropeller.Polar
open Translation

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => sphere (0 : E) 1
local notation "V" => (volume : Measure E)

end GaussianPropeller.Polar

namespace GaussianPropeller.Polar
open Real
noncomputable def radial (n : ℕ) (b : ℝ) : ℝ := ∫ r in Ioi (0:ℝ), r^n * exp (-b*r^2)

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => Metric.sphere (0:E) 1

end GaussianPropeller.Polar

end OAI


