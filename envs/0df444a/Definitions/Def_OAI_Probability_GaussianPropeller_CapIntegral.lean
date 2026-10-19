-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
-- name    : OAI_Probability_GaussianPropeller_CapIntegral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:35:36.630369+00:00
-- url     : https://prove2.me/theorems/e69caa78-a528-42c4-9f6e-7f68ba06f5e4
-- title:
--   Gaussian averages of radial tail functions
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   With $Y$ a standard Gaussian vector in $\mathbb R^n$ and $p$ the standard normal tail probability:
--
--   1. **Averaged tail.** $P_n(a)=\mathbb E\,p(a|Y|)$.
--   2. **Averaged density.**
--   $$
--   M_n(a)=\frac1{\sqrt{2\pi}}\,\mathbb E\,e^{-a^2|Y|^2/2}.
--   $$
--   These are the Gaussian measures of caps, written as functions of the cap parameter $a$. Their derivatives in $a$ are related, and closed forms are available for small $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapIntegral.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapIntegral.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar

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
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

variable {n : ℕ}
abbrev CE (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def capP (n : ℕ) (a : ℝ) : ℝ := ∫ y : CE n, p (a*‖y‖) ∂stdGaussian (CE n)
noncomputable def capM (n : ℕ) (a : ℝ) : ℝ := gaussianConst * ∫ y : CE n, density (a*‖y‖) ∂stdGaussian (CE n)

end GaussianPropeller.Cap

end OAI


