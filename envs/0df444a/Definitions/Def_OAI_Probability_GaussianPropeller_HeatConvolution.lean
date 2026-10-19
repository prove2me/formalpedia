-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
-- name    : OAI_Probability_GaussianPropeller_HeatConvolution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:10:49.825296+00:00
-- url     : https://prove2.me/theorems/0df39a40-fd03-4650-b670-83ed57949609
-- title:
--   The Gaussian heat semigroup
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Heat flow.** For a function $F$ on $\mathbb R^\iota$ with values in a normed space and $t\ge0$,
--   $$
--   (P_tF)(x)=\int F\bigl(x+\sqrt t\,z\bigr)\,d\gamma(z),
--   $$
--   the convolution of $F$ with the centred Gaussian of variance $t$. It solves the heat equation $\partial_tP_tF=\frac12\Delta P_tF$, and it is used to regularize functions while controlling concavity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/HeatConvolution.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/HeatConvolution.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianPropeller mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation

namespace OAI

universe uV uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

namespace GaussianPropeller.HeatConvolution
-- [generator] dropped: open GaussianPropeller.Stein
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

noncomputable def heat {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) (t : ℝ) (x : E) : V := ∫ z, F (x+Real.sqrt t • z) ∂γ

section General
variable {V : Type uV} [NormedAddCommGroup V]

variable [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

end General

end GaussianPropeller.HeatConvolution

end OAI


