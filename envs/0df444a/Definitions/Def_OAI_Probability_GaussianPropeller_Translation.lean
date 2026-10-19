-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Translation
-- name    : OAI_Probability_GaussianPropeller_Translation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:09:40.833615+00:00
-- url     : https://prove2.me/theorems/59fd3d40-2d7b-46ec-bcf4-a522743015e5
-- title:
--   The standard Gaussian density on a Euclidean space
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Standard density.** For a finite index set $\iota$, the product of one-dimensional standard normal densities
--   $$
--   \rho(x)=\prod_{i\in\iota}\frac1{\sqrt{2\pi}}e^{-x_i^2/2}=(2\pi)^{-|\iota|/2}e^{-|x|^2/2}.
--   $$
--   It is the density of the standard Gaussian measure on $\mathbb R^\iota$. It is used to translate Gaussian integrals, $\int f(x+a)\,d\gamma=\int f(x)\,e^{\langle a,x\rangle-|a|^2/2}\,d\gamma$, and to differentiate them in the shift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Translation.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Translation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianPropeller mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

namespace OAI

universe uE uX uY uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Translation

noncomputable def stdDensity {ι : Type uι} [Fintype ι]
    (x : EuclideanSpace ℝ ι) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

end GaussianPropeller.Translation

end OAI


