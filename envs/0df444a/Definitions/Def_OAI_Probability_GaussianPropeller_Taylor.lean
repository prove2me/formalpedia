-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
-- name    : OAI_Probability_GaussianPropeller_Taylor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:24:46.461642+00:00
-- url     : https://prove2.me/theorems/b7acd2e1-08e5-4ed3-938e-c420d59eacef
-- title:
--   Partial sums for the exponential and the Gaussian integral
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Exponential partial sums.** $E_n(x)=\sum_{k=0}^n\frac{(-x)^k}{k!}$.
--   2. **Gaussian integral partial sums.**
--   $$
--   J_n(x)=\sum_{k=0}^n\frac{(-1)^k\,x^{2k+1}}{2^k\,k!\,(2k+1)},
--   $$
--   the Taylor polynomials of $\int_0^xe^{-t^2/2}\,dt$. Alternating-series bounds by these polynomials give the rational certificates for Gaussian probabilities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Taylor.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Taylor.lean by skeleton subtraction
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

namespace GaussianPropeller.Taylor
noncomputable def E (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (-1:ℝ)^k*x^k/(Nat.factorial k)
noncomputable def J (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (-1:ℝ)^k*x^(2*k+1)/((2:ℝ)^k*(Nat.factorial k)*(2*k+1))

end GaussianPropeller.Taylor

end OAI


