-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
-- name    : OAI_Probability_GaussianPropeller_QuantileCalculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:13:28.538882+00:00
-- url     : https://prove2.me/theorems/3f99d3ca-4f50-42d7-8f9c-35dda0724ac2
-- title:
--   Derivatives of a Gaussian distribution function composed with a map
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   For a function $f$ on $\mathbb R^\iota$ with gradient $g$ and Hessian $K$:
--
--   1. **Gradient.** $\varphi(f(x))\,g(x)$, the gradient of $\Phi\circ f$.
--   2. **Hessian.** The Hessian of $\Phi\circ f$,
--   $$
--   \varphi(f(x))\,K(x)-f(x)\,\varphi(f(x))\;g(x)\otimes g(x),
--   $$
--   using $\varphi'(t)=-t\,\varphi(t)$. These formulas let one pass concavity information between $f$ and $\Phi\circ f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/QuantileCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/QuantileCalculus.lean by skeleton subtraction
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
namespace GaussianPropeller.QuantilePDE
open GaussianPropeller.Quantile

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.QuantilePDE

namespace GaussianPropeller.SmoothCDF
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def grad (f : E → ℝ) (g : E → E) (x : E) : E := φ (f x) • g x
noncomputable def hess (f : E → ℝ) (g : E → E) (K : E → E →L[ℝ] E) (x : E) : E →L[ℝ] E :=
  φ (f x) • K x - (f x*φ (f x)) • ((innerSL ℝ (g x)).smulRight (g x))

end GaussianPropeller.SmoothCDF

end OAI


