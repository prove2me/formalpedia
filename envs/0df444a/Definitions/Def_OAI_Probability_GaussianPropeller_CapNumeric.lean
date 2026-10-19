-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
-- name    : OAI_Probability_GaussianPropeller_CapNumeric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:42:33.578902+00:00
-- url     : https://prove2.me/theorems/a358300c-9612-4fea-b47c-f49a8f302dd9
-- title:
--   Polynomials for numerical cap estimates
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Comparison polynomials.** $Q(t)=\frac4{15}-\frac t{35}-\frac{t^2}{504}$, $U(t)=(1-t)\,t^2\sqrt{2t}\,Q(t)$ and $R(t)=\frac43-\frac{31t}{15}+\frac{67t^2}{280}+\frac{11t^3}{504}$.
--   2. **Spherical gap.**
--   $$
--   \int_b^1(u-b)\sqrt{1-u^2}\,du,
--   $$
--   together with an explicit primitive in the variable $s=1-b$.
--
--   These give rational upper and lower bounds for cap integrals near the boundary of the disc.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapNumeric.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapNumeric.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds

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
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.CapNumeric
open Real Set
noncomputable def Q (t:ℝ) := (4/15:ℝ)-t/35-t^2/504
noncomputable def U (t:ℝ) := (1-t)*t^2*Real.sqrt (2*t)*Q t
noncomputable def R (t:ℝ) := (4/3:ℝ)-31*t/15+67*t^2/280+11*t^3/504

end GaussianPropeller.CapNumeric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

noncomputable def sphereGap (b:ℝ) := ∫ u in b..1, (u-b)*Real.sqrt (1-u^2)

noncomputable def gapPrim (t s:ℝ) := Real.sqrt (2*s)*
    (2*t*s/3-(2/5+t/10)*s^2+(1/14-t/112)*s^3+s^4/144)

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

end GaussianPropeller.Cap

end OAI


