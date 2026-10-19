-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
-- name    : OAI_Probability_GaussianPropeller_ConeConcavity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:20:18.649882+00:00
-- url     : https://prove2.me/theorems/8d809dec-ebac-4886-8114-6016df16423a
-- title:
--   Gaussian probabilities of shifted cones
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   For finitely many vectors $v_i$ in $\mathbb R^\iota$:
--
--   1. **Cone.** $C=\{y:\langle v_i,y\rangle\ge0\ \text{for all }i\}$.
--   2. **Shifted cone and its probability.** The set of $y$ with $x+y\in C$, and its Gaussian measure
--   $$
--   p(x)=\gamma\bigl(\{y:x+y\in C\}\bigr).
--   $$
--   The module shows that $\Phi^{-1}\circ p$ is concave in $x$. This is obtained from the soft minimum and the smoothed quantile transform in a limit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/ConeConcavity.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/ConeConcavity.lean by skeleton subtraction
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

namespace OAI

universe uX uι uκ

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

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

def cone (v : κ → E) : Set E := {y | ∀ i, 0 ≤ ⟪v i,y⟫}
def shifted (v : κ → E) (x : E) : Set E := {y | x+y ∈ cone v}
noncomputable def prob (v : κ → E) (x : E) : ℝ := (γ).real (shifted v x)

end GaussianPropeller.EhrhardCone

namespace GaussianPropeller.Quantile

end GaussianPropeller.Quantile

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

end GaussianPropeller.EhrhardCone

end OAI


