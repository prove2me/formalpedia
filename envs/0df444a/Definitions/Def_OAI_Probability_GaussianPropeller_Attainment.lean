-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
-- name    : OAI_Probability_GaussianPropeller_Attainment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:28:03.020285+00:00
-- url     : https://prove2.me/theorems/4af285ed-e985-4ccd-b16d-dba83b723074
-- title:
--   Score vectors of the propeller
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   For $d\ge2$, with $e_0,e_1$ the first two coordinate vectors:
--
--   1. **Sector scores.** The triple
--   $$
--   \bigl(2\sqrt3\,e_0,\ -\sqrt3\,e_0+3e_1,\ -\sqrt3\,e_0-3e_1\bigr),
--   $$
--   three vectors of equal length at mutual angles of $120^\circ$. Their score cells are the three sectors of the propeller. This is used to show that the propeller is a partition attaining $9/(8\pi)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Attainment.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Attainment.lean by skeleton subtraction
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

namespace OAI

universe uE

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

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable def axis0 (d : ℕ) (hd : 2 ≤ d) : Space d :=
  EuclideanSpace.single ⟨0, by omega⟩ 1
noncomputable def axis1 (d : ℕ) (hd : 2 ≤ d) : Space d :=
  EuclideanSpace.single ⟨1, by omega⟩ 1

noncomputable def sectorScores (d : ℕ) (hd : 2 ≤ d) : Tuple d 3 :=
  WithLp.toLp 2 ![(2 * Real.sqrt 3) • axis0 d hd,
    (-Real.sqrt 3) • axis0 d hd + (3 : ℝ) • axis1 d hd,
    (-Real.sqrt 3) • axis0 d hd - (3 : ℝ) • axis1 d hd]

end GaussianPropeller.Reduction

namespace GaussianPropeller

end GaussianPropeller

end OAI


