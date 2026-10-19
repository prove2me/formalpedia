-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Configuration
-- name    : OAI_Probability_GaussianPropeller_Configuration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:51:51.839872+00:00
-- url     : https://prove2.me/theorems/95cb9c49-b957-4e14-a822-8b7d03d7bcf8
-- title:
--   Configurations of a hypothetical counterexample
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Configuration.** A configuration with $k$ cells in $\mathbb R^d$ consists of nonzero vectors $z_j$, the normalized centroids, and numbers $P_j$, the cell masses, satisfying:
--   $$
--   \sum_jz_j=0,\qquad \sum_j|z_j|^2=1,\qquad \sum_jP_j=1,\qquad P_j\le\tfrac12,\qquad |z_j|\le\tfrac23 .
--   $$
--   The norms $|z_j|$ are decreasing and the vectors are pairwise obtuse. Each $P_j$ satisfies a linear and a quadratic lower bound in $|z_j|$. Further conditions control residuals of pairs of vectors, plus two extra conditions when $k=4$. A minimal optimal partition with value above $9/(8\pi)$ produces such a configuration, and none exists for $k\ge4$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Configuration.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Configuration.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_Scalar

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell ProbabilityBounds
open scoped RealInnerProductSpace

structure Configuration (d k:ℕ) where
  z : Fin k→Space d
  P : Fin k→ℝ
  zero : ∑ j,z j=0
  norm : ∑ j,‖z j‖^2=1
  pos : ∀ j,z j≠0
  order : Antitone (fun j=>‖z j‖)
  obtuse : Pairwise (fun j l=>⟪z j,z l⟫<0)
  cap : ∀ j,‖z j‖≤2/3
  probability : ∑ j,P j=1
  half : ∀ j,P j≤1/2
  quadratic : ∀ j,(if k=5 then (0.929:ℝ) else 0.884)*‖z j‖^2≤P j
  linear : ∀ j,0.415*‖z j‖+0.15*‖z j‖^2≤P j
  pair : ∀ i j l, i≠j → i≠l →
      ‖residualVector (z i) (z j)‖^2*‖residualVector (z i) (z l)‖^2-
      ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z j))^2*
      (1+residualCoefficient (z i) (z l))^2
  cap3 : k=4 → ∀ j,‖z j‖≤(8/3:ℝ)*P j*(1-P j)
  loss4 : k=4 → ∀ j,∃ x≥(0:ℝ),p x=P j ∧
      (9/(8*Real.pi))*‖z j‖^2/(1+Real.sqrt (1-(4/3:ℝ)*‖z j‖^2))≤loss x

variable {d k:ℕ} [NeZero k]

end GaussianPropeller.Reduction

end OAI


