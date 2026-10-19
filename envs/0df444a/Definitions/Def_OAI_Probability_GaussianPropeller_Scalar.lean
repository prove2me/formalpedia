-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Scalar
-- name    : OAI_Probability_GaussianPropeller_Scalar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:49:10.506135+00:00
-- url     : https://prove2.me/theorems/a6948c6c-4cdf-409c-85dd-deea4107b04b
-- title:
--   Charge functions and radius data for many cells
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Charge.** For a parameter $A$ and $u\ge0$, $c_A(u)=0.415\,u-(A-0.15)\,u^2$. Together with derived quantities (a final budget, a threshold $0.415/(A-0.15)$, a small root of $k\,c_A(u)=1-A$ and a clipping coefficient), it bounds the mass a cell must carry.
--   2. **Regime.** The list of numerical conditions on $A$ and $k$ under which the argument applies, starting from $0.884\le A<1$ and $k\ge2$.
--   3. **Radius data.** A decreasing sequence $r_0\ge r_1\ge\cdots$ with
--   $$
--   0<r_i\le\tfrac23,\qquad \sum_ir_i^2=1,\qquad \sum_i\delta_i=1-A,\qquad c_A(r_i)\le\delta_i .
--   $$
--   Showing that no such data exists rules out configurations with five or more cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Scalar.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Scalar.lean by skeleton subtraction
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

namespace GaussianPropeller
namespace Scalar

def charge (A u : ℝ) : ℝ := 0.415 * u - (A - 0.15) * u ^ 2

noncomputable def finalBudget (A k t : ℝ) : ℝ :=
  charge A (Real.sqrt (2.6 * t)) + k * charge A t

noncomputable def smallRoot (A k : ℝ) : ℝ :=
  (0.415 - Real.sqrt (0.415 ^ 2 - 4 * (A - 0.15) * (1 - A) / k)) /
    (2 * (A - 0.15))

noncomputable def threshold (A : ℝ) : ℝ := 0.415 / (A - 0.15)

noncomputable def clipCoeff (A : ℝ) : ℝ := (A - 0.15) * 0.42 / (threshold A + 0.42)

structure Regime (A : ℝ) (k : ℕ) : Prop where
  A_lower : 0.884 ≤ A
  A_upper : A < 1
  k_lower : 2 ≤ k
  root_lower : 0.066 < smallRoot A k
  root_upper : smallRoot A k < 0.12
  root_eq : (k : ℝ) * charge A (smallRoot A k) = 1 - A
  root_cap : 2.6 * smallRoot A k < (threshold A) ^ 2
  root_slope : (A - 0.15) * (0.42 + smallRoot A k) < 0.415
  cap_charge : 1 - A < (k : ℝ) * charge A 0.42
  tail_end_charge : charge A 0.066 ≤ charge A 0.45
  base_charge_pos : 0 < charge A 0.066
  four_margin : 1 - A < clipCoeff A *
      (4 * (threshold A) ^ 2 - 1 + ((k : ℝ) - 1) * 0.066 ^ 2) +
      ((k : ℝ) - 1) * charge A 0.066
  third_margin : 1 - A < charge A 0.23 + (k : ℝ) * charge A 0.066
  final_margin : 1 - A < finalBudget A k 0.066

structure RadiusData (m : ℕ) (A : ℝ) where
  r : ℕ → ℝ
  δ : ℕ → ℝ
  pos : ∀ i < m, 0 < r i
  ordered : AntitoneOn r (Set.Iio m)
  cap : ∀ i < m, r i ≤ 2 / 3
  norm : ∑ i ∈ Finset.range m, r i ^ 2 = 1
  nonneg : ∀ i < m, 0 ≤ δ i
  lower : ∀ i < m, charge A (r i) ≤ δ i
  budget : ∑ i ∈ Finset.range m, δ i = 1 - A

namespace RadiusData

variable {m : ℕ} {A : ℝ} (D : RadiusData m A)

end RadiusData

end Scalar

end GaussianPropeller

end OAI


