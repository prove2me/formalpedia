-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:34:53.696902+00:00
-- url     : https://prove2.me/theorems/15f12081-a60e-4495-8185-31ad5beb1241
-- title:
--   Replica weights from inverse Gram–Schmidt lengths
-- statement:
--   Weights used to bound moments of projected densities by integrating over independent replicas.
--
--   1. **Replica weight.** For $m\in\mathbb N$, a base point $p$ and vectors $v_1,\dots,v_n$, the replica weight is
--   $$
--   \prod_i\|g_i\|^{-m},
--   $$
--   where $g_i$ are the Gram–Schmidt vectors of the differences $v_j-p$; it is large when the points are nearly affinely dependent.
--   2. **Replica constant.** For a measure $\nu$ and exponent $a$ on a space of dimension $n$, the replica constant is $\nu(E)+3^n4^a\,2^{m+1}$, which bounds integrated replica weights under a local mass bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/ReplicaMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/ReplicaMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments

namespace OAI

/-!
Inverse Gram moments and almost-everywhere replica independence.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def replicaWeight (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal ((‖gramSchmidt ℝ (fun j => v j - p) i‖)⁻¹ ^ m)

def replicaConstant (ν : Measure E) (a : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ν Set.univ + ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ E * (4 : ℝ) ^ a) *
    (2 : ℝ≥0∞) ^ (m+1)

end ReplicaMoments
section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end AePiLast

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end NoiselessRegression

end

end OAI


