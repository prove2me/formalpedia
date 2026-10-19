-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Projection__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:37:35.463984+00:00
-- url     : https://prove2.me/theorems/4cf68ce1-b60a-4a30-967c-4f8559edc41c
-- title:
--   Laws of Gaussian projections and noisy observations
-- statement:
--   Laws on pairs (rows, labels) for $m$ observations of a vector $t\sim\nu$ in an inner product space $E$.
--
--   1. **Reference law.** Independent standard Gaussian rows $A_1,\dots,A_m$ together with Lebesgue measure on the labels.
--   2. **Projection law.** Draw independent Gaussian rows and $t\sim\nu$, and record the rows with the noiseless labels
--   $$
--   y_j=\langle t,A_j\rangle .
--   $$
--   3. **Gaussian coupling and noise.** Draw rows, $t\sim\nu$ and independent standard Gaussian noises $\xi_j$; the noisy observation with level $\delta$ has labels $\langle t,A_j\rangle+\delta\xi_j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Projection.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Projection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments

namespace OAI

/-!
Exact noiseless projection laws and completed-event bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def matrixLabelReference (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  (Measure.pi (fun _ => stdGaussian E)).prod volume

def projectionLaw (ν : Measure E) (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  ((Measure.pi (fun _ => stdGaussian E)).prod ν).map
    (fun z => (z.1, fun j => ⟪z.2, z.1 j⟫))

def gaussianCoupling (ν : Measure E) (m : ℕ) :
    Measure ((Fin m → E) × (E × (Fin m → ℝ))) :=
  (Measure.pi (fun _ => stdGaussian E)).prod
    (ν.prod (Measure.pi (fun _ => gaussianReal 0 1)))

def noisyObservation (m : ℕ) (δ : ℝ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) : (Fin m → E) × (Fin m → ℝ) :=
  (z.1, fun j => ⟪z.2.1, z.1 j⟫ + δ * z.2.2 j)

end ProjectionCoupling

end NoiselessRegression

end

end OAI


