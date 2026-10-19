-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:40:29.383611+00:00
-- url     : https://prove2.me/theorems/2f2ba0f0-3d38-454d-b4d9-b590a3580551
-- title:
--   Polynomial mass, local normalization and block values
-- statement:
--   Localization tools for measures in an inner product space.
--
--   1. **Polynomial mass.** $\nu$ has polynomial mass with exponent $a$ and constant $C$ if every closed ball has $\nu(\bar B(z,r))\le C\,r^a$.
--   2. **Local normalization.** The local normalization at $z$ and radius $r$ restricts $\nu$ to $\bar B(z,r)$, pushes it to the unit ball by $x\mapsto(x-z)/r$, and divides by $Cr^a$:
--   $$
--   \nu_{z,r}=(Cr^a)^{-1}\,\bigl(x\mapsto r^{-1}(x-z)\bigr)_*\bigl(\nu|_{\bar B(z,r)}\bigr).
--   $$
--   3. **Block values.** For finitely many weight functions $h_j$ and a selection map $\varphi$ of observations, the block value at $s$ averages $h_{\varphi(A,\langle s,A\rangle)}(s)$ over Gaussian rows $A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Blocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Blocks.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments

namespace OAI

/-!
Localization, finite selection, and block mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def PolynomialMass (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ z : E, ∀ r : ℝ, 0 < r → ν (Metric.closedBall z r) ≤ C * ENNReal.ofReal (r^a)

def localNormalize (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) (r : ℝ) : Measure E :=
  (C * ENNReal.ofReal (r^a))⁻¹ • (ν.restrict (Metric.closedBall z r)).map (fun x => r⁻¹ • (x-z))

def blockValue {J : Type*} [Fintype J] {m : ℕ} (h : J → E → ℝ≥0∞)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (s : E) : ℝ≥0∞ :=
  ∫⁻ A, h (φ (A, fun j => ⟪s,A j⟫)) s ∂Measure.pi (fun _ : Fin m => stdGaussian E)

end Block

end NoiselessRegression

end

end OAI


