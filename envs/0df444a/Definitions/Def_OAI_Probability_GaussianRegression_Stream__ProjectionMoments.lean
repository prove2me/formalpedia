-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Stream__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:45:53.467628+00:00
-- url     : https://prove2.me/theorems/2bd952fa-55ac-4069-89f8-acd7102ac8e4
-- title:
--   Sequential routing and continuation mass
-- statement:
--   Bookkeeping for a streaming procedure with finitely many states $J$ processing observations $(x,\langle s,x\rangle)$ one at a time.
--
--   1. **Routing.** Given transition maps $\delta_n:J\times(E\times\mathbb R)\to J$, the route after $k$ observations from step $n$ applies $\delta_{n+1},\delta_{n+2},\dots$ to the successive observations.
--   2. **Continuation.** For weights $w_n(j,s)$, the continuation averages the weight reached after $k$ more Gaussian observations:
--   $$
--   \mathrm{cont}_{n,k+1}(j,s)=\int\mathrm{cont}_{n+1,k}\bigl(\delta_{n+1}(j,(x,\langle s,x\rangle)),s\bigr)\,d\gamma(x).
--   $$
--   3. **Stream factor.** $32768^{\dim E}\,|J|^{1/q}$, the per-step growth factor in the mass propagation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Stream.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Stream.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments

namespace OAI

/-!
Sequential routing and continuation mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

def streamRoute (δ : ℕ → J → (E × ℝ) → J) (n : ℕ) :
    (k : ℕ) → J → ((Fin k → E) × (Fin k → ℝ)) → J
  | 0, j, _ => j
  | k+1, j, x => streamRoute δ (n+1) k (δ (n+1) j (x.1 0, x.2 0)) (Fin.tail x.1, Fin.tail x.2)

def continuation (δ : ℕ → J → (E × ℝ) → J) (w : ℕ → J → E → ℝ≥0∞)
    (n : ℕ) : ℕ → J → E → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, continuation δ w (n+1) k (δ (n+1) j (x, ⟪s,x⟫)) s ∂stdGaussian E

def streamFactor (q : ℕ) : ℝ≥0∞ :=
  (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/(q : ℝ))

end StreamAux

end NoiselessRegression

end

end OAI


