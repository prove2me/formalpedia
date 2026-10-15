-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Stream
-- name    : OAI_Probability_GaussianRegression_Stream
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:13:31.043988+00:00
-- url     : https://prove2.me/theorems/f45a0803-803e-467d-ba63-550456cc37e6
-- title:
--   Sequential routing of observation streams, continuation values, and the per-block mass factor
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra and standard Gaussian measure $\gamma_E$, and let $J$ be a finite set of states. A transition rule is a map $\delta:\mathbb{N}\times J\times(E\times\mathbb{R})\to J$; $\delta(t,j,(x,y))$ is the state entered when the observation $(x,y)$ is read at time $t$ in state $j$. The file defines three objects.
--
--   1. **Stream route.** For a start time $n\in\mathbb{N}$, a start state $j\in J$ and $k$ observations $(A_0,y_0),\dots,(A_{k-1},y_{k-1})\in E\times\mathbb{R}$, the route is the final state $j_k$ of the recursion
--      $$j_0=j,\qquad j_{i+1}=\delta\big(n+i+1,\ j_i,\ (A_i,y_i)\big)\qquad(0\le i<k).$$
--
--   2. **Continuation value.** For terminal weights $w:\mathbb{N}\times J\times E\to[0,\infty]$, the values $V_{n,k}(j,s)$, for $n,k\in\mathbb{N}$, $j\in J$ and $s\in E$, are defined by recursion on $k$:
--      $$V_{n,0}(j,s)=w(n,j,s),\qquad V_{n,k+1}(j,s)=\int_E V_{n+1,k}\Big(\delta\big(n+1,\,j,\,(x,\langle s,x\rangle)\big),\,s\Big)\,d\gamma_E(x).$$
--      Thus $V_{n,k}(j,s)$ is the expected terminal weight $w(n+k,j_k,s)$ when the process starts in state $j$ at time $n$ and reads $k$ independent rows $x\sim\gamma_E$ with exact labels $\langle s,x\rangle$, $j_k$ being the stream route.
--
--   3. **Per-block factor.** For $q\in\mathbb{N}$,
--      $$F_q=32768^{\dim E}\cdot|J|^{1/q}.$$
--
--   For a finite-memory learner reading noiseless Gaussian samples of an unknown vector $s$, the route is the learner's memory state. With indicator weights of small balls around the learner's outputs, the continuation value becomes the conditional probability, given $s$, that the output is close to $s$. Mass bounds are propagated along the stream block by block: a stream of $k$ observations is split into about $k/q$ blocks, each multiplying a polynomial ball-mass constant by at most $F_q$.
--
--   **Formalization Note** The Lean names are `streamRoute δ n k j`, `continuation δ w n k j s` and `streamFactor q`; observations are passed as a pair of tuples of type `(Fin k → E) × (Fin k → ℝ)`, and $J$ is a `Fintype` with a measurable structure in which singletons are measurable. The factor is computed in $[0,\infty]$, with $32768=2^{15}$; for $q=0$ Lean's convention $1/0=0$ gives $F_0=32768^{\dim E}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Stream.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Stream.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere

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


