-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
-- name    : OAI_Probability_Subsphere_Regression_Streaming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:39:27.590562+00:00
-- url     : https://prove2.me/theorems/247a7371-8747-481b-8905-0576be639ee8
-- title:
--   Deterministic stream routes, Gaussian continuation weights, block growth factor and forced runs
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra and standard Gaussian measure $\gamma_E$, and let $J$ be a set of states. A *deterministic transition rule* is a map $\delta:\mathbb{N}\times J\times(E\times\mathbb{R})\to J$; $\delta(t,j,(a,y))$ is the state after processing the observation $(a,y)$ at time $t$ in state $j$.
--
--   1. **Stream route.** For a start time $n\in\mathbb{N}$, a length $k\in\mathbb{N}$, a state $j\in J$ and a block $(A,y)\in E^k\times\mathbb{R}^k$, the route is $\mathrm{route}^k_n(j;A,y)=j_k$, where $j_0=j$ and
--   $$j_{i+1}=\delta\bigl(n+i+1,\ j_i,\ (A_i,y_i)\bigr),\qquad 0\le i<k .$$
--   2. **Continuation weight.** For a terminal weight $w:\mathbb{N}\times J\times E\to[0,\infty]$, define recursively
--   $$c^0_n(j,s)=w(n,j,s),\qquad c^{k+1}_n(j,s)=\int_E c^{k}_{n+1}\Bigl(\delta\bigl(n+1,j,(x,\langle s,x\rangle)\bigr),\ s\Bigr)\,d\gamma_E(x).$$
--   Unwinding the recursion, $c^k_n(j,s)$ is the expected terminal weight $w(n+k,j_k,s)$ when the stream starts in state $j$ after time $n$ and processes $k$ independent standard Gaussian rows $x$ with noiseless labels $\langle s,x\rangle$.
--   3. **Block growth factor.** For a finite set $J$ and $q\in\mathbb{N}$,
--   $$\Phi_q=32768^{\dim E}\,|J|^{1/q}\in[0,\infty],\qquad 32768=2^{15}.$$
--   4. **Forced run.** For a seeded learner of the deterministic model (seed $\omega$, initial choice $c_0(\omega)=(b_0,q_0)$, transition rule $\delta_L(t,\omega,q,(x,y))\in\{0,1\}\times Q_M$ with $Q_M=\{0,\dots,2^M-1\}$), a hidden unit vector $s\in\mathbb{R}^d$ and samples $x\in(\mathbb{R}^d)^T$, the forced run ignores every stop flag: it starts at $q_0$, sets $q_{n+1}$ to the state component of $\delta_L\bigl(n+1,\omega,q_n,(x_n,\langle x_n,s\rangle)\bigr)$ for $n<T$, and $q_{n+1}=q_n$ for $n\ge T$.
--   5. **Cap weight.** For $y\in E$ and $\varepsilon\in\mathbb{R}$, the indicator function of the closed ball $\overline B(y,\varepsilon)=\{x:\|x-y\|\le\varepsilon\}$.
--
--   Routes and continuation weights describe a finite-state stream fed with Gaussian rows; a run of $m+k$ steps splits into the route of the first $m$ steps followed by a $k$-step continuation, which is how streams are analysed block by block. The factor $\Phi_q$ is the per-block loss in the mass bounds for continuation weights, so that after $k$ steps a bound is multiplied by $\Phi_q^{\lfloor k/q\rfloor+1}$. The forced run is the state sequence of a learner with early stopping disabled, and the cap weight is the success indicator for landing within distance $\varepsilon$ of a point.
--
--   **Formalization Note** `streamRoute δ n k j`, `continuation δ w n k j s`, `streamFactor q` (with `E`, `J` implicit), `Learner.forcedRun L s ω x n` and `capWeight y ε`. In `streamFactor` the exponent `1/(q : ℝ)` is $0$ when $q=0$ (Lean's convention $1/0=0$), and $\dim E$ is `Module.finrank ℝ E`. `streamRoute` uses no structure on $E$ and $J$; the measurability and finiteness assumptions of the surrounding sections are not arguments of these definitions except where used ($|J|$ needs $J$ finite).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Streaming.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Streaming.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
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

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

def forcedRun (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → State M
  | 0 => (L.initialChoice ω).2
  | n+1 =>
    if hn : n < T then
      (L.transition (n+1) ω (L.forcedRun s ω x n) (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)).2
    else L.forcedRun s ω x n

end Learner

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

def capWeight (y : E) (ε : ℝ) : E → ℝ≥0∞ :=
  (Metric.closedBall y ε).indicator (fun _ => 1)

end StreamCaps

section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ObservationAC

end SubsphereRegression
end
end

end OAI


