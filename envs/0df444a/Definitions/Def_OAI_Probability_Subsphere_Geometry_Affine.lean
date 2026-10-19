-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
-- name    : OAI_Probability_Subsphere_Geometry_Affine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:52:32.200164+00:00
-- url     : https://prove2.me/theorems/2182ad75-3818-46e2-b956-d909d306d32b
-- title:
--   Random-tape realization of finite-state streams and simulation of a stream on an affine subsphere
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, $J$ a finite nonempty set of states (all subsets measurable) and $T\in\mathbb{N}$. A *finite-state stream* $L$ on $E$ with $T$ steps consists of an initial distribution $\pi_0$ on $J$, transition kernels $K_t(q;a,y)$ (distributions on $J$, for $t\in\mathbb{N}$, $q\in J$, $(a,y)\in E\times\mathbb{R}$) and output probability measures $o_q$ on $E$. With hidden vector $s\in E$ and rows $x=(x_0,\dots,x_{T-1})\in E^T$, the state starts with law $\pi_0$ and at step $n<T$ moves according to $K_{n+1}(q;x_n,\langle x_n,s\rangle)$; the estimate law is the mixture of the $o_q$ over the law of the state at time $T$. For a distribution $p$ on $J$ and $r\in\mathbb{R}$, $\mathrm{sample}(p,r)$ denotes inverse-CDF sampling along a fixed enumeration $j_0,\dots,j_{N-1}$ of $J$: the $j_i$ with $\sum_{l<i}p(j_l)\le r<\sum_{l\le i}p(j_l)$, or $j_0$ if there is none.
--
--   1. **Tapes.** A tape is $\omega=(q_0,(r_0,\dots,r_{T-1}),\tau)\in J\times\mathbb{R}^T\times E^J$; the tape law is $\pi_0\otimes\mathrm{Unif}[0,1)^{\otimes T}\otimes\bigotimes_{q\in J}o_q$, a probability measure. The estimate law is also a probability measure.
--   2. **Step maps.** The step kernel at time $n$ in state $q$ is $K_{n+1}(q;x_n,\langle x_n,s\rangle)$ if $n<T$ and the point mass at $q$ otherwise; the deterministic step with coin $r$ is $\mathrm{sample}(\text{step kernel},r)$.
--   3. **Tape estimate.** With $q_{n+1}$ the deterministic step from $q_n$ at time $n$ with coin $r_n$, the tape estimate is $\tau(q_T)$, the pre-drawn output of the final state.
--   4. **Tape transition.** $(\omega,n,q,(a,y))\mapsto\mathrm{sample}\bigl(K_n(q;a,y),\,r_{n-1}\bigr)$, with the coin replaced by $0$ when $n-1\ge T$.
--   5. **Tests on estimates.** For $s,y\in E$: the Euclidean test $\mathbf 1\{\|y-s\|\le\eta\}$ and the angular test $\mathbf 1\{\arccos\langle y,s\rangle\le\varepsilon\}$. Also recorded: the uniform law on $S_E$ (for $E\neq\{0\}$) and the Gaussian row law $\gamma_E^{\otimes T}$ are probability measures.
--   6. **Projection onto a test.** For an affine test $A$ in $\mathbb{R}^d$ (subspace $K_A$, centre $c_A\in K_A^\perp$, radius $r_A>0$, $\|c_A\|^2+r_A^2=1$), the measurable map
--   $$\mathrm{pr}_A(y)=r_A^{-1}\,P_{K_A}(y-c_A)\in K_A,$$
--   which inverts the point map: $\mathrm{pr}_A(c_A+r_As)=s$ for $s\in K_A$.
--   7. **Simulated stream.** For a stream $L$ on $\mathbb{R}^d$ with state set $J$ and $T$ steps, a test $A$ and complementary rows $w=(w_0,\dots,w_{T-1})\in(K_A^\perp)^T$, the stream on $K_A$ with the same initial law, outputs $(\mathrm{pr}_A)_*o_q$, and transitions
--   $$K^{A,w}_t(q;a,y)=K_t\bigl(q;\ v,\ \langle v,c_A\rangle+r_Ay\bigr),\qquad v=a+w_{t-1}\quad(a\in K_A,\ y\in\mathbb{R}),$$
--   with $w_{t-1}$ replaced by $0$ when $t-1\ge T$.
--   8. **Pulled-back block observation.** For rows $a_0,\dots,a_{m-1}\in K_A$, labels $y\in\mathbb{R}^m$ and complementary rows $w_i\in K_A^\perp$, the observation $\bigl((a_i+w_i)_{i<m},\ (\langle a_i+w_i,c_A\rangle+r_Ay_i)_{i<m}\bigr)\in(\mathbb{R}^d)^m\times\mathbb{R}^m$.
--
--   The tape constructions realize a randomized stream as a deterministic function of independent coins and pre-drawn outputs, so that averages of the estimate law become integrals against an explicit product measure. The simulation is an exact Gaussian reconstruction for an affine-sphere test: if $s\in S_{K_A}$, $a$ is a standard Gaussian vector of $K_A$ with label $y=\langle a,s\rangle$, and $w$ is an independent standard Gaussian vector of $K_A^\perp$, then $v=a+w$ is standard Gaussian in $\mathbb{R}^d$ and $\langle v,c_A\rangle+r_Ay=\langle v,c_A+r_As\rangle$, so the simulated stream behaves exactly like $L$ on the hidden point $c_A+r_As$. The complementary rows are independent random parameters, not an extra sample channel.
--
--   **Formalization Note** Names: `Fixed.Stream.Tape`, `tapeLaw` (with `tapeLaw_probability`), `estimateLaw_probability`, `stepPMF`, `stepDet`, `tapeEstimate` (via `detChain`), `tapeTransition`, `Fixed.sphereLaw_probability`, `Fixed.rowsLaw_probability`, `Fixed.euclideanTest`, `Fixed.angularTest`, `Affine.Test.project` (with `measurable_project`), `Affine.Simulation.stream A L w`, the local instance `affineSimulationSphereLaw_probability`, and `Weighted.pullObservation A w z`. Inverse-CDF sampling is `samplePMF` along `Fintype.equivFin J`. The indices $t-1$ are truncated natural subtraction; `Real.arccos` clamps arguments outside $[-1,1]$. The `[Nontrivial A.space]` assumption of the last section is not an argument of `pullObservation`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Affine.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Affine.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
namespace Stream
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

abbrev Tape (E J : Type*) (T : ℕ) := J × ((Fin T → ℝ) × (J → E))

def tapeLaw (L : Stream E J T) : Measure (Tape E J T) :=
  L.initial.toMeasure.prod ((Measure.pi (fun _ : Fin T => coinLaw)).prod
    (Measure.pi L.output))

instance tapeLaw_probability (L : Stream E J T) : IsProbabilityMeasure L.tapeLaw := by
  let : ∀ q, IsProbabilityMeasure (L.output q) := L.output_probability
  unfold tapeLaw
  infer_instance

instance estimateLaw_probability (L : Stream E J T) (s : E) (x : Fin T → E) :
    IsProbabilityMeasure (L.estimateLaw s x) := by
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  exact ae_of_all _ L.output_probability

def stepPMF (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) (q : J) : PMF J :=
  if hn : n < T then L.transition (n+1) q (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s⟫)
  else PMF.pure q

def stepDet (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) (q : J) (r : ℝ) : J :=
  samplePMF (L.stepPMF s x n q) r

def tapeEstimate (L : Stream E J T) (s : E) (ω : Tape E J T) (x : Fin T → E) : E :=
  ω.2.2 (detChain (L.stepDet s x) ω.1 T ω.2.1)

def tapeTransition (L : Stream E J T) (ω : Tape E J T) (n : ℕ) (q : J) (obs : E × ℝ) : J :=
  samplePMF (L.transition n q obs) (if h : n-1 < T then ω.2.1 ⟨n-1,h⟩ else 0)

end Stream
end SubsphereCurrent.Fixed
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw E) :=
  SubsphereRegression.sphereLaw_probability
instance rowsLaw_probability (T : ℕ) : IsProbabilityMeasure (rowsLaw E T) := by
  unfold rowsLaw
  infer_instance

def euclideanTest (η : ℝ) (s y : E) : ℝ≥0∞ :=
  {y | ‖y-s‖ ≤ η}.indicator (fun _ => 1) y

namespace Stream
variable {J : Type*} [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

end Stream
end SubsphereCurrent.Fixed
end
end
section
/-! Exact Gaussian reconstruction for an affine-sphere test. The complementary
rows are independent random parameters, not an extra sample channel to a learner. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Affine
variable {d n : ℕ}
namespace Test
variable (A : Test d n)

def project (y : Vector d) : A.space :=
  A.radius⁻¹ • A.space.orthogonalProjectionOnto (y-A.center)

lemma measurable_project : Measurable A.project := by unfold project; fun_prop

end Test

namespace Simulation
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (A : Test d n) (L : Fixed.Stream (Vector d) J T)

def stream (w : Fin T → A.spaceᗮ) : Fixed.Stream A.space J T where
  initial := L.initial
  transition t q obs :=
    let v : Vector d := obs.1.val + ((if h : t-1 < T then w ⟨t-1,h⟩ else 0) : A.spaceᗮ).val
    L.transition t q (v,⟪v,A.center⟫ + A.radius*obs.2)
  output q := (L.output q).map A.project
  output_probability q := by
    let := L.output_probability q
    exact Measure.isProbabilityMeasure_map A.measurable_project.aemeasurable

end Simulation
end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def angularTest (ε : ℝ) (s y : E) : ℝ≥0∞ :=
  {y | Real.arccos ⟪y,s⟫ ≤ ε}.indicator (fun _ => 1) y

namespace Stream
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ}
end Stream
end SubsphereCurrent.Fixed
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Affine
namespace Simulation
local instance affineSimulationSphereLaw_probability {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    IsProbabilityMeasure (sphereLaw E) := Fixed.sphereLaw_probability

variable {d n : ℕ} (A : Test d n) [Nontrivial A.space]
  {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (L : Fixed.Stream (Vector d) J T)

end Simulation
end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted
variable {d n m : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
variable {V : Type*} [Fintype V]

def pullObservation (w : Fin m → A.spaceᗮ)
    (z : (Fin m → A.space) × (Fin m → ℝ)) : Observation d m :=
  (fun i => (z.1 i : Vector d)+(w i : Vector d),
   fun i => ⟪(z.1 i : Vector d)+(w i : Vector d),A.center⟫ + A.radius*z.2 i)

end SubsphereCurrent.Weighted
end
end

end OAI


