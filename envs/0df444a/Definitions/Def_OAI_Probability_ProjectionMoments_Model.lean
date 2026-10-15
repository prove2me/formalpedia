-- Prove2me | Definitions.Def_OAI_Probability_ProjectionMoments_Model
-- name    : OAI_Probability_ProjectionMoments_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:01:52.507989+00:00
-- url     : https://prove2.me/theorems/b32e1ebb-76da-428b-a8e5-63e699a0cc1f
-- title:
--   Uniform sphere law, orthogonal group, and stop-tagged memory states
-- statement:
--   Throughout, $E$ is a finite-dimensional real inner product space with its Borel $\sigma$-algebra and its canonical volume measure $\mathrm{vol}_E$ (the Haar measure giving the unit cube of an orthonormal basis volume $1$). Write $S(E)=\{x\in E:\|x\|=1\}$ for the unit sphere. The file introduces the following objects.
--
--   1. **Uniform law on the sphere.** Let $\sigma_E$ be the surface measure on $S(E)$ induced by the volume,
--      $$\sigma_E(A)=(\dim E)\cdot\mathrm{vol}_E\big(\{rx:\ 0<r<1,\ x\in A\}\big)\qquad\text{for measurable }A\subseteq S(E).$$
--      The sphere law is its normalization
--      $$\mathrm{Unif}_{S(E)}=\sigma_E\big(S(E)\big)^{-1}\,\sigma_E ,$$
--      which for $\dim E\ge1$ is the rotation-invariant probability measure on $S(E)$.
--
--   2. **Ambient sphere law.** The same law regarded as a measure on $E$, i.e. the push-forward of $\mathrm{Unif}_{S(E)}$ under the inclusion $S(E)\hookrightarrow E$. It is concentrated on the sphere.
--
--   3. **Orthogonal group.** The group
--      $$\mathrm{O}(E)=\{U\in\mathcal L(E):\ U^{*}U=UU^{*}=I\}$$
--      of unitary elements of the algebra $\mathcal L(E)$ of linear operators on $E$, where $U^{*}$ is the adjoint. It carries the operator-norm topology and the corresponding Borel $\sigma$-algebra, and the file records that $\mathrm{O}(E)$ is compact.
--
--   4. **Stop-tagged memory states.** For $M,T\in\mathbb{N}$ let $[2^M]=\{0,1,\dots,2^M-1\}$ be the set of memory states of a learner with $M$ bits of memory. A tagged state is an element of the disjoint union
--      $$[2^M]\ \sqcup\ \big(\{0,1,\dots,T\}\times[2^M]\big).$$
--      A state $j$ in the first summand means that the learner is still running in memory state $j$; a pair $(t,j)$ in the second summand means that it stopped at time $t$ in memory state $j$. This finite set carries the discrete $\sigma$-algebra, in which every subset is measurable.
--
--   In the memory–sample analysis of noiseless Gaussian regression, the unknown unit vector is drawn from $\mathrm{Unif}_{S(E)}$ with $E=\mathbb{R}^d$, the orthogonal group is used to exploit the rotation invariance of the Gaussian design and of this prior, and tagged states let the run of a randomized learner be described by transitions on a finite state space, in which a stopped run stays put together with the time at which it stopped.
--
--   **Formalization Note** The Lean names are `sphereLaw`, `ambientSphereLaw`, `Rotation E` (an abbreviation for `unitary (E →L[ℝ] E)`) with the instances `rotationMeasurableSpace` (the Borel $\sigma$-algebra), `rotationBorelSpace` and `rotationCompact`, and `Learner.TaggedState M T`, the sum type `State M ⊕ (Fin (T+1) × State M)`, whose instance `taggedMeasurableSpace` is the top $\sigma$-algebra. The surface measure is Mathlib's `Measure.toSphere` applied to `volume`. When $\dim E=0$ the sphere is empty, its surface measure is zero, and the normalizing factor $0^{-1}=\infty$ multiplies the zero measure, so the sphere law is then the zero measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression

namespace OAI

noncomputable section

section InlineMainProof

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

universe u

namespace NoiselessRegression

namespace Learner

end Learner

open scoped Topology

open InnerProductSpace

section SphereBounds

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

end SphereBounds

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def ambientSphereLaw : Measure E := (sphereLaw (E := E)).map Subtype.val

end NoiselessRegression

end InlineMainProof

open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section GaussianGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianGraph

section

section BallDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end BallDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section Rotations

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev Rotation := unitary (E →L[ℝ] E)

instance rotationMeasurableSpace : MeasurableSpace (Rotation E) := borel (Rotation E)

instance rotationBorelSpace : BorelSpace (Rotation E) := ⟨rfl⟩

instance rotationCompact : CompactSpace (Rotation E) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  apply (Metric.isBounded_closedBall (x := (0 : E →L[ℝ] E)) (r := 1)).subset (s := (unitary (E →L[ℝ] E) : Set (E →L[ℝ] E)))
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases h : Subsingleton E
  · have := h
    simp
  · have : Nontrivial E := not_subsingleton_iff_nontrivial.mp h
    exact (CStarRing.norm_of_mem_unitary hU).le

variable {E}

variable [MeasurableSpace E] [BorelSpace E]

end Rotations

section Triangular

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Triangular

section CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end CoordinateDensity

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

namespace Learner

section

universe u

variable {d M T : ℕ} {Ω : Type u}

abbrev TaggedState (M T : ℕ) := Sum (State M) (Fin (T+1) × State M)

instance taggedMeasurableSpace : MeasurableSpace (TaggedState M T) := ⊤

end

universe u

variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

end Learner

namespace FiniteKernelLearner

variable {d M T : ℕ}

end FiniteKernelLearner

section

variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

end

namespace FiniteKernelLearner

section

open Learner

variable {d M T : ℕ}

end

open Learner

variable {d M T : ℕ}

end FiniteKernelLearner

section

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace Learner

variable {d M T : ℕ} {Ω : Type u}

end Learner

end

namespace FiniteKernelLearner

section

universe u

variable {d M T : ℕ}

end

universe u

variable {d M T : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]

end FiniteKernelLearner

end NoiselessRegression

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

-- [generator] trimmed: open NoiselessRegression NoiselessRegression.FiniteKernelLearner
open NoiselessRegression

open scoped ENNReal NNReal RealInnerProductSpace Topology

universe u

namespace ProjectionMoments

end ProjectionMoments

end

end OAI


