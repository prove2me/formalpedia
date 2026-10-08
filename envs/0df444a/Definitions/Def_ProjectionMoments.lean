-- Prove2me | Definitions.Def_ProjectionMoments
-- name    : ProjectionMoments
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:11.972687+00:00
-- url     : https://prove2.me/theorems/14c45482-43b2-41d4-9d97-7fa6048cf582
-- statement:
--   This block sets up a noiseless linear-regression learning model on the unit sphere and then defines a conjunction of fifteen propositions about projection moments and streaming lower bounds. A hidden direction s is drawn uniformly (normalized surface measure) from the unit sphere of R^d; the learner sees T rows x_i drawn from i.i.d. standard Gaussians together with noiseless labels <x_i,s>, has M bits of memory (states Fin(2^M)), and must output a unit vector whose angular error arccos<ŝ,s> is at most ε. A Learner is a randomized-seed deterministic rule with an initial choice (stop or continue plus a state), per-step transitions from (state, row, label) and outputs indexed by stopping time; its run stops at the first step where it elects to, otherwise at time T, and uniformSuccess is the product-measure probability of angular error at most ε, with a variant that also fixes the stopping time t; Admissible and MeasurableRules record measurability requirements. A FiniteKernelLearner is the probabilistic version, with probability-measure-valued initial, transition and output kernels; CompletedRules asks each transition probability of a singleton to be almost-everywhere measurable in the observation. Its success laws are built by iterating the kernels through a tagged state recording the stopping time, giving uniformSuccess, uniformFixedSuccess, seeded averages over a probability space Ξ of learners, and a conditional success for a fixed s and sample. Supporting objects include ball-averaged lower densities of the law of the projection of a measure ν under a frame of k row vectors (the Lebesgue-density liminf of averages over balls of radius 1/(n+1)), the all-ball-mass condition ν(B(b,t)) ≤ K t^a, Haar-distributed rotations and the induced frame law of rotated orthonormal frames, the Riesz kernel and the supremum of its sphere potential, polar rows obtained from the matrix square root of the Gram matrix, the normalized unit-ball law, spherical caps with their normalized measures, and a CapDictionary, a countable family of caps covering the sphere at all scales between 4rt and 8rt and containing the parent cap, with a properness condition. The defined propositions assert, with absolute constants and dimension thresholds, the following: an integrated moment bound on the Lq-norm of coordinate densities of ν over random orthonormal frames; a normalized unit-ball L^k moment bound of size exp(C_D d k); an all-radii sphere moment bound for densities f≤1; a positive cap domination statement decomposing the cap reference of kernels with total mass at most 1 into dictionary caps; a deterministic-offset density bound via the Riesz potential; an all-radii bound for fractional blocks; Haar and Riesz streaming-cost bounds and cap-based fixed- and total-stopping-time cost bounds, plus asymptotic versions for memory M(d)=o(d^2), all upper-bounding the seeded success probability by exponentially small expressions in d, ε, T and M; KernelModelBridge, saying that for d≥3 every completed-rule kernel learner is matched in uniform and fixed-stopping success by a measurable admissible Learner on a probability tape space; and two sample-complexity statements, FixedQuadraticMemory and SubquadraticMemoryWithPointwise, saying that success probability at least 2/3 at accuracy ε≤1/10 forces T ≥ c d log(1/ε). MainStatement is the conjunction of all fifteen propositions; these are defined propositions, not established theorems.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProjectionMoments.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ProjectionMoments.lean; bytes 16..29579
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace Topology

universe u

namespace NoiselessRegression

section

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1

abbrev State (M : ℕ) := Fin (2 ^ M)

abbrev Samples (d T : ℕ) := Fin T → Vector d

def uniformSphere (d : ℕ) : Measure (UnitSphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ

def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

structure Learner (d M T : ℕ) (Ω : Type u) where
  initialChoice : Ω → Bool × State M
  transition : ℕ → Ω → State M → (Vector d × ℝ) → Bool × State M
  output : ℕ → Ω → State M → UnitSphere d

namespace Learner

abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)

def start {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω) (ω : Ω) :
    RunStatus M :=
  let a := L.initialChoice ω
  if a.1 then .inr (0, a.2) else .inl a.2

def run {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → RunStatus M
  | 0 => L.start ω
  | n + 1 =>
    match L.run s ω x n with
    | .inr done => .inr done
    | .inl state =>
      if hn : n < T then
        let row := x ⟨n, hn⟩
        let a := L.transition (n + 1) ω state (row, ⟪row, s.val⟫)
        if a.1 then .inr (n + 1, a.2) else .inl a.2
      else .inl state

def terminal {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ × State M :=
  match L.run s ω x T with
  | .inl state => (T, state)
  | .inr done => done

def estimate {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : UnitSphere d :=
  let a := L.terminal s ω x
  L.output a.1 ω a.2

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  initialChoice : AEMeasurable L.initialChoice ρ
  transition : ∀ t a, AEMeasurable (fun z : Ω × (Vector d × ℝ) =>
    L.transition t z.1 a z.2) (ρ.prod (observationReference d))
  output : ∀ t a, AEMeasurable (fun ω => L.output t ω a) ρ
  fixed_experiment : ∀ s, AEMeasurable (fun z : Ω × Samples d T =>
    L.estimate s z.1 z.2) (ρ.prod (sampleLaw d T))
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def angularError {d : ℕ} (s ŝ : UnitSphere d) : ℝ :=
  Real.arccos ⟪ŝ.val, s.val⟫

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}

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

end

section

section

variable {d M T : ℕ} {Ω : Type u}

abbrev Learner.TaggedState (M T : ℕ) := Sum (State M) (Fin (T+1) × State M)

instance Learner.taggedMeasurableSpace : MeasurableSpace (TaggedState M T) := ⊤

def Learner.taggedStart (a : Bool × State M) : TaggedState M T :=
  if a.1 then .inr (⟨0,by omega⟩,a.2) else .inl a.2

end

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

structure Learner.MeasurableRules (L : Learner d M T Ω) : Prop where
  initial : Measurable L.initialChoice
  transition : ∀ t j, Measurable (fun z : Ω × (Vector d × ℝ) => L.transition t z.1 j z.2)
  output : ∀ t j, Measurable (fun ω => L.output t ω j)

end

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

structure FiniteKernelLearner (d M T : ℕ) where
  initial : Measure (Bool × State M)
  initial_probability : IsProbabilityMeasure initial
  transition : ℕ → State M → (Vector d × ℝ) → Measure (Bool × State M)
  transition_probability : ∀ t j obs, IsProbabilityMeasure (transition t j obs)
  output : ℕ → State M → Measure (UnitSphere d)
  output_probability : ∀ t j, IsProbabilityMeasure (output t j)

namespace FiniteKernelLearner

variable {d M T : ℕ}

structure CompletedRules (K : FiniteKernelLearner d M T) : Prop where
  transition : ∀ t j a, AEMeasurable (fun obs => K.transition t j obs {a}) (observationReference d)

end FiniteKernelLearner

open MeasureTheory ProbabilityTheory Set Filter unitInterval

section CoinRun

variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

def kernelRun (P : ℕ → J → O → Measure J) : (n : ℕ) → J → (Fin n → O) → Measure J
  | 0, j, _ => Measure.dirac j
  | n+1, j, obs => (kernelRun P n j (Fin.init obs)).bind (fun a => P (n+1) a (obs (Fin.last n)))

end CoinRun

section

section

open Learner

variable {d M T : ℕ}

abbrev FiniteKernelLearner.Tape (M T : ℕ) := (Bool × State M) × ((Fin T → I) × I)

def FiniteKernelLearner.destination (t : ℕ) (h : t ≤ T) (a : Bool × State M) : TaggedState M T :=
  if a.1 then .inr (⟨t,by omega⟩,a.2) else .inl a.2

def FiniteKernelLearner.taggedKernel (K : FiniteKernelLearner d M T) (t : ℕ) :
    TaggedState M T → (Vector d × ℝ) → Measure (TaggedState M T)
  | .inr a, _ => Measure.dirac (.inr a)
  | .inl j, obs => if ht : t ≤ T then (K.transition t j obs).map (destination t ht)
    else Measure.dirac (.inl j)

def FiniteKernelLearner.terminalOutput (K : FiniteKernelLearner d M T) : TaggedState M T → Measure (UnitSphere d)
  | .inl j => K.output T j
  | .inr (t,j) => K.output t j

end

open MeasureTheory ProbabilityTheory Set Filter unitInterval

open scoped ENNReal NNReal RealInnerProductSpace

open Learner

variable {d M T : ℕ}

abbrev FiniteKernelLearner.Result (d M : ℕ) := (ℕ × State M) × UnitSphere d

def FiniteKernelLearner.terminalTag : TaggedState M T → ℕ × State M
  | .inl j => (T,j)
  | .inr (t,j) => (t,j)

def FiniteKernelLearner.terminalJointOutput (K : FiniteKernelLearner d M T) (j : TaggedState M T) : Measure (Result d M) :=
  (K.terminalOutput j).map (fun y => (terminalTag j,y))

def FiniteKernelLearner.jointExperimentLaw (K : FiniteKernelLearner d M T) (obs : Fin T → (Vector d × ℝ)) : Measure (Result d M) :=
  K.initial.bind (fun a => (kernelRun K.taggedKernel T (taggedStart a) obs).bind K.terminalJointOutput)

def FiniteKernelLearner.uniformSuccess (K : FiniteKernelLearner d M T) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × Samples d T,
    K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫))
      {r | angularError z.1 r.2 ≤ ε} ∂((uniformSphere d).prod (sampleLaw d T))

def FiniteKernelLearner.uniformFixedSuccess (K : FiniteKernelLearner d M T) (ε : ℝ) (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × Samples d T,
    K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫))
      {r | r.1.1 = t ∧ angularError z.1 r.2 ≤ ε} ∂((uniformSphere d).prod (sampleLaw d T))

end

section

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {d M T : ℕ} {Ω : Type u}

def Learner.uniformFixedSuccess [MeasurableSpace Ω] (L : Learner d M T Ω) (ρ : Measure Ω)
    (ε : ℝ) (t : ℕ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | (L.terminal z.1 z.2.1 z.2.2).1 = t ∧ angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}

end

section

variable {d M T : ℕ}

def FiniteKernelLearner.seededSuccess {Ξ : Type u} [MeasurableSpace Ξ]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, (K ξ).uniformSuccess ε ∂ρ

def FiniteKernelLearner.seededFixedSuccess {Ξ : Type u} [MeasurableSpace Ξ]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) (ε : ℝ) (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ ξ, (K ξ).uniformFixedSuccess ε t ∂ρ

def FiniteKernelLearner.FixedQuadraticMemory : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → ∀ M T : ℕ, (M : ℝ) ≤ A₀ * (d : ℝ)^2 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
    ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
    (2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε →
    c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)

end

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal RealInnerProductSpace

variable {d M T : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]

def FiniteKernelLearner.conditionalSuccess (K : FiniteKernelLearner d M T) (ε : ℝ)
    (s : UnitSphere d) (x : Samples d T) : ℝ≥0∞ :=
  K.jointExperimentLaw (fun i => (x i,⟪s.val,x i⟫)) {r | Learner.angularError s r.2 ≤ ε}

def FiniteKernelLearner.seededPointwiseSuccess (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ)
    (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  ∫⁻ z : Ξ × Samples d T, (K z.1).conditionalSuccess ε s z.2 ∂ρ.prod (sampleLaw d T)

def FiniteKernelLearner.JointSuccessMeasurable (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) (ε : ℝ) : Prop :=
  AEMeasurable (fun z : UnitSphere d × (Ξ × Samples d T) =>
    (K z.2.1).conditionalSuccess ε z.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def FiniteKernelLearner.SubquadraticMemoryWithPointwise : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d:ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
    ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
    ((2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε ∨
      (JointSuccessMeasurable K ρ ε ∧ ∀ s, (2/3 : ℝ≥0∞) ≤ seededPointwiseSuccess K ρ ε s)) →
    c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)

end NoiselessRegression

namespace ProjectionMoments

open NoiselessRegression NoiselessRegression.FiniteKernelLearner

section

section GaussianGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def vectorSmoothing (ν : Measure E) (m : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞)
    (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t, φ (fun j => z.2 j - ⟪t, z.1 j⟫) ∂ν

abbrev Label (m : ℕ) := EuclideanSpace ℝ (Fin m)

def ballKernel (m : ℕ) (η : ℝ) (y : Fin m → ℝ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : Label m) η).indicator
    (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹) (WithLp.toLp 2 y)

def rowMap {m : ℕ} (A : Fin m → E) : E →L[ℝ] Label m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))

def ballAverage (ν : Measure E) (m : ℕ) (η : ℝ)
    (z : (Fin m → E) × Label m) : ℝ≥0∞ :=
  vectorSmoothing ν m (ballKernel m η) (z.1, WithLp.ofLp z.2)

def lowerDensity (ν : Measure E) (m : ℕ) (z : (Fin m → E) × Label m) : ℝ≥0∞ :=
  liminf (fun n : ℕ => ballAverage ν m ((n : ℝ) + 1)⁻¹ z) atTop

def AllBallMass (ν : Measure E) (K a : ℝ) : Prop :=
  ∀ b : E, ∀ t : ℝ, 0 < t → ν (Metric.closedBall b t) ≤ ENNReal.ofReal (K * t ^ a)

end GaussianGraph

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace Topology

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

def rotationLaw : Measure (Rotation E) :=
  ((Measure.haar : Measure (Rotation E)) Set.univ)⁻¹ • Measure.haar

variable {E}

variable [MeasurableSpace E] [BorelSpace E]

def rotateRows {ι : Type*} (O : Rotation E) (v : ι → E) : ι → E :=
  fun i => (O : E →L[ℝ] E) (v i)

end Rotations

section Triangular

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def coordinateMap {m : ℕ} (A : Fin m → E) : E →ₗ[ℝ] (Fin m → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)) ∘ₗ (rowMap A).toLinearMap

def coordinateDensity (ν : Measure E) (m : ℕ) (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  lowerDensity ν m (z.1, WithLp.toLp 2 z.2)

def frameLaw {m : ℕ} (u : Fin m → E) : Measure (Fin m → E) :=
  (rotationLaw E).map (fun O => rotateRows O u)

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace Topology

def rieszKernel (α : ℝ) (z s : E) : ℝ≥0∞ := (ENNReal.ofReal ‖s-z‖)^(-α)

def rieszPotential (α : ℝ) (h : E → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ z : E, ∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix

open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator

def mixRows {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) : Fin k → E :=
  fun i => ∑ j, M i j • X j

def polarRadial {k : ℕ} (X : Fin k → E) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt (Matrix.gram ℝ X)

def rawPolarRows {k : ℕ} (X : Fin k → E) : Fin k → E :=
  mixRows (polarRadial X)⁻¹ X

def polarRows {k : ℕ} (u X : Fin k → E) : Fin k → E := by
  classical
  exact if LinearIndependent ℝ X then rawPolarRows X else u

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace Topology

def unitBallVolume (k : ℕ) : ℝ≥0∞ := (volume : Measure (Label k)) (Metric.closedBall 0 1)

def unitBallLaw (k : ℕ) : Measure (Label k) :=
  (unitBallVolume k)⁻¹ • volume.restrict (Metric.closedBall 0 1)

def normalizedDensity (ν : Measure E) (k : ℕ) (u : Fin k → E)
    (z : (Fin k → E) × Label k) : ℝ≥0∞ :=
  unitBallVolume k * lowerDensity ν k (polarRows u z.1,z.2)

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace Topology

def sphereWeightedRestriction (h : E → ℝ≥0∞) (H : Set E) : Measure E :=
  (NoiselessRegression.ambientSphereLaw.withDensity h).restrict H

end Triangular

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def capMeasure (c : E) (r : ℝ) : Measure E :=
  (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ •
    NoiselessRegression.ambientSphereLaw.restrict (Metric.closedBall c r)

structure CapDictionary (c : E) (r α : ℝ) where
  I : Type u
  countable : Countable I
  center : I → E
  radius : I → ℝ
  center_norm : ∀ i, ‖center i‖ = 1
  radius_pos : ∀ i, 0 < radius i
  radius_le : ∀ i, radius i ≤ r
  parent : I
  parent_center : center parent = c
  parent_radius : radius parent = r
  proper : ∀ R : ℝ, {i | (r/radius i)^α ≤ R}.Finite
  cover : ∀ (s : E), ‖s‖ = 1 → ∀ t : ℝ, 0 < t → t ≤ 1/4 →
    ∃ i, 4*r*t ≤ radius i ∧ radius i < 8*r*t ∧ dist s (center i) ≤ radius i/2

end

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix

open scoped ENNReal NNReal RealInnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def radialLabel {k : ℕ} (X : Fin k → E) (y : Label k) : Label k :=
  WithLp.toLp 2 (polarRadial X *ᵥ y.ofLp)

def capKernelValue {k : ℕ} (K : (Fin k → E) × Label k → ℝ≥0∞) (s : E) : ℝ≥0∞ :=
  ∫⁻ X, K (X,rowMap X s) ∂Measure.pi (fun _ => stdGaussian E)

def capReferenceLabel {k : ℕ} (c : E) (r : ℝ) (X : Fin k → E) (z : Label k) : Label k :=
  rowMap X c + r • radialLabel X z

def capReference {k : ℕ} (K : (Fin k → E) × Label k → ℝ≥0∞) (c : E) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ X, ∫⁻ z, K (X,capReferenceLabel c r X z) ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E)

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def fractionalBlock {J : Type*} [Fintype J] {k : ℕ}
    (Q : J → (Fin k → E) × Label k → ℝ≥0∞) (f : J → E → ℝ≥0∞) (s : E) : ℝ≥0∞ :=
  ∫⁻ X, ∑ j, Q j (X,rowMap X s)*f j s ∂Measure.pi (fun _ => stdGaussian E)

end

def IntegratedFrameMoment : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d k q : ℕ) (β K R : ℝ)
      (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
      (z : EuclideanSpace ℝ (Fin d)) (u : Fin k → EuclideanSpace ℝ (Fin d)),
      1 ≤ k → 2 ≤ q → k+q ≤ d → 0 < β → β ≤ d →
      1 ≤ β-k-((q:ℝ)-2) → 0 ≤ K → 0 < R →
      ν.support ⊆ Metric.closedBall z R → AllBallMass ν K β →
      Orthonormal ℝ u →
      (∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) →
      Measurable (coordinateDensity ν k) ∧
      (∀ᵐ A ∂frameLaw u,
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity ν k (A,y)) =
          ν.map (coordinateMap A)) ∧
      (∀ (A : Fin k → EuclideanSpace ℝ (Fin d)), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ,
          R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ → coordinateDensity ν k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity ν k (A,y)^q ∂volume ∂frameLaw u) ^ (1/(q:ℝ)) ≤
        ENNReal.ofReal (C^d * (C*Real.sqrt d)^((k:ℝ)*(1-1/(q:ℝ))) *
          K * R^(β-(k:ℝ)*(1-1/(q:ℝ))))

def NormalizedUnitBallMoment : Prop :=
  ∀ D : ℝ, 0 < D →
    ∃ C_D : ℝ, 0 < C_D ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let lam : ℝ := ((d:ℝ)-1)/2
      ∀ (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
        (u : Fin k → EuclideanSpace ℝ (Fin d)),
        ν Set.univ ≤ 1 → ν.support ⊆ Metric.closedBall 0 1 →
        AllBallMass ν (D^d) lam → Orthonormal ℝ u →
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) →
        Measurable (normalizedDensity ν k u) ∧
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
            (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X))) ∧
        (∀ X y, 1 < ‖y‖ → normalizedDensity ν k u (X,y) = 0) ∧
        (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^k ∂unitBallLaw k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
          ENNReal.ofReal (Real.exp (C_D*d*k))

def AllRadiiSphereMoment : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      Measurable f → (∀ s, f s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity f) K β →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ R : ℝ, 0 < R →
      ∀ u : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ u →
      let μ := sphereWeightedRestriction f (Metric.closedBall z R)
      Measurable (coordinateDensity μ k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity μ k (A,y)) =
          μ.map (coordinateMap A)) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ, R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ →
          coordinateDensity μ k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity μ k (A,y)^k ∂volume ∂frameLaw u) ^ (1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d*(C*Real.sqrt d)^((k:ℝ)*(1-1/(k:ℝ)))*
          K*R^(β-(k:ℝ)*(1-1/(k:ℝ))))

def PositiveCapDomination : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 → ∀ N : ℕ,
      ∀ K : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (K j)) → (∀ z, ∑ j, K j z ≤ 1) →
      (∑ j, capReference (K j) c r) ≤ 1 ∧
      ∀ j, ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference (K j) c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue (K j)) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞

def DeterministicOffsetDensity : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/8
      let α : ℝ := (d:ℝ)/2
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h → (∀ s, h s ≤ 1) →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ ρ : ℝ, 0 < ρ →
      ∀ H : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet H → H ⊆ Metric.closedBall z ρ →
      rieszPotential α h < ∞ ∧
      Measurable (lowerDensity (sphereWeightedRestriction h H) k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), LinearIndependent ℝ A →
        volume.withDensity (fun y => lowerDensity (sphereWeightedRestriction h H) k (A,y)) =
          (sphereWeightedRestriction h H).map (rowMap A)) ∧
      (∀ b : Label k, (∫⁻ A, (lowerDensity (sphereWeightedRestriction h H) k (A,rowMap A z+b))^k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d))))^(1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d) * rieszPotential α h * ENNReal.ofReal (ρ^(α-k))) ∧
      (∀ A y, ‖rowMap A‖*ρ < ‖y-rowMap A z‖ →
        lowerDensity (sphereWeightedRestriction h H) k (A,y) = 0)

def AllRadiiBlockBound : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ N : ℕ, ∀ f : Fin N → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      (∀ j, Measurable (f j)) → (∀ j s, f j s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ j, AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (f j)) K β) →
      ∀ Q : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (Q j)) → (∀ z, ∑ j, Q j z ≤ 1) →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (fractionalBlock Q f))
        (C^d*(N:ℝ)^(1/(k:ℝ))*K) β

def HaarStreamingCost : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k))

def RieszStreamingCost : Prop :=
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q))

def CapFixedStoppingCost : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((t+k-1)/k))

def CapTotalStoppingCost : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (((T:ℝ)+1)*Real.exp (C*d)*(ε/2)^α*
          (Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((T+k-1)/k))

def CapFixedStoppingAsymptotic : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun d => (M d:ℝ)) (fun d => (d:ℝ)^2) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d*(1+((t+k-1)/k:ℕ)))*(ε/2)^α)

def CapTotalStoppingAsymptotic : Prop :=
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ M : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun d => (M d:ℝ)) (fun d => (d:ℝ)^2) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (((T:ℝ)+1)*Real.exp (C₁*d+C₂*T-(d:ℝ)*Real.log (1/ε)/3))

def KernelModelBridge : Prop :=
  ∀ d M T : ℕ, 3 ≤ d → ∀ K : FiniteKernelLearner d M T, K.CompletedRules →
    ∃ (ρ : Measure (Tape M T)) (L : Learner d M T (Tape M T)),
      IsProbabilityMeasure ρ ∧ L.MeasurableRules ∧ L.Admissible ρ ∧
      (∀ ε, L.uniformSuccess ρ ε = K.uniformSuccess ε) ∧
      (∀ ε t, L.uniformFixedSuccess ρ ε t = K.uniformFixedSuccess ε t)

def MainStatement : Prop :=
  IntegratedFrameMoment ∧ NormalizedUnitBallMoment ∧ AllRadiiSphereMoment ∧
  PositiveCapDomination ∧ DeterministicOffsetDensity ∧ AllRadiiBlockBound ∧
  HaarStreamingCost.{u} ∧ RieszStreamingCost.{u} ∧ CapFixedStoppingCost.{u} ∧
  CapTotalStoppingCost.{u} ∧ CapFixedStoppingAsymptotic.{u} ∧
  CapTotalStoppingAsymptotic.{u} ∧ KernelModelBridge ∧
  NoiselessRegression.FiniteKernelLearner.SubquadraticMemoryWithPointwise.{u} ∧
  NoiselessRegression.FiniteKernelLearner.FixedQuadraticMemory.{u}

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology



end ProjectionMoments
end
end OAI


