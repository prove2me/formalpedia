-- Prove2me | Definitions.Def_SubsphereCurrent
-- name    : SubsphereCurrent
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:27.477656+00:00
-- url     : https://prove2.me/theorems/63d14e24-f7ca-4168-a96d-da3484471f5f
-- statement:
--   This block formalizes a model of adaptive learning of an unknown unit vector s in the sphere S^{d-1} of Euclidean space R^d from T linear measurements <x_i,s>, together with a collection of defined (not proved) propositions about its sample complexity. The basic objects are the normalized surface measure on a sphere, T independent standard Gaussian sample vectors x_1,...,x_T, and a reference measure on observations (Gaussian vector, real number). A KernelLearner with memory M has a finite state space of 2^M states, a random initial pair (halt flag, state), time-dependent randomized transition rules that read the observation (x_n, <x_n,s>) and return a new flag and state, and for each time and state an output probability measure on the sphere. Running it for T steps, once the flag is set the time and state are frozen, so the learner effectively stops, and otherwise it runs to time T; the output law is the mixture of output measures over the terminal (time, state), and conditional success at accuracy ε is the probability that the output u has angular error arccos<u,s> at most ε. A SeededLearner is a family of such learners indexed by a random seed ω with law ρ, and it is Admissible if the rules are almost surely measurable in the observation and the success functions are almost-everywhere measurable jointly with the seed and samples, both for fixed s and for s uniform on the sphere. Success and uniformSuccess are the corresponding integrals over seed and samples, for fixed s or additionally averaged over uniform s. ExplicitPrecision states that whenever M(d) is little-o of d^2, there is a threshold d0 such that for all d ≥ d0, all T, all 0<ε≤1/10, every probability seed space and every admissible seeded learner with memory M(d) and T samples that achieves success probability at least 2/3 either on average over uniform s or at every fixed s must have T ≥ 2^{-16} d log2(1/ε). HalfPrecision is the same with success probability at least 1/2 in the uniform-average sense only, concluding T ≥ c d log2(1/ε) for some universal c>0. The remaining definitions are auxiliary estimates. Affine tests are pairs of an n-dimensional subspace and a center orthogonal to it with ‖center‖^2+radius^2=1 and positive radius, giving a sub-sphere of points center + radius·s that lies on the unit sphere. A radius-weighted norm of a function g on the sphere is the supremum over such tests of radius^{d/16} times the integral of g over the sub-sphere. RadiusWeightedFullEstimate asserts, for large d, a bound of this norm for block-averaged mixtures of at most W functions with values in [0,1], comparing dimension n with n-2, and a bound on the norm of the terminal ε-cap indicator of any probability measure by C^d ε^{d/16}. Fixed.DimensionEstimate bounds the success of streaming learners with at most 2^{d^2} states in a fixed m-dimensional space by (C^{j+1} η)^{d/32} for Euclidean accuracy η, and Affine.AllAffineFullEstimate bounds angular success of suffix learners on affine sub-spheres by (16·1000^{32ℓ}ε/radius)^{2⌊d/32⌋}. Finally, Mixture defines Haar measure on the orthogonal group, block isometries acting on a subspace V and its complement, and direction and latitude laws, and MixtureEstimate asserts that the direction law is dominated by 2^{dim E} times the sum of the uniform sphere law and a Beta-latitude law, that it equals the uniform sphere law when V is zero, and that the joint law equals the product of uniform sphere laws when N is the whole space. CurrentMainScope is the conjunction of all six propositions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SubsphereCurrent.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SubsphereCurrent.lean; bytes 16..17965
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent
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

structure KernelLearner (d M T : ℕ) where
  initial : PMF (Bool × State M)
  transition : ℕ → State M → (Vector d × ℝ) → PMF (Bool × State M)
  output : ℕ → State M → Measure (UnitSphere d)
  output_probability : ∀ t q, IsProbabilityMeasure (output t q)

namespace KernelLearner
abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)

def tagged (M t : ℕ) (a : Bool × State M) : RunStatus M :=
  if a.1 then .inr (t, a.2) else .inl a.2

def run {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : ℕ → PMF (RunStatus M)
  | 0 => L.initial.map (tagged M 0)
  | n + 1 => (L.run s x n).bind fun status =>
      match status with
      | .inr done => PMF.pure (.inr done)
      | .inl q => if hn : n < T then
          (L.transition (n + 1) q (x ⟨n, hn⟩, ⟪x ⟨n, hn⟩, s.val⟫)).map (tagged M (n + 1))
        else PMF.pure (.inl q)

def terminal {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : PMF (ℕ × State M) :=
  (L.run s x T).map fun status =>
    match status with
    | .inl q => (T, q)
    | .inr done => done

def estimateLaw {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : Measure (UnitSphere d) :=
  (L.terminal s x).toMeasure.bind fun a => L.output a.1 a.2

def angularError {d : ℕ} (s u : UnitSphere d) : ℝ :=
  Real.arccos ⟪u.val, s.val⟫

def conditionalSuccess {d M T : ℕ} (L : KernelLearner d M T) (ε : ℝ)
    (s : UnitSphere d) (x : Samples d T) : ℝ≥0∞ :=
  L.estimateLaw s x {u | angularError s u ≤ ε}

def CompletedRules {d M T : ℕ} (L : KernelLearner d M T) : Prop :=
  ∀ t q dest, AEMeasurable (fun obs => L.transition t q obs dest) (observationReference d)

end KernelLearner

structure SeededLearner (d M T : ℕ) (Ω : Type u) where
  rules : Ω → KernelLearner d M T

namespace SeededLearner

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) : Prop where
  completed_rules : ∀ᵐ ω ∂ρ, (L.rules ω).CompletedRules
  fixed_experiment : ∀ s ε, AEMeasurable
    (fun z : Ω × Samples d T => (L.rules z.1).conditionalSuccess ε s z.2)
    (ρ.prod (sampleLaw d T))
  uniform_experiment : ∀ ε, AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) =>
      (L.rules z.2.1).conditionalSuccess ε z.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  ∫⁻ z : Ω × Samples d T, (L.rules z.1).conditionalSuccess ε s z.2
    ∂(ρ.prod (sampleLaw d T))

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × (Ω × Samples d T),
    (L.rules z.2.1).conditionalSuccess ε z.1 z.2.2
      ∂((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
end SeededLearner

def ExplicitPrecision : Prop :=
  ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : SeededLearner d (M d) T Ω, L.Admissible ρ →
    ((2 / 3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, (2 / 3 : ℝ≥0∞) ≤ L.success ρ ε s) →
    (2 : ℝ)⁻¹ ^ 16 * (d : ℝ) * Real.logb 2 (1 / ε) ≤ (T : ℝ)
end SubsphereCurrent
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Sphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

def sphereLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Sphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

structure Test (d n : ℕ) where
  space : Submodule ℝ (Vector d)
  dimension : Module.finrank ℝ space = n
  center : Vector d
  perpendicular : center ∈ spaceᗮ
  radius : ℝ
  radius_positive : 0 < radius
  unit : ‖center‖^2 + radius^2 = 1

def Test.point {d n : ℕ} (A : Test d n) (s : Sphere A.space) : Vector d :=
  A.center + A.radius • s.val.val

end SubsphereCurrent.Affine
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe v
namespace SubsphereCurrent.Weighted
abbrev Vector (d : ℕ) := Affine.Vector d
abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
abbrev Rows (d k : ℕ) := Fin k → Vector d
abbrev Observation (d k : ℕ) := Rows d k × (Fin k → ℝ)

def onTest {d n : ℕ} (A : Affine.Test d n) (s : Affine.Sphere A.space) : Sphere d := by
  refine ⟨A.point s,mem_sphere_zero_iff_norm.mpr ?_⟩
  have hs : ‖(s.val : Vector d)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  have ho : ⟪A.center, (s.val : Vector d)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal s.val.property A.perpendicular
  have hz : ‖A.point s‖^2 = 1 := by
    rw [Affine.Test.point,norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.radius_positive,hs,mul_one]
    nlinarith [A.unit]
  nlinarith [norm_nonneg (A.point s)]

def norm (d n : ℕ) (g : Sphere d → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ A : Affine.Test d n, (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
    ∫⁻ s : Affine.Sphere A.space, g (onTest A s) ∂Affine.sphereLaw A.space

def blockInput {d k : ℕ} {V : Type*} [Fintype V]
    (κ : V → Observation d k → ℝ≥0∞) (g : V → Sphere d → ℝ≥0∞)
    (s : Sphere d) : ℝ≥0∞ :=
  ∫⁻ X : Rows d k, ∑ v, κ v (X,fun i => ⟪X i,s.val⟫)*g v s
    ∂Measure.pi (fun _ => stdGaussian (Vector d))

def terminalInput {d : ℕ} (π : Measure (Sphere d)) (ε : ℝ) (s : Sphere d) : ℝ≥0∞ :=
  π {u | Real.arccos ⟪u.val,s.val⟫ ≤ ε}

end SubsphereCurrent.Weighted
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe v
namespace SubsphereCurrent.Weighted

def RadiusWeightedFullEstimate : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ W : ℝ, 1 ≤ W → ∀ (V : Type v) [Fintype V] [Nonempty V],
      (Fintype.card V : ℝ) ≤ W →
      ∀ κ : V → Observation d (d/16) → ℝ≥0∞,
      (∀ v, Measurable (κ v)) → (∀ obs, ∑ v, κ v obs ≤ 1) →
      ∀ g : V → Sphere d → ℝ≥0∞,
      (∀ v, Measurable (g v)) → (∀ v s, g v s ≤ 1) →
      ∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      norm d n (blockInput κ g) ≤
        (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ))*ENNReal.ofReal (C^d)*(⨆ v, norm d (n-2) (g v))) ∧
    (∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      ∀ π : Measure (Sphere d), IsProbabilityMeasure π →
      ∀ ε : ℝ, 0 < ε →
      norm d n (terminalInput π ε) ≤ ENNReal.ofReal (C^d)*(ENNReal.ofReal ε)^((d : ℝ)/16))

end SubsphereCurrent.Weighted
end

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

def HalfPrecision : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : SeededLearner d (M d) T Ω, L.Admissible ρ →
    (1/2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.logb 2 (1/ε) ≤ (T : ℝ)
end SubsphereCurrent
end

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent
namespace Fixed

abbrev Vector (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Sphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

def sphereLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Sphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

def rowsLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (T : ℕ) :
    Measure (Fin T → E) := Measure.pi fun _ => stdGaussian E

structure Stream (E J : Type*) [MeasurableSpace E] (T : ℕ) where
  initial : PMF J
  transition : ℕ → J → (E × ℝ) → PMF J
  output : J → Measure E
  output_probability : ∀ q, IsProbabilityMeasure (output q)

namespace Stream
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J]
  {T : ℕ}

def run (L : Stream E J T) (s : E) (x : Fin T → E) : ℕ → PMF J
  | 0 => L.initial
  | n+1 => (L.run s x n).bind fun q => if hn : n < T then
      L.transition (n+1) q (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s⟫)
    else PMF.pure q

def estimateLaw (L : Stream E J T) (s : E) (x : Fin T → E) : Measure E :=
  (L.run s x T).toMeasure.bind L.output

def euclideanSuccess (L : Stream E J T) (η : ℝ) (s : E) (x : Fin T → E) : ℝ≥0∞ :=
  L.estimateLaw s x {y | ‖y-s‖ ≤ η}

def angularSuccess (L : Stream E J T) (ε : ℝ) (s : E) (x : Fin T → E) : ℝ≥0∞ :=
  L.estimateLaw s x {y | Real.arccos ⟪y,s⟫ ≤ ε}

def BorelRules (L : Stream E J T) : Prop :=
  ∀ n q a, Measurable (fun obs => L.transition n q obs a)

def suffix (L : Stream E J T) (n k : ℕ) (v : J) : Stream E J k where
  initial := PMF.pure v
  transition t := L.transition (n+t)
  output := L.output
  output_probability := L.output_probability

end Stream

def DimensionEstimate : Prop :=
  ∃ C : ℝ, 2 ≤ C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ j m : ℕ,
    (d : ℝ)/2 + 2*j ≤ m → m ≤ d →
    ∀ η : ℝ, 0 < η →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → Stream (Vector m) (Fin (2^(d^2))) (j*(d/32)),
    (∀ᵐ ω ∂ρ, (L ω).BorelRules) →
    AEMeasurable (fun z : Sphere (Vector m) × (Ω × (Fin (j*(d/32)) → Vector m)) =>
      (L z.2.1).euclideanSuccess η z.1.val z.2.2)
      ((sphereLaw (Vector m)).prod (ρ.prod (rowsLaw (Vector m) (j*(d/32))))) →
    (∫⁻ z : Sphere (Vector m) × (Ω × (Fin (j*(d/32)) → Vector m)),
      (L z.2.1).euclideanSuccess η z.1.val z.2.2
        ∂(sphereLaw (Vector m)).prod (ρ.prod (rowsLaw (Vector m) (j*(d/32)))))
      ≤ ENNReal.ofReal ((C^(j+1)*η)^((d : ℝ)/32))

end Fixed
end SubsphereCurrent
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

def AllAffineFullEstimate : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
    (d+1)/2 + 2*k ≤ d → ∀ W : ℝ, 1 ≤ W →
    ∀ (J : Type v) [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J],
    (Fintype.card J : ℝ) ≤ W → W^(1/((d/8 : ℕ) : ℝ)) ≤ (2 : ℝ)^d →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → Fixed.Stream (Vector d) J (k*(d/16)),
    (∀ᵐ ω ∂ρ, (L ω).BorelRules ∧ ∀ q, ∀ᵐ y ∂(L ω).output q, ‖y‖ = 1) →
    ∀ ell : ℕ, ell ≤ k → ∀ v : J, ∀ n : ℕ, (d+1)/2 + 2*ell ≤ n →
    ∀ A : Test d n,
    (∫⁻ z : Sphere A.space × (Ω × (Fin (ell*(d/16)) → Vector d)),
      ((L z.2.1).suffix ((k-ell)*(d/16)) (ell*(d/16)) v).angularSuccess ε (A.point z.1) z.2.2
        ∂(sphereLaw A.space).prod (ρ.prod (Fixed.rowsLaw (Vector d) (ell*(d/16)))))
      ≤ ENNReal.ofReal (((16 * ((1000 : ℝ)^32)^ell * ε)/A.radius)^(2*(d/32)))

end SubsphereCurrent.Affine
end

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereRegression
section
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ
end
section
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def ambientSphereLaw : Measure E := (sphereLaw (E := E)).map Subtype.val
end
end SubsphereRegression
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Orthogonal (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  unitary (E →L[ℝ] E)

instance orthogonal_compact : CompactSpace (Orthogonal E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [Metric.mem_closedBall,dist_zero_right]
  apply u.opNorm_le_bound (by norm_num)
  intro x
  simp only [u.norm_map_of_mem_unitary hu,one_mul,le_refl]

noncomputable def orthogonalLaw : Measure (Orthogonal E) :=
  Measure.haarMeasure ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
end SubsphereCurrent.Mixture
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def blockIso (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) : E ≃ₗᵢ[ℝ] E :=
  (V.orthogonalDecomposition.trans
    ((Unitary.linearIsometryEquiv u).withLpProdCongr 2 (Unitary.linearIsometryEquiv w))).trans
      V.orthogonalDecomposition.symm
end SubsphereCurrent.Mixture
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def directionLaw (V N : Submodule ℝ E) : Measure E :=
  ((orthogonalLaw (E := Vᗮ)).prod (SubsphereRegression.ambientSphereLaw (E := N))).map
    (fun z => blockIso V 1 z.1 (z.2 : E))

def directionJointLaw (V N : Submodule ℝ E) (t : ℕ) : Measure (Fin t → E) :=
  ((orthogonalLaw (E := Vᗮ)).prod
    (Measure.pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw (E := N)))).map
      (fun z i => blockIso V 1 z.1 (z.2 i : E))

def latitudeSpace (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) : Submodule ℝ E :=
  (ℝ ∙ (e.val : E))ᗮ

def latitudeLaw (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) (a delta : ℝ) : Measure E :=
  ((betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := latitudeSpace V e)))).map
      (fun z => blockIso V z.2.1 1
        (Real.sqrt (1-z.1) • (e.val : E) + Real.sqrt z.1 • (z.2.2 : E)))

def MixtureEstimate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Prop :=
  (∀ (V N : Submodule ℝ E), V ≤ N → 1 ≤ Module.finrank ℝ V →
    Module.finrank ℝ V < Module.finrank ℝ N → Module.finrank ℝ N < Module.finrank ℝ E →
    ∀ e : Metric.sphere (0 : V) 1,
    directionLaw V N ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E •
      (SubsphereRegression.ambientSphereLaw + latitudeLaw V e
        (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        (((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ N : ℝ))/2))) ∧
  (∀ N : Submodule ℝ E, 1 ≤ Module.finrank ℝ N →
    directionLaw ⊥ N = SubsphereRegression.ambientSphereLaw) ∧
  (∀ (V : Submodule ℝ E) (t : ℕ), 1 ≤ Module.finrank ℝ E →
    directionJointLaw V ⊤ t =
      Measure.pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw))

end SubsphereCurrent.Mixture
end

noncomputable section
universe u v w
namespace SubsphereCurrent

def CurrentMainScope : Prop :=
  ExplicitPrecision.{u} ∧
  Weighted.RadiusWeightedFullEstimate.{v} ∧
  HalfPrecision.{u} ∧
  Affine.AllAffineFullEstimate.{u,v} ∧
  Fixed.DimensionEstimate.{u} ∧
  (∀ (E : Type w) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E], Mixture.MixtureEstimate E)

end SubsphereCurrent
end

noncomputable section
universe u v w
namespace SubsphereCurrent



end SubsphereCurrent
end
end OAI


