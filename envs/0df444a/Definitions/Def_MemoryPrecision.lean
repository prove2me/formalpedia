-- Prove2me | Definitions.Def_MemoryPrecision
-- name    : MemoryPrecision
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.02443+00:00
-- url     : https://prove2.me/theorems/7ecceab3-487e-44fe-9846-5b1c614999a2
-- statement:
--   This file formalizes a memory-bounded learning model on the unit sphere S^{d-1} and a chain of density and block estimates that bound its success. In the kernel model, a Policy with M bits of memory has 2^M states and actions pairing a Boolean stop flag with a next state; it consists of a probability distribution on initial actions, time-dependent transition distributions that read an observation (a vector a in R^d together with a real label) and output a probability measure on the sphere for each time and state. A recursive evaluation sums over actions, weighting by transition probabilities and either stopping (applying a weight function) or continuing on the tail of the observations. For a hidden point s on the sphere and T Gaussian rows A_i, the records are the pairs (A_i, <s,A_i>), so labels are noiseless linear measurements. The experiment evaluates a policy path on these records and averages a test function of (s, output) over the policy's output law. Success(ε) is the probability, under a prior π on s, a probability measure ρ on a randomization parameter, and Gaussian rows, that the output lies within angle ε of s; ChordSuccess(ε) uses Euclidean distance at most ε instead. Admissible means almost every policy is measurable in the observation and the experiment of every measurable [0,1]-valued test is almost-everywhere measurable; ModelAdmissible requires this for every probability prior. Auxiliary objects include the uniform sphere measure, a Gaussian-times-Lebesgue reference measure on matrices and labels, the law of (rows, projections of a random signal drawn from μ), the ellipsoid of labels reachable from a signal within distance R of z, an ambient ball bound μ(B(x,r)) ≤ H r^β, the coefficient J(β,m,j) = 1 + 3^j 2^β m/(β-j-m), the norm scale (2π)^{-m(p-1)/(2p)} H R^{β-m(1-1/p)} (∏_{j<p-1} J)^{1/p}, a Gaussian-regularized density with its pointwise limit, a radial mixture representation of the Gaussian kernel, a sphere-local ball bound, weighted block averages, and a cube of side 1 in R^{d/2} embedded in the sphere via u ↦ (d/2)^{-1/2}·(u, sqrt(1-u_i²)), with a local-measure condition and the induced cube prior. The file then defines, as propositions rather than established theorems, several statements: AmbientGramStatement (affine-subspace small-ball and inverse-distance integral bounds, almost sure linear independence, an integral bound on the inverse Gram determinant, plus explicit dimension-dependent constants for p = d/8); FiniteDensityStatement (the projection law has an L^p density, supported in the ellipsoid, with norm at most the norm scale); MeasurableTestStatement (the projection law satisfies η(E) ≤ B ν(E)^{1-1/p} and a corresponding bound for measurable [0,1]-valued tests); JointL1Statement (for μ absolutely continuous with respect to the uniform sphere, regularized densities converge in L^1 to any density and the L^p bound holds); PointwiseDensityStatement and its properties, RadialMixtureRepresentation and FullRankDensityFormula; CoefficientStepStatement and CubeBlockStatement (block averages of sphere-local, respectively cube-local, functions remain local with constant multiplied by C^d N^{1/(d/8)}, resp. C^{d/2} N^{1/((d/2)/4)}); and SourceEllipsoidStatement, which asserts constants C, C₀ ≥ 1 such that for d ≥ 16, 0<ε≤1/10 and every admissible policy family under the uniform sphere prior, Success is at most min(1, 4^d ε^{(d-1)/2} (C^d ((d/8+2)2^M)^{1/(d/8)})^{⌈T/(d/8)⌉}), ChordSuccess has an analogous bound with C₀^d ε^{d/2-1}, and angular closeness implies chordal closeness.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MemoryPrecision.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MemoryPrecision.lean; bytes 16..40195
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

namespace MemoryPrecision.Kernel

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1

abbrev State (M : ℕ) := Fin (2^M)

abbrev Action (M : ℕ) := Bool × State M

abbrev Observations (d k : ℕ) := Fin k → (Vector d × ℝ)

abbrev Rows (d k : ℕ) := Fin k → Vector d

def UniformSphere (d : ℕ) : Measure (Sphere d) :=
  let euclideanGroup : NormedAddCommGroup (Vector d) :=
    PiLp.normedAddCommGroup
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
      (fun _ : Fin d => ℝ)
  let euclideanInner := PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)
  let σ := @Measure.toSphere (Vector d) euclideanGroup
    (@InnerProductSpace.toNormedSpace ℝ (Vector d) _
      euclideanGroup.toSeminormedAddCommGroup euclideanInner) inferInstance
    (@volume (Vector d) (@measureSpaceOfInnerProductSpace (Vector d)
      euclideanGroup euclideanInner inferInstance inferInstance inferInstance))
  (σ Set.univ)⁻¹ • σ

def RowLaw (d k : ℕ) : @Measure (Rows d k)
    (@MeasurableSpace.pi (Fin k) (fun _ => Vector d)
      (fun _ => @WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
        (Fin d → ℝ) inferInstance)) :=
  let euclideanMeasurable := @WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
    (Fin d → ℝ) inferInstance
  @Measure.pi (Fin k) (fun _ => Vector d) inferInstance (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Vector d)
    (PiLp.normedAddCommGroup
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
      (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)) inferInstance euclideanMeasurable)

def ObservationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

structure Policy (d M T : ℕ) where
  initial : Action M → ℝ≥0∞
  initial_sum : ∑ a, initial a = 1
  transition : ℕ → State M → (Vector d × ℝ) → Action M → ℝ≥0∞
  transition_sum : ∀ t j obs, ∑ a, transition t j obs a = 1
  output : ℕ → State M → Measure (Sphere d)
  output_probability : ∀ t j, IsProbabilityMeasure (output t j)

namespace Policy

def Completed {d M T : ℕ} (K : Policy d M T) : Prop :=
  ∀ t j a, AEMeasurable (fun obs => K.transition t j obs a) (ObservationReference d)

def eval {d M T : ℕ} {X : Type*} (K : Policy d M T)
    (w : ℕ → State M → X → ℝ≥0∞) (n : ℕ) :
    (k : ℕ) → State M → X → Observations d k → ℝ≥0∞
  | 0, j, s, _ => w n j s
  | k+1, j, s, obs => ∑ a : Action M, K.transition (n+1) j (obs 0) a *
      if a.1 then w (n+1) a.2 s else K.eval w (n+1) k a.2 s (Fin.tail obs)

def pathValue {d M T : ℕ} {X : Type*} (K : Policy d M T)
    (w : ℕ → State M → X → ℝ≥0∞) (s : X) (obs : Observations d T) : ℝ≥0∞ :=
  ∑ a : Action M, K.initial a * if a.1 then w 0 a.2 s else K.eval w 0 T a.2 s obs

def records {d T : ℕ} (s : Sphere d) (A : Rows d T) : Observations d T :=
  fun index => (A index, @inner ℝ (EuclideanSpace ℝ (Fin d))
    (@InnerProductSpace.toInner ℝ (EuclideanSpace ℝ (Fin d)) _
      (PiLp.seminormedAddCommGroup
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
        (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))) s.val (A index))

def outputTest {d M T : ℕ} (K : Policy d M T) (f : Sphere d × Sphere d → ℝ≥0∞)
    (t : ℕ) (j : State M) (s : Sphere d) : ℝ≥0∞ :=
  ∫⁻ v, f (s,v) ∂K.output t j

def angleTest {d : ℕ} (ε : ℝ)
    (point : MemoryPrecision.Kernel.Sphere d × MemoryPrecision.Kernel.Sphere d) : ℝ≥0∞ :=
  @ite ℝ≥0∞ (Real.arccos (@inner ℝ (EuclideanSpace ℝ (Fin d))
      (@InnerProductSpace.toInner ℝ (EuclideanSpace ℝ (Fin d)) _
        (PiLp.seminormedAddCommGroup
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
          (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      point.2.val point.1.val) ≤ ε) (Classical.propDecidable _) 1 0

def chordTest {d : ℕ} (ε : ℝ) (x : Sphere d × Sphere d) : ℝ≥0∞ :=
  {x : Sphere d × Sphere d | dist x.2.val x.1.val ≤ ε}.indicator (fun _ => 1) x

def experiment {d M T : ℕ} {Ω : Type u} (K : Ω → Policy d M T)
    (f : Sphere d × Sphere d → ℝ≥0∞) (z : Sphere d × (Ω × Rows d T)) : ℝ≥0∞ :=
  (K z.2.1).pathValue ((K z.2.1).outputTest f) z.1 (records z.1 z.2.2)

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) : Prop where
  completed : ∀ᵐ ω ∂ρ, (K ω).Completed
  experiment : ∀ f : Sphere d × Sphere d → ℝ≥0∞, Measurable f →
    (∀ x, f x ≤ 1) → AEMeasurable (experiment K f) (π.prod (ρ.prod (RowLaw d T)))

def Success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, experiment K (angleTest ε) z ∂π.prod (ρ.prod (RowLaw d T))

def ChordSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, experiment K (chordTest ε) z ∂π.prod (ρ.prod (RowLaw d T))

end Policy
end MemoryPrecision.Kernel

namespace NoiselessRegression
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
end NoiselessRegression

namespace MemoryPrecision
open NoiselessRegression

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def J (β : ℝ) (m j : ℕ) : ℝ :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let three : ℝ := @OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))
  1 + three^j * two^β * (m : ℝ) / (β - (j : ℝ) - (m : ℝ))

def AmbientBallBound {d : ℕ} (μ : Measure (Space d)) (H β : ℝ) : Prop :=
  ∀ x : Space d, ∀ r : ℝ, 0 < r →
    μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H * r^β)

def InverseGram {d p : ℕ} (m : ℕ) (v : Space d × (Fin (p-1) → Space d)) : ℝ≥0∞ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  letI : AddCommGroup (Space d) := WithLp.instAddCommGroup exponent (Fin d → ℝ)
  letI : Inner ℝ (Space d) := @InnerProductSpace.toInner ℝ (Space d) _
    (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
  ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ (fun i => v.2 i - v.1)).det)⁻¹ ^ m)

def MatrixLabelReference (d m : ℕ) : @Measure ((Fin m → Space d) × (Fin m → ℝ))
    (@MeasurableSpace.prod (Fin m → Space d) (Fin m → ℝ)
      (@MeasurableSpace.pi (Fin m) (fun _ => Space d)
        (fun _ => WithLp.measurableSpace
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
      inferInstance) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := WithLp.measurableSpace exponent (Fin d → ℝ)
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  let rowLaw := @Measure.pi (Fin m) (fun _ => Space d) inferInstance
    (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Space d)
      (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
      inferInstance euclideanMeasurable)
  @Measure.prod _ _ rowMeasurable inferInstance rowLaw volume

def ProjectionLaw {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) : @Measure ((Fin m → Space d) × (Fin m → ℝ))
      (@MeasurableSpace.prod (Fin m → Space d) (Fin m → ℝ)
        (@MeasurableSpace.pi (Fin m) (fun _ => Space d)
          (fun _ => WithLp.measurableSpace
            (@OfNat.ofNat ℝ≥0∞ 2
              (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
                (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
        inferInstance) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := WithLp.measurableSpace exponent (Fin d → ℝ)
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  let rowLaw := @Measure.pi (Fin m) (fun _ => Space d) inferInstance
    (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Space d)
      (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
      inferInstance euclideanMeasurable)
  @Measure.map ((Fin m → Space d) × Space d) ((Fin m → Space d) × (Fin m → ℝ))
    (@MeasurableSpace.prod _ _ rowMeasurable euclideanMeasurable)
    (@MeasurableSpace.prod _ _ rowMeasurable inferInstance)
    (fun pair => (pair.1, fun index => @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      pair.2 (pair.1 index)))
    (@Measure.prod _ _ rowMeasurable euclideanMeasurable rowLaw μ)

def ProjectedEllipsoid {d m : ℕ} (z : Space d) (R : ℝ) :
    Set ((Fin m → Space d) × (Fin m → ℝ)) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanInner := @InnerProductSpace.toInner ℝ (Space d) _
    (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
  {pair | ∃ displacement ∈ @Metric.closedBall (Space d)
      (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.toLp exponent (fun _ => (0 : ℝ))) R,
    pair.2 = fun index => @inner ℝ (Space d) euclideanInner z (pair.1 index) +
      @inner ℝ (Space d) euclideanInner displacement (pair.1 index)}

def ProjectionNormScale (m p : ℕ) (H β R : ℝ) : ℝ :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  (two * Real.pi) ^ (-(m : ℝ) * ((p : ℝ)-1) / (two*(p : ℝ))) * H *
    R ^ (β - (m : ℝ)*(1-1/(p : ℝ))) *
    (∏ j ∈ Finset.range (p-1), J β m j) ^ (1/(p : ℝ))

def UniformSphere (d : ℕ) : @Measure (Space d)
    (WithLp.measurableSpace
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)) :=
  let euclideanMeasurable := WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
        (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)
  @Measure.map (Kernel.Sphere d) (Space d)
    (MeasurableSpace.comap Subtype.val euclideanMeasurable) euclideanMeasurable
    Subtype.val (Kernel.UniformSphere d)

def GaussianRegularization {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) (δ : ℝ)
    (Ay : (Fin m → Space d) × (Fin m → ℝ)) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  ∫ signal, ∏ index, gaussianPDFReal 0 ⟨δ^2, sq_nonneg δ⟩
    (Ay.2 index - @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      signal (Ay.1 index)) ∂μ

def PointwiseDensity {d : ℕ} (μ : Measure (Space d)) (m : ℕ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) : ℝ := by
  classical
  exact if h : ∃ l : ℝ, Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x)
      atTop (𝓝 l) then Classical.choose h else 0

lemma space_finiteDimensional (d : ℕ) : FiniteDimensional ℝ (Space d) := by
  infer_instance

def UnitBallVolume (m : ℕ) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanGroup := PiLp.normedAddCommGroup exponent (fun _ : Fin m => ℝ)
  letI : MeasurableSpace (Space m) := WithLp.measurableSpace exponent (Fin m → ℝ)
  let euclideanVolume := @volume (Space m) (@measureSpaceOfInnerProductSpace (Space m)
    euclideanGroup (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin m => ℝ))
    (space_finiteDimensional m) inferInstance inferInstance)
  (euclideanVolume (@Metric.ball (Space m)
    (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin m => ℝ))
    (WithLp.toLp exponent (fun _ : Fin m => (0 : ℝ))) 1)).toReal

def CoordinateUnit (m : ℕ) : Space m :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  WithLp.toLp exponent (fun j : Fin m => if (j:ℕ) = 0 then (1:ℝ) else 0)

lemma gaussianVariance_nonneg (δ : ℝ) : 0 ≤ δ^2 := sq_nonneg δ

def GaussianKernel (m : ℕ) (δ : ℝ) (y : Space m) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∏ index, gaussianPDFReal 0 ⟨δ^2, gaussianVariance_nonneg δ⟩
    (@WithLp.ofLp exponent (Fin m → ℝ) y index)

def RadialMixture (m : ℕ) (δ r : ℝ) : ℝ :=
  UnitBallVolume m * r^m * (r / δ^2) * GaussianKernel m δ (r • CoordinateUnit m)

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Space d) 1

def SpherePrior (d : ℕ) : Measure (Sphere d) :=
  MemoryPrecision.Kernel.UniformSphere d

def SphereBallBound {d : ℕ} (h : Sphere d → ℝ≥0∞) (H α : ℝ) : Prop :=
  ∀ z : Space d, ∀ r : ℝ, 0 < r →
    (∫⁻ s in {s : Sphere d | dist s.val z ≤ r}, h s ∂SpherePrior d) ≤
      ENNReal.ofReal (H * r^α)

section WeightedImage
variable {X : Type*} [MeasurableSpace X] {d m N : ℕ}

def WeightedBlock (ι : X → Space d) (h : Fin N → X → ℝ≥0∞)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := @WithLp.measurableSpace exponent (Fin d → ℝ) inferInstance
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  @MeasureTheory.lintegral (Fin m → Space d) rowMeasurable
    (@Measure.pi (Fin m) (fun _ => Space d) inferInstance (fun _ => euclideanMeasurable)
      (fun _ => @stdGaussian (Space d)
        (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
        (space_finiteDimensional d) euclideanMeasurable))
    (fun rows => ∑ state, g state (rows, fun index => @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      (ι x) (rows index)) * h state x)

end WeightedImage

def SphereBlock {d m N : ℕ} (h : Fin N → Sphere d → ℝ≥0∞)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞)
    (s : Sphere d) : ℝ≥0∞ :=
  WeightedBlock Subtype.val h g s

abbrev CubeSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  fun (point : EuclideanSpace ℝ (Fin n)) => ∀ index : Fin n,
    @LE.le ℝ Real.instLE
      (@abs ℝ Real.lattice Real.instAddGroup
        (@WithLp.ofLp
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
          (Fin n → ℝ) point index))
      (@HDiv.hDiv ℝ ℝ ℝ (@instHDiv ℝ Real.instDivInvMonoid.toDiv)
        (@OfNat.ofNat ℝ 1 (@One.toOfNat1 ℝ Real.instOne))
        (@OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))))

abbrev Cube (d : ℕ) := CubeSet (d/2)

def CubeLaw (d : ℕ) : Measure (Cube d) :=
  (volume : Measure (Space (d/2))).comap Subtype.val

lemma cube_second_coordinate_lt (d : ℕ) (index : Fin d)
    (lower : ¬index.val < d/2) (upper : index.val < 2*(d/2)) :
    index.val - d/2 < d/2 := by omega

def cubeRaw (d : ℕ) (u : Space (d/2)) : Space d :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  @HSMul.hSMul ℝ (Space d) (Space d)
    (@instHSMul ℝ (Space d) (WithLp.instSMul exponent ℝ (Fin d → ℝ)))
    (Real.sqrt (d/2:ℕ))⁻¹ (WithLp.toLp exponent (fun index : Fin d =>
      if lower : index.val < d/2 then
        @WithLp.ofLp exponent (Fin (d/2) → ℝ) u ⟨index.val, lower⟩
      else if upper : index.val < 2*(d/2) then
        Real.sqrt (1-(@WithLp.ofLp exponent (Fin (d/2) → ℝ) u
          ⟨index.val-d/2, cube_second_coordinate_lt d index lower upper⟩)^2)
      else 0))

def CubeEmbedding (d : ℕ) (u : Cube d) : Space d := cubeRaw d u.val

def CubeBall (d : ℕ) (z : Space (d/2)) (r : ℝ) : Set (Cube d) :=
  {u | dist u.val z ≤ Real.sqrt (d/2:ℕ) * r}

def CubeLocal {d : ℕ} (f : Cube d → ℝ≥0∞) (L : ℝ) : Prop :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let cubeMeasurable := @Subtype.instMeasurableSpace (Space (d/2)) (CubeSet (d/2))
    (@WithLp.measurableSpace exponent (Fin (d/2) → ℝ) inferInstance)
  ∀ z : Space (d/2), ∀ r : ℝ, 0 < r →
    @MeasureTheory.lintegral (Cube d) cubeMeasurable
      (@Measure.restrict (Cube d) cubeMeasurable (CubeLaw d) (CubeBall d z r)) f ≤
      ENNReal.ofReal (L * r^(
        (@OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))) * (d/2:ℕ) /
        (@OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))) : ℝ))

/-- Every coordinate of the paired cube has square at most one quarter. -/

lemma cube_coordinate_square_le {d : ℕ} (u : Cube d) (i : Fin (d/2)) : u.val i^2 ≤ 1/4 := by
  have hu : -(1/2 : ℝ) ≤ u.val i ∧ u.val i ≤ 1/2 := abs_le.mp (u.property i)
  nlinarith [sq_nonneg (u.val i-1/2), sq_nonneg (u.val i+1/2)]

lemma sum_fin_split {n d : ℕ} (hn : n ≤ d) (f : Fin d → ℝ) :
    (∑ i, f i) = (∑ i : Fin n, f ⟨i.val,by omega⟩) +
      ∑ i : Fin (d-n), f ⟨n+i.val,by omega⟩ := by
  let e : Fin (n+(d-n)) ≃ Fin d := finCongr (Nat.add_sub_of_le hn)
  calc
    _ = ∑ i : Fin (n+(d-n)), f (e i) := (Equiv.sum_comp e f).symm
    _ = _ := by rw [Fin.sum_univ_add]; rfl

def cubeCoords (d : ℕ) (u : Space (d/2)) : Space d :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  WithLp.toLp exponent (fun index : Fin d =>
    if lower : index.val < d/2 then
      @WithLp.ofLp exponent (Fin (d/2) → ℝ) u ⟨index.val, lower⟩
    else if upper : index.val < 2*(d/2) then
      Real.sqrt (1-(@WithLp.ofLp exponent (Fin (d/2) → ℝ) u
        ⟨index.val-d/2, cube_second_coordinate_lt d index lower upper⟩)^2)
    else 0)

lemma cubeCoords_first (d : ℕ) (u : Space (d/2)) (i : Fin (d/2)) :
    cubeCoords d u ⟨i.val,by omega⟩ = u i := by
  simp [cubeCoords, i.isLt]

lemma cubeCoords_second (d : ℕ) (u : Space (d/2)) (i : Fin (d/2)) :
    cubeCoords d u ⟨d/2+i.val,by omega⟩ = Real.sqrt (1-u i^2) := by
  simp [cubeCoords, show ¬d/2+i.val < d/2 by omega, show d/2+i.val < 2*(d/2) by omega]

lemma cubeCoords_tail (d : ℕ) (u : Space (d/2)) (i : Fin d) (hi : 2*(d/2) ≤ i.val) :
    cubeCoords d u i = 0 := by
  simp [cubeCoords, show ¬i.val < d/2 by omega, show ¬i.val < 2*(d/2) by omega]

lemma cubeCoords_sum (d : ℕ) (u : Space (d/2)) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ i : Fin d, f (cubeCoords d u i)) =
      (∑ i : Fin (d/2), f (u i)) + ∑ i : Fin (d/2), f (Real.sqrt (1-u i^2)) := by
  rw [sum_fin_split (show d/2 ≤ d by omega)]
  simp_rw [cubeCoords_first]
  rw [sum_fin_split (show d/2 ≤ d-d/2 by omega)]
  congr 1
  have h1 : (∑ i : Fin (d/2), f (cubeCoords d u ⟨d/2+i.val,by omega⟩)) =
      ∑ i : Fin (d/2), f (Real.sqrt (1-u i^2)) := by simp_rw [cubeCoords_second]
  rw [h1]
  have h0 : (∑ i : Fin (d-d/2-d/2), f (cubeCoords d u ⟨d/2+(d/2+i.val),by omega⟩)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [cubeCoords_tail d u _ (show 2*(d/2) ≤ d/2+(d/2+i.val) by omega), hf]
  rw [h0, add_zero]

lemma cubeEmbedding_norm {d : ℕ} (hd : 2 ≤ d) (u : Cube d) :
    @Norm.norm (Space d) (PiLp.instNorm
      (p := @OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (β := fun _ : Fin d => ℝ))
      (CubeEmbedding d u) = (1 : ℝ) := by
  have hs : ‖cubeCoords d u.val‖^2 = (d/2:ℕ) := by
    rw [EuclideanSpace.real_norm_sq_eq, cubeCoords_sum d u.val (fun x => x^2) (by norm_num)]
    have he (i : Fin (d/2)) : Real.sqrt (1-u.val i^2)^2 = 1-u.val i^2 :=
      Real.sq_sqrt (by have := cube_coordinate_square_le u i; linarith)
    simp_rw [he]
    rw [← Finset.sum_add_distrib]
    simp
  have hn : 0 < (d/2:ℕ) := by omega
  have hr : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnorm : ‖cubeCoords d u.val‖ = Real.sqrt (d/2:ℕ) := by
    rw [← Real.sqrt_sq (norm_nonneg _), hs]
  change ‖(Real.sqrt (d/2:ℕ))⁻¹ • cubeCoords d u.val‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hnorm, inv_mul_cancel₀ hr.ne']

def CubeSphere {d : ℕ} (hd : 2 ≤ d) (u : Cube d) : UnitSphere d :=
  ⟨CubeEmbedding d u, by simpa [Metric.mem_sphere, dist_zero_right] using cubeEmbedding_norm hd u⟩

def AmbientGramStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let three : ℝ := @OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))
  let four : ℝ := @OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  (∀ (d m p : ℕ),
    letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
    letI : PseudoMetricSpace (Space d) :=
      PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)
    letI : AddCommGroup (Space d) := WithLp.instAddCommGroup exponent (Fin d → ℝ)
    letI : Module ℝ (Space d) := WithLp.instModule (p := exponent) (K := ℝ) (V := Fin d → ℝ)
    1 ≤ d → 1 ≤ m → 2 ≤ p →
    ∀ β R H : ℝ, (m : ℝ) + (p : ℝ) - two < β → 0 < R → 0 < H →
    ∀ (μ : Measure (Space d)), IsFiniteMeasure μ →
    ∀ z : Space d, μ.support ⊆ Metric.closedBall z R →
    AmbientBallBound μ H β →
    (∀ (j : ℕ), j ≤ p-2 → ∀ L : AffineSubspace ℝ (Space d),
      Nonempty L → Module.finrank ℝ L.direction = j →
      (∀ t : ℝ, 0 < t → t ≤ R →
        μ {s | Metric.infDist s L ≤ t} ≤
          ENNReal.ofReal (three^j * two^β * H * R^j * t^(β-(j:ℝ)))) ∧
      (∫⁻ s, (ENNReal.ofReal (Metric.infDist s L)) ^ (-(m:ℝ)) ∂μ) ≤
        ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) ∧
    (∀ᵐ v : Space d × (Fin (p-1) → Space d)
      ∂μ.prod (Measure.pi (fun _ : Fin (p-1) => μ)),
      LinearIndependent ℝ (fun i => v.2 i - v.1)) ∧
    (∫⁻ v : Space d × (Fin (p-1) → Space d), InverseGram m v
      ∂μ.prod (Measure.pi (fun _ : Fin (p-1) => μ))) ≤
      ENNReal.ofReal (H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) *
        ∏ j : Fin (p-1), J β m j)) ∧
  (∃ C : ℝ, 1 ≤ C ∧ ∀ (d m p : ℕ), 16 ≤ d → p = d/8 →
    1 ≤ m → m ≤ p → ∀ β : ℝ, ((d:ℝ)-1)/two ≤ β → β ≤ (d:ℝ)/two →
    (∀ j : ℕ, j ≤ p-2 →
      ((d:ℝ)-1)/two - two*(p:ℝ) + two ≤ β-(j:ℝ)-(m:ℝ) ∧
      (d:ℝ)/four + three/two ≤ ((d:ℝ)-1)/two - two*(p:ℝ) + two ∧
      J β m j ≤ C^d) ∧
    (∀ H R : ℝ, 0 < H → 0 < R →
      H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) * (∏ j : Fin (p-1), J β m j) ≤
        C^(d*(p-1)) * H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ))))

def FiniteDensityStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  1 ≤ d → 1 ≤ m → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    ∃ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
      Measurable F ∧ (∀ x, 0 ≤ F x) ∧
      (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
        ProjectionLaw μ m ∧
      (∀ᵐ x ∂MatrixLabelReference d m, x ∉ ProjectedEllipsoid z R → F x = 0) ∧
      eLpNorm F (p : ℝ≥0∞) (MatrixLabelReference d m) ≤
        ENNReal.ofReal (ProjectionNormScale m p H β R)

def MeasurableTestStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  1 ≤ d → 1 ≤ m → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    let ν := MatrixLabelReference d m
    let η := ProjectionLaw μ m
    let B := ENNReal.ofReal (ProjectionNormScale m p H β R)
    let α := 1-1/(p:ℝ)
    (∀ E, MeasurableSet E → ν E ≠ ∞ → η E ≤ B * (ν E)^α) ∧
    η ≪ ν ∧
    ∃ ηc : Measure (NullMeasurableSpace ((Fin m → Space d) × (Fin m → ℝ)) ν),
      (∀ E, NullMeasurableSet E ν → ηc E = η E) ∧
      (∀ E, NullMeasurableSet E ν → ν.completion E ≠ ∞ →
        ηc E ≤ B * (ν.completion E)^α) ∧
      (∀ φ : NullMeasurableSpace ((Fin m → Space d) × (Fin m → ℝ)) ν → ℝ≥0∞,
        Measurable φ → (∀ x, φ x ≤ 1) →
        (∫⁻ x, φ x ∂ηc) ≤ B * (∫⁻ x in ProjectedEllipsoid z R, φ x ∂ν.completion)^α)

def JointL1Statement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  2 ≤ d → 1 ≤ m → m < d → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    μ ≪ UniformSphere d →
  ∀ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
    Measurable F → (∀ x, 0 ≤ F x) →
    (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m →
    Tendsto (fun δ => eLpNorm (fun Ay => GaussianRegularization μ m δ Ay - F Ay)
      1 (MatrixLabelReference d m)) (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    eLpNorm F (p : ℝ≥0∞) (MatrixLabelReference d m) ≤
      ENNReal.ofReal (ProjectionNormScale m p H β R)

def RadialMixtureRepresentation (m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    (∀ r : ℝ, 0 < r → 0 ≤ RadialMixture m δ r) ∧
    Measurable (RadialMixture m δ) ∧
    (∫ r in Set.Ioi 0, RadialMixture m δ r) = 1 ∧
    (∀ y : Space m, GaussianKernel m δ y =
      ∫ r in Set.Ioi ‖y‖, RadialMixture m δ r / (UnitBallVolume m * r^m))

def FullRankDensityFormula {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) : Prop :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ A : Fin m → Space d,
    @LinearIndependent (Fin m) ℝ (Space d) A Real.commRing.toSemiring
      (WithLp.instAddCommGroup exponent (Fin d → ℝ)).toAddCommMonoid
      (WithLp.instModule (p := exponent) (K := ℝ) (V := Fin d → ℝ)) →
    (volume : Measure (Fin m → ℝ)).withDensity
      (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =
      @Measure.map (Space d) (Fin m → ℝ)
        (WithLp.measurableSpace exponent (Fin d → ℝ)) inferInstance
        (fun signal => fun index => @inner ℝ (Space d)
          (@InnerProductSpace.toInner ℝ (Space d) _
            (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
            (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
          signal (A index)) μ

def PointwiseDensityProperties {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m p : ℕ) (H β R : ℝ) : Prop :=
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
        (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)
  let reference : Measure ((Fin m → Space d) × (Fin m → ℝ)) := MatrixLabelReference d m
  RadialMixtureRepresentation m ∧
  (∀ x, 0 ≤ PointwiseDensity μ m x) ∧
  Measurable (PointwiseDensity μ m) ∧
  FullRankDensityFormula μ m ∧
  reference.withDensity (fun x => ENNReal.ofReal (PointwiseDensity μ m x)) =
    ProjectionLaw μ m ∧
  (∀ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
    Measurable F → (∀ x, 0 ≤ F x) →
    reference.withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m → PointwiseDensity μ m =ᵐ[reference] F) ∧
  (∫⁻ x, ENNReal.ofReal (PointwiseDensity μ m x)^p ∂reference) ≤
    ENNReal.ofReal (ProjectionNormScale m p H β R)^p

def PointwiseDensityStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ, 2 ≤ d → 1 ≤ m → m < d → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d,
  ∀ μ : @Measure (Space d) (WithLp.measurableSpace exponent (Fin d → ℝ)),
    IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    μ ≪ UniformSphere d → PointwiseDensityProperties μ m p H β R

def CoefficientStepStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∃ C : ℝ, 1 ≤ C ∧ ∀ d m N : ℕ, 16 ≤ d →
    1 ≤ m → m ≤ d/8 → 1 ≤ N →
    ∀ α H : ℝ, ((d:ℝ)-1)/two ≤ α → α ≤ (d:ℝ)/two → 0 < H →
    ∀ h : Fin N → Sphere d → ℝ≥0∞,
      (∀ w, Measurable (h w)) → (∀ w s, h w s ≤ 1) →
      (∀ w, SphereBallBound (h w) H α) →
    ∀ g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞,
      (∀ w, Measurable (g w)) → (∀ x, ∑ w, g w x ≤ 1) →
      SphereBallBound (SphereBlock h g) (C^d * (N:ℝ)^(1/((d/8:ℕ):ℝ)) * H) α

def CubeBlockStatement : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ d k N : ℕ, 16 ≤ d → 1 ≤ k → k ≤ (d/2)/4 → 1 ≤ N →
    ∀ L : ℝ, 0 ≤ L → ∀ f : Fin N → Cube d → ℝ≥0∞,
      (∀ v, Measurable (f v)) → (∀ v u, f v u ≤ 1) → (∀ v, CubeLocal (f v) L) →
    ∀ g : Fin N → ((Fin k → Space d) × (Fin k → ℝ)) → ℝ≥0∞,
      (∀ v, Measurable (g v)) → (∀ x, ∑ v, g v x ≤ 1) →
      CubeLocal (WeightedBlock (CubeEmbedding d) f g)
        (C^(d/2) * (N:ℝ)^(1/(((d/2)/4:ℕ):ℝ)) * L)

end MemoryPrecision

namespace MemoryPrecision.Kernel
namespace Policy

def ModelAdmissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) : Prop :=
  ∀ π : Measure (Sphere d), IsProbabilityMeasure π → Admissible K ρ π

end Policy

open MemoryPrecision NoiselessRegression Policy

def CubePrior {d : ℕ} (hd : 2 ≤ d) : Measure (MemoryPrecision.Kernel.Sphere d) :=
  (CubeLaw d).map (CubeSphere hd)

def BlockCount (T p : ℕ) : ℕ := ⌈(T:ℝ)/(p:ℝ)⌉₊

def SourceEllipsoidStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let four : ℝ := @OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))
  let ten : ℝ := @OfNat.ofNat ℝ 10 (@instOfNatAtLeastTwo ℝ 10 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 8)))
  ∃ C C₀ : ℝ, 1 ≤ C ∧ 1 ≤ C₀ ∧
  ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/ten →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ K : Ω → Policy d M T, Policy.Admissible K ρ (UniformSphere d) →
    Policy.Success K ρ (UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      (four^d * ε^(((d:ℝ)-1)/two) *
        (C^d * (((d/8+2)*2^M : ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^(BlockCount T (d/8)))) ∧
    Policy.ChordSuccess K ρ (UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      (C₀^d * ε^((d:ℝ)/two-1) *
        (C^d * (((2*(d/8)+4)*2^M : ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^(BlockCount T (d/8)))) ∧
    {x : Sphere d × Sphere d | Real.arccos (@inner ℝ (Vector d)
      (@InnerProductSpace.toInner ℝ (Vector d) _
        (PiLp.seminormedAddCommGroup
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
          (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      x.2.val x.1.val) ≤ ε} ⊆
    {x | @Dist.dist (Vector d)
      (PiLp.instDist (p := @OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
        (α := fun _ : Fin d => ℝ)) x.2.val x.1.val ≤ ε}

lemma cubePrior_dimension {d₀ d : ℕ} (hd₀ : 16 ≤ d₀) (hd : d₀ ≤ d) : 2 ≤ d :=
  Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_trans hd₀ hd)

end MemoryPrecision.Kernel

namespace MemoryPrecision



end MemoryPrecision
end
end OAI


