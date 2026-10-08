-- Prove2me | Definitions.Def_PerceptronFreeEnergy
-- name    : PerceptronFreeEnergy
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:24.669451+00:00
-- url     : https://prove2.me/theorems/53faee5c-5207-4327-be20-893e98067b38
-- statement:
--   For real parameters α (pattern density) and N spins, the file sets up a spherical perceptron free-energy problem. Spin configurations live in ℝ^N; the number of patterns is ⌊αN⌋, and a pattern array is a ⌊αN⌋×N matrix of independent standard Gaussian entries (patternLaw, a product measure). The spin reference measure sphereLaw is the normalized uniform surface measure on the unit sphere in ℝ^N, rescaled by √N. For a pattern array g, patternField for pattern a is (Σ_i g_{a,i} x_i)/√N, and for a bounded continuous function φ the hamiltonian is the sum over patterns of φ applied to these fields. The pressure at inverse temperature β is (1/N) log of the sphereLaw integral of exp(β·hamiltonian), and expectedPressure averages it over the Gaussian patterns. The variational side uses a Trial, a monotone, measurable function m from [0,1] to [0,1]. Its tailIntegral at t is the integral of m over [t,1], and its entropy is one half of the integral over t in [0,1] of (tailIntegral(t))⁻¹ − (1−t)⁻¹, computed in extended nonnegative reals. On Brownian paths (continuous functions from ℝ≥0 to ℝ, with Borel structure), a control v is Progressive if, for each t in [0,1], (s,ω) ↦ v(s,ω) on [0,t]×paths is measurable with respect to the product of the Borel structure with the right-continuous augmented Brownian filtration at time t, formed from path evaluations up to times slightly after t together with P-null sets. Given a measure P, the controlCost of v is the expectation of ∫₀¹ m(t) v(t)² dt, and controlPayoff for a bounded continuous f is E[f(B₁ + ∫₀¹ m(t)v(t) dt)] minus half the controlCost's real part. controlValue is the supremum of payoffs over progressive controls with finite cost, and variationalValue(P,α,β,φ) is the infimum over all trials m of α·controlValue(P, βφ, m) plus the entropy of m, as an extended real. The file only defines these objects and states no theorem relating them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PerceptronFreeEnergy.lean; bytes 16..3753
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

abbrev Time := unitInterval
abbrev BrownianPath := C(ℝ≥0, ℝ)

instance : MeasurableSpace BrownianPath := borel BrownianPath
instance : BorelSpace BrownianPath := ⟨rfl⟩

abbrev Spin (N : ℕ) := EuclideanSpace ℝ (Fin N)

def patternCount (α : ℝ) (N : ℕ) : ℕ := ⌊α * (N : ℝ)⌋₊
abbrev Patterns (α : ℝ) (N : ℕ) := Fin (patternCount α N) → Fin N → ℝ

def patternLaw (α : ℝ) (N : ℕ) : Measure (Patterns α N) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

def unitSphereLaw (N : ℕ) : Measure (Metric.sphere (0 : Spin N) 1) :=
  let s := (volume : Measure (Spin N)).toSphere
  (s Set.univ)⁻¹ • s

def sphereLaw (N : ℕ) : Measure (Spin N) :=
  (unitSphereLaw N).map fun x => Real.sqrt (N : ℝ) • x.val

def patternField {α : ℝ} {N : ℕ} (g : Patterns α N)
    (a : Fin (patternCount α N)) (x : Spin N) : ℝ :=
  (∑ i : Fin N, g a i * x i) / Real.sqrt (N : ℝ)

def hamiltonian (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) (g : Patterns α N)
    (x : Spin N) : ℝ :=
  ∑ a : Fin (patternCount α N), φ (patternField g a x)

def pressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) (g : Patterns α N) : ℝ :=
  Real.log (∫ x, Real.exp (β * hamiltonian α φ N g x) ∂sphereLaw N) / (N : ℝ)

def expectedPressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) : ℝ :=
  ∫ g, pressure α β φ N g ∂patternLaw α N

structure Trial where
  toFun : Time → ℝ
  monotone : Monotone toFun
  measurable : Measurable toFun
  nonneg : ∀ t, 0 ≤ toFun t
  le_one : ∀ t, toFun t ≤ 1

instance : CoeFun Trial (fun _ => Time → ℝ) := ⟨Trial.toFun⟩

def timeLaw : Measure Time := Measure.comap Subtype.val volume

def tailIntegral (m : Trial) (t : Time) : ℝ :=
  ∫ s in Set.Ici t, m s ∂timeLaw

def entropy (m : Trial) : ℝ≥0∞ :=
  (∫⁻ t, (ENNReal.ofReal (tailIntegral m t))⁻¹ -
    (ENNReal.ofReal (1 - (t : ℝ)))⁻¹ ∂timeLaw) / 2

def brownianEval (t : ℝ≥0) (ω : BrownianPath) : ℝ := ω t

@[instance_reducible] def nullSigma (P : Measure BrownianPath) : MeasurableSpace BrownianPath :=
  MeasurableSpace.generateFrom {s | P s = 0}

@[instance_reducible] def usualBrownianSigma (P : Measure BrownianPath) (t : Time) :
    MeasurableSpace BrownianPath :=
  ⨅ s : {s : ℝ≥0 // (t : ℝ) < s},
    (⨆ r : {r : ℝ≥0 // r ≤ s.val},
      MeasurableSpace.comap (brownianEval r.val) (borel ℝ)) ⊔ nullSigma P

def Progressive (P : Measure BrownianPath) (v : Time → BrownianPath → ℝ) : Prop :=
  ∀ t : Time,
    @Measurable (Set.Iic t × BrownianPath) ℝ
      (MeasurableSpace.prod inferInstance (usualBrownianSigma P t)) (borel ℝ)
      (fun p => v p.1.val p.2)

def controlCost (P : Measure BrownianPath) (m : Trial)
    (v : Time → BrownianPath → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t, ENNReal.ofReal (m t * v t ω ^ 2) ∂timeLaw ∂P

def controlPayoff (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial)
    (v : Time → BrownianPath → ℝ) : ℝ :=
  (∫ ω, f (brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw) ∂P) -
    (controlCost P m v).toReal / 2

def controlValue (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) : ℝ :=
  sSup {a | ∃ v : Time → BrownianPath → ℝ,
    Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v}

def variationalValue (P : Measure BrownianPath) (α β : ℝ) (φ : ℝ →ᵇ ℝ) : EReal :=
  ⨅ m : Trial, ((α * controlValue P (β • φ) m : ℝ) : EReal) + (entropy m).toEReal



end SphericalPerceptronFreeEnergy
end
end OAI


