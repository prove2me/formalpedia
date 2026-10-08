-- Prove2me | Definitions.Def_SphericalField
-- name    : SphericalField
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:24.878018+00:00
-- url     : https://prove2.me/theorems/a10d5eef-3860-4645-9813-534232e24f73
-- statement:
--   Time is the unit interval [0,1] with Lebesgue measure as a probability law, and Spin(N) is N-dimensional Euclidean space with the normalized surface measure on its unit sphere. A Trial is a measurable nondecreasing function m on [0,1] with values in [0,1]; its tail integral is T(t)=∫_{s≥t} m(s)ds, and its entropy is the extended-nonnegative quantity (1/2)∫₀¹ [1/T(t) − 1/(1−t)] dt. The file builds Poisson random measures: finite Poisson laws on finite sums of point masses, countable independent mixtures of them, and, for an s-finite intensity, a Poisson random measure law, with total masses normalized. The stable log-intensity of parameter b has density b·e^{−bx} on the real line. Iterating this gives a decoratedCascade, a depth-n nested random measure on (ℝ × (marks × previous level)), with a law determined by a vector z of parameters. A kernel reweights atoms by e^{x} and normalizes, and a second kernel multiplies by the total weight times e^{−x}. Along a cascade, a terminal total and a leaf integral accumulate e^{x}-weighted integrals of a function evaluated after a state-update step. Concretely the marks are standard Gaussian vectors in each of d coordinates, and the state update shifts a sequence and adds σ_i times the mark. From these come an angular factor, which averages exp(⟨field, rθ⟩) over the unit sphere, a coordinate angular log of its ratio to the terminal total, and a normalized sphere log at radius √(n+1) divided by n+1. Its expectation under Gaussian initial data and the cascade law is expectedCoordinateSphereLog. For weights w and nondecreasing nonnegative values h on k+1 levels, with step increments √(2(h_{i+1}−h_i)) and cumulative weights, finiteSphericalFieldValue is that expectation at initial variance 2h₀ minus the last value h_k. The finite dual objective of a monotone q is the entropy of the weighted step trial Σ wᵢ·1{qᵢ≤t} minus Σ wᵢhᵢqᵢ, and the dual values range over monotone q with q_k<1. A FiniteFieldModel of f is a finitely-valued nondecreasing representation of f almost everywhere by a measurable label with positive-probability level sets; its pressure is finiteSphericalFieldValue with its weights and values. A BoundedField H is a nondecreasing function on [0,1] with values in [0,H]. It is rounded down to multiples of 1/(N+1), which gives finitely many values and hence a model, and boundedSphericalFieldValue is the limit as N→∞ of the rounded models' pressures. For a quantile function q, quantileTrial(q) has distribution function Leb{q≤t}, quantileTail(q,t)=∫(1−max(q,t)), and quantileA(q,r)=∫₀^r dt/quantileTail(q,t)². For a bounded field q with bound B<1, the stationary field is quantileA(q,q(u))/2, a bounded field with bound B/(2(1−B)²); stationaryQuantileField first clips a monotone q at B. SphericalLinearFieldFormula is a defined proposition, not an established theorem, with two parts. First, for every k and positive weights summing to 1: for each nondecreasing h with h₀≥0 the dual objective attains its minimum over the admissible monotone q, and for every compact set of such h the finite field values converge uniformly in n to the infimum of the dual values. Second, for every B in [0,1) and ε>0, eventually in n, for every monotone q with q≤B almost everywhere, the entropy of quantileTrial(q) is finite, twice the stationary field equals quantileA(q,q(u)) almost everywhere, and the bounded spherical field value of the stationary field differs from entropy(quantileTrial(q)) − ∫ field·q by less than ε.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SphericalField.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SphericalField.lean; bytes 16..25509
-- Kind: block; original declaration names preserved; body compatibility edits recorded in manifest.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

abbrev Time := unitInterval

abbrev Spin (N : ℕ) := EuclideanSpace ℝ (Fin N)

def unitSphereLaw (N : ℕ) : Measure (Metric.sphere (0 : Spin N) 1) :=
  let s := (volume : Measure (Spin N)).toSphere
  (s Set.univ)⁻¹ • s

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

@[simp] theorem timeLaw_eq_volume : timeLaw = (volume : Measure Time) := rfl

instance : IsProbabilityMeasure timeLaw := by
  rw [timeLaw_eq_volume]
  infer_instance

def finitePointMeasure {S : Type*} [MeasurableSpace S] (n : ℕ) (x : Fin n → S) : Measure S :=
  ∑ i : Fin n, Measure.dirac (x i)

@[fun_prop] lemma finitePointMeasure_measurable {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (finitePointMeasure (S := S) n) := by
  unfold finitePointMeasure
  fun_prop

def finitePoissonLaw {S : Type*} [MeasurableSpace S] (r : ℝ≥0) (ν : Measure S) :
    Measure (Measure S) :=
  Measure.sum fun n : ℕ =>
    poissonMeasure r {n} • (Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)

instance finitePoissonLaw_probability {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (finitePoissonLaw r ν) := by
  constructor
  rw [finitePoissonLaw,Measure.sum_apply _ MeasurableSet.univ]
  have hmass (n : ℕ) : ((Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)) univ = 1 := by
    rw [Measure.map_apply (finitePointMeasure_measurable n) MeasurableSet.univ,
      preimage_univ,measure_univ]
  simp only [Measure.smul_apply,hmass,smul_eq_mul,mul_one]
  have hh := hasSum_one_poissonMeasure r
  simp_rw [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hh.summable,hh.tsum_eq]
  norm_num

lemma measureSum_measurable {S : Type*} [MeasurableSpace S] :
    Measurable (fun η : ℕ → Measure S => Measure.sum η) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)

def countablePoissonLaw {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) : Measure (Measure S) :=
  (Measure.infinitePi fun i => finitePoissonLaw (r i) (ν i)).map Measure.sum

instance countablePoissonLaw_probability {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (countablePoissonLaw r ν) := by
  unfold countablePoissonLaw
  exact Measure.isProbabilityMeasure_map measureSum_measurable.aemeasurable

def finiteIntensityMarks {S : Type*} [MeasurableSpace S] [Nonempty S] (κ : Measure S) : Measure S :=
  if κ univ = 0 then Measure.dirac (Classical.choice ‹Nonempty S›) else (κ univ)⁻¹ • κ

instance finiteIntensityMarks_probability {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ] : IsProbabilityMeasure (finiteIntensityMarks κ) := by
  by_cases hκ : κ univ = 0
  · simp only [finiteIntensityMarks,ite_eq_left hκ]
    infer_instance
  · constructor
    simp [finiteIntensityMarks,hκ,ENNReal.inv_mul_cancel hκ (measure_ne_top _ _)]

def poissonRandomMeasureLaw {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] : Measure (Measure S) :=
  countablePoissonLaw (fun i => ((sfiniteSeq κ i) univ).toNNReal)
    (fun i => finiteIntensityMarks (sfiniteSeq κ i))

instance poissonRandomMeasureLaw_probability {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] : IsProbabilityMeasure (poissonRandomMeasureLaw κ) := by
  unfold poissonRandomMeasureLaw
  infer_instance

def stableLogIntensity (b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (b * Real.exp (-b*x)))

instance stableLogIntensity_sigmaFinite (b : ℝ) : SigmaFinite (stableLogIntensity b) := by
  unfold stableLogIntensity
  infer_instance

def normalizedMeasure {S : Type*} [MeasurableSpace S] (μ : Measure S) : Measure S :=
  (μ univ)⁻¹ • μ

lemma measurable_measure_withDensity_fixed {S : Type*} [MeasurableSpace S]
    {f : S → ℝ≥0∞} (hf : Measurable f) : Measurable (fun μ : Measure S => μ.withDensity f) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [withDensity_apply _ hs,← lintegral_indicator hs]
  exact Measure.measurable_lintegral (hf.indicator hs)

lemma normalizedMeasure_measurable {S : Type*} [MeasurableSpace S] :
    Measurable (normalizedMeasure (S := S)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  change Measurable (fun μ : Measure S => (μ univ)⁻¹ * μ s)
  exact (Measure.measurable_coe MeasurableSet.univ).inv.mul (Measure.measurable_coe hs)

section MarkedStable
variable {S : Type*} [MeasurableSpace S]

def markedStableTotalE (η : Measure (ℝ × S)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp p.1) ∂η

@[fun_prop] lemma markedStableTotalE_measurable : Measurable (markedStableTotalE (S := S)) :=
  Measure.measurable_lintegral (by fun_prop)

def markedStableTotal (η : Measure (ℝ × S)) : ℝ := (markedStableTotalE η).toReal

@[fun_prop] lemma markedStableTotal_measurable : Measurable (markedStableTotal (S := S)) :=
  markedStableTotalE_measurable.ennreal_toReal

def markedStableMassKernel : Kernel (Measure (ℝ × S)) (ℝ × S) where
  toFun η := normalizedMeasure (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)))
  measurable' := normalizedMeasure_measurable.comp (measurable_measure_withDensity_fixed (by fun_prop))

instance markedStableMassKernel_finite : IsFiniteKernel (markedStableMassKernel (S := S)) := by
  refine ⟨1, by simp, ?_⟩
  intro η
  change (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ)⁻¹ *
    (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ) ≤ 1
  exact ENNReal.inv_mul_le_one _

def markedStableCountKernel : Kernel (Measure (ℝ × S)) (ℝ × S) :=
  markedStableMassKernel.withDensity (fun η p => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1)))

end MarkedStable

@[reducible] def DecoratedCascade (S : Type) [MeasurableSpace S] : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (Measure (ℝ×(S×DecoratedCascade S n)))

instance decoratedCascadeNonempty (S : Type) [MeasurableSpace S] (n : ℕ) :
    Nonempty (DecoratedCascade S n) := by
  cases n with
  | zero => exact ⟨()⟩
  | succ n => exact ⟨(0 : Measure (ℝ×(S×DecoratedCascade S n)))⟩

def decoratedCascadeLaw {S : Type} [MeasurableSpace S] [Nonempty S]
    (ν : ProbabilityMeasure S) : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (DecoratedCascade S n)
  | 0, _ => ⟨Measure.dirac (),by exact Measure.dirac.isProbabilityMeasure⟩
  | n+1, z => ⟨poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))),
        by exact poissonRandomMeasureLaw_probability _⟩

def decoratedTerminalTotalE {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (H : X → ℝ) : (n : ℕ) → X×DecoratedCascade S n → ℝ≥0∞
  | 0, p => ENNReal.ofReal (Real.exp (H p.1))
  | n+1, p => ∫⁻ q : ℝ×(S×DecoratedCascade S n), ENNReal.ofReal (Real.exp q.1) *
      decoratedTerminalTotalE step H n (step (p.1,q.2.1),q.2.2) ∂markedStableCountKernel p.2

def decoratedTerminalTotal {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (H : X → ℝ) (n : ℕ) (p : X×DecoratedCascade S n) : ℝ :=
  (decoratedTerminalTotalE step H n p).toReal

def gaussianShiftStep (σ : ℕ → ℝ) (p : (ℕ → ℝ) × ℝ) : ℕ → ℝ :=
  fun i => p.1 (i+1)+σ i*p.2

def standardGaussianMark : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1,inferInstance⟩

def piMarkLaw {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) : ProbabilityMeasure (ι → S) :=
  ⟨Measure.pi (fun i => (ν i : Measure S)),inferInstance⟩

def canonicalCoordinateStep (d : ℕ) (σ : ℕ → ℝ) :
    (Fin d → ℕ → ℝ)×(Fin d → ℝ) → (Fin d → ℕ → ℝ) :=
  fun p i => gaussianShiftStep σ (p.1 i,p.2 i)

def decoratedLeafIntegral {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (F : X → ℝ≥0∞) :
    (n : ℕ) → X × DecoratedCascade S n → ℝ≥0∞
  | 0, p => F p.1
  | n+1, p => ∫⁻ q : ℝ × (S × DecoratedCascade S n),
      ENNReal.ofReal (Real.exp q.1) *
        decoratedLeafIntegral step F n (step (p.1,q.2.1),q.2.2)
          ∂markedStableCountKernel p.2

def decoratedFieldFactor {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (d : ℕ) (step : X × S → X) (field : X → Spin d) (k : ℕ)
    (p : X × DecoratedCascade S k) (x : Spin d) : ℝ≥0∞ :=
  decoratedLeafIntegral step (fun y => ENNReal.ofReal (Real.exp (inner ℝ (field y) x))) k p

def decoratedAngularFactor {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (field : X → Spin (n+1)) (k : ℕ)
    (p : X × DecoratedCascade S k) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u : Metric.sphere (0:Spin (n+1)) 1,
    decoratedFieldFactor (n+1) step field k p (r • (u:Spin (n+1))) ∂unitSphereLaw (n+1)

def coordinateLeafField (d : ℕ) (x : Fin d → ℕ → ℝ) : Spin d :=
  WithLp.toLp 2 (fun i => x i 0)

def coordinateCascadeLaw (d k : ℕ) (z : Fin k → ℝ) (r : ℝ≥0) :
    Measure ((Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k) :=
  (Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
    (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) k z)

def coordinateAngularLog (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ :=
  Real.log ((decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p R).toReal /
      decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)

def normalizedCoordinateSphereLog (n k : ℕ) (σ : ℕ → ℝ)
    (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ :=
  coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => p.1 i),p.2) / ((n+1:ℕ):ℝ)

def expectedCoordinateSphereLog (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ) (r : ℝ≥0) : ℝ :=
  ∫ p, normalizedCoordinateSphereLog n k σ p ∂coordinateCascadeLaw (n+1) k z r

def weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) : Trial where
  toFun := fun t => ∑ i, if q i ≤ t then w i else 0
  monotone := by
    intro s t hst
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : q i ≤ s
    · simp only [ite_eq_left hi,ite_eq_left (hi.trans hst),le_refl]
    · rw [ite_eq_right hi]
      split_ifs <;> first | exact hw i | rfl
  measurable := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
  nonneg := by
    intro t
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact hw i | rfl
  le_one := by
    intro t
    rw [← hw1]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | rfl | exact hw i

def stepCumulative {k : ℕ} (w : Fin (k+1) → ℝ) (i : Fin k) : ℝ :=
  ∑ j : Fin (k+1), if j ≤ i.castSucc then w j else 0

def stepFieldIncrement (k : ℕ) (h : Fin (k+1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < k then
    Real.sqrt (2*(h (Fin.rev ⟨j,hj⟩).succ-h (Fin.rev ⟨j,hj⟩).castSucc)) else 0

def finiteSphericalFieldValue (n k : ℕ) (w h : Fin (k+1) → ℝ) : ℝ :=
  expectedCoordinateSphereLog n k (stepFieldIncrement k h) (stepCumulative w)
    (Real.toNNReal (2*h 0))-h (Fin.last k)

def finiteSphericalDualObjective {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (q : Fin (k+1) → Time) : ℝ :=
  (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ)

def finiteSphericalDualValues {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) : Set ℝ :=
  finiteSphericalDualObjective w h hw hw1 ''
    {q : Fin (k+1) → Time | Monotone q ∧ (q (Fin.last k):ℝ) < 1}

structure FiniteFieldModel (f : Time → ℝ) where
  depth : ℕ
  value : Fin (depth+1) → ℝ
  label : Time → Fin (depth+1)
  measurable_label : Measurable label
  positive : ∀ i, 0 < timeLaw.real (label ⁻¹' {i})
  monotone_value : Monotone value
  agrees : (fun u => value (label u)) =ᵐ[timeLaw] f

def FiniteFieldModel.weight {f : Time → ℝ} (M : FiniteFieldModel f) (i : Fin (M.depth+1)) : ℝ :=
  timeLaw.real (M.label ⁻¹' {i})

def FiniteFieldModel.pressure {f : Time → ℝ} (M : FiniteFieldModel f) (n : ℕ) : ℝ :=
  finiteSphericalFieldValue n M.depth M.weight M.value

theorem exists_finiteFieldModel (f : Time → ℝ) (hf : Measurable f)
    (hfin : (Set.range f).Finite) : Nonempty (FiniteFieldModel f) := by
  classical
  let S := hfin.toFinset
  let T := S.filter (fun r => 0 < timeLaw.real (f ⁻¹' {r}))
  have hae : ∀ᵐ u ∂timeLaw, f u ∈ T := by
    have hnull : ∀ r ∈ S, ∀ᵐ u ∂timeLaw, f u=r → 0 < timeLaw.real (f ⁻¹' {r}) := by
      intro r hr
      by_cases hp : 0 < timeLaw.real (f ⁻¹' {r})
      · exact ae_of_all _ (fun _ _ => hp)
      · have hz : timeLaw (f ⁻¹' {r})=0 := by
          have hz : (timeLaw (f ⁻¹' {r})).toReal=0 := le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
          have hp := (ENNReal.toReal_eq_zero_iff _).mp hz
          rcases hp with hp | hp
          · exact hp
          · exact (measure_ne_top _ _ hp).elim
        have hnot : ∀ᵐ u ∂timeLaw, f u ≠ r := by
          apply ae_iff.mpr
          simpa only [Set.preimage,Set.mem_singleton_iff,not_not] using hz
        filter_upwards [hnot] with u hu
        exact fun h => (hu h).elim
    have hall := (S.eventually_all).mpr hnull
    filter_upwards [hall] with u hu
    have hmem : f u ∈ S := hfin.mem_toFinset.mpr (mem_range_self u)
    exact Finset.mem_filter.mpr ⟨hmem,hu (f u) hmem rfl⟩
  have hT : T.Nonempty := by
    obtain ⟨u,hu⟩ := hae.exists
    exact ⟨f u,hu⟩
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hT)
  let e := T.orderIsoOfFin hd
  let v : Fin (d+1) → ℝ := fun i => e i
  have hv : StrictMono v := fun i j hij => e.strictMono hij
  have hve : MeasurableEmbedding v := ⟨hv.injective,measurable_of_finite _,fun _ _ => (Set.toFinite _).measurableSet⟩
  let a : Time → Fin (d+1) := fun u => hve.invFun (f u)
  have hag : (fun u => v (a u)) =ᵐ[timeLaw] f := by
    filter_upwards [hae] with u hu
    have hx : f u=v (e.symm ⟨f u,hu⟩) := congrArg Subtype.val (e.apply_symm_apply ⟨f u,hu⟩) |>.symm
    dsimp only [a]
    rw [hx,hve.leftInverse_invFun]
  refine ⟨⟨d,v,a,hve.measurable_invFun.comp hf,?_,hv.monotone,hag⟩⟩
  intro i
  have he : a ⁻¹' {i}=ᵐ[timeLaw] f ⁻¹' {v i} := by
    filter_upwards [hag] with u hu
    apply propext
    change (a u=i) ↔ f u=v i
    rw [← hu]
    exact hv.injective.eq_iff.symm
  change 0 < (timeLaw (a ⁻¹' {i})).toReal
  rw [measure_congr he]
  exact (Finset.mem_filter.mp (e i).2).2

structure BoundedField (H : ℝ) where
  toFun : Time → ℝ
  monotone : Monotone toFun
  nonneg : ∀ u, 0 ≤ toFun u
  le_bound : ∀ u, toFun u ≤ H

instance {H : ℝ} : CoeFun (BoundedField H) (fun _ => Time → ℝ) := ⟨BoundedField.toFun⟩

lemma BoundedField.measurable {H : ℝ} (f : BoundedField H) : Measurable f := f.monotone.measurable

def roundLower (N : ℕ) (x : ℝ) : ℝ := (⌊(N+1:ℕ)*x⌋₊:ℝ)/(N+1:ℕ)

lemma roundLower_nonneg (N : ℕ) (x : ℝ) : 0 ≤ roundLower N x := by unfold roundLower; positivity

lemma roundLower_monotone (N : ℕ) : Monotone (roundLower N) := by
  intro x y hxy
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_left hxy (by positivity))

lemma roundLower_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : roundLower N x ≤ x := by
  unfold roundLower
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(N+1:ℕ))]
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg (by positivity) hx)

def BoundedField.round {H : ℝ} (f : BoundedField H) (N : ℕ) : BoundedField H where
  toFun := fun u => roundLower N (f u)
  monotone := (roundLower_monotone N).comp f.monotone
  nonneg := fun u => roundLower_nonneg N (f u)
  le_bound := fun u => (roundLower_le N (f.nonneg u)).trans (f.le_bound u)

lemma BoundedField.round_finite {H : ℝ} (f : BoundedField H) (N : ℕ) :
    (Set.range (f.round N)).Finite := by
  let T := (Finset.range (⌊(N+1:ℕ)*H⌋₊+1)).image (fun k : ℕ => (k:ℝ)/(N+1:ℕ))
  apply T.finite_toSet.subset
  rintro x ⟨u,rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨⌊(N+1:ℕ)*f u⌋₊,?_,rfl⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Nat.floor_mono (mul_le_mul_of_nonneg_left (f.le_bound u) (by positivity)))

def BoundedField.roundModel {H : ℝ} (f : BoundedField H) (N : ℕ) : FiniteFieldModel (f.round N) :=
  Classical.choice (exists_finiteFieldModel _ (f.round N).measurable (f.round_finite N))

def quantileTrial (q : Time → Time) : Trial where
  toFun := fun t => timeLaw.real {u | q u ≤ t}
  monotone := by
    intro s t hst
    exact measureReal_mono (fun u hu => hu.trans hst)
  measurable := by
    apply Monotone.measurable
    intro s t hst
    exact measureReal_mono (fun u hu => hu.trans hst)
  nonneg := fun _ => measureReal_nonneg
  le_one := by
    intro t
    exact measureReal_le_one

def quantileTail (q : Time → Time) (t : ℝ) : ℝ :=
  ∫ u, 1-max (q u:ℝ) t ∂timeLaw

lemma quantileTail_integrable (q : Time → Time) (hq : Measurable q) (t : ℝ) :
    Integrable (fun u => 1-max (q u:ℝ) t) timeLaw := by
  have hm : Measurable (fun u => 1-max (q u:ℝ) t) :=
    measurable_const.sub ((measurable_subtype_coe.comp hq).max measurable_const)
  apply Integrable.mono' (integrable_const (2+|t|)) hm.aestronglyMeasurable
  exact ae_of_all _ fun u => by
    rw [Real.norm_eq_abs]
    have hq0 := (q u).2.1
    have hq1 := (q u).2.2
    have ha : |max (q u:ℝ) t| ≤ 1+|t| := by
      rcases le_total (q u:ℝ) t with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h,abs_of_nonneg hq0]; nlinarith [abs_nonneg t]
    have hb := abs_sub 1 (max (q u:ℝ) t)
    norm_num at hb
    linarith

lemma quantileTail_lower (q : Time → Time) (hq : Measurable q) {B t : ℝ}
    (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) (ht : t ≤ B) :
    1-B ≤ quantileTail q t := by
  have h := integral_mono_ae (integrable_const (1-B)) (quantileTail_integrable q hq t)
    (hb.mono fun u hu => sub_le_sub_left (max_le hu ht) 1)
  simpa [quantileTail] using h

lemma quantileTail_lipschitz (q : Time → Time) (hq : Measurable q) :
    LipschitzWith 1 (quantileTail q) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul]
  unfold quantileTail
  rw [← integral_sub (quantileTail_integrable q hq s) (quantileTail_integrable q hq t)]
  calc
    _ ≤ ∫ u, |(1-max (q u:ℝ) s)-(1-max (q u:ℝ) t)| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Time, |s-t| ∂timeLaw := by
      apply integral_mono ((quantileTail_integrable q hq s).sub (quantileTail_integrable q hq t)).abs (integrable_const _)
      intro u
      have h := (LipschitzWith.id.const_max (q u:ℝ)).dist_le_mul s t
      simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
      change |(1-max (q u:ℝ) s)-(1-max (q u:ℝ) t)| ≤ _
      rw [show (1-max (q u:ℝ) s)-(1-max (q u:ℝ) t)=max (q u:ℝ) t-max (q u:ℝ) s by ring,abs_sub_comm]
      exact h
    _ = _ := by simp

def boundedSphericalFieldValue {H : ℝ} (f : BoundedField H) (n : ℕ) : ℝ :=
  limUnder atTop (fun N => (f.roundModel N).pressure n)

def BoundedField.toQuantile {B : ℝ} (q : BoundedField B) (hB : B ≤ 1) : Time → Time :=
  fun u => ⟨q u,q.nonneg u,(q.le_bound u).trans hB⟩

lemma BoundedField.toQuantile_measurable {B : ℝ} (q : BoundedField B) (hB : B ≤ 1) :
    Measurable (q.toQuantile hB) := q.measurable.subtype_mk

def quantileA (q : Time → Time) (r : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..r, 1/(quantileTail q t)^2

lemma quantileA_integrand_continuous {B : ℝ} (q : Time → Time) (hq : Measurable q)
    (hB : B < 1) (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) :
    ContinuousOn (fun t => 1/(quantileTail q t)^2) (Icc 0 B) := by
  apply continuousOn_const.div ((quantileTail_lipschitz q hq).continuous.continuousOn.pow 2)
  intro t ht
  exact pow_ne_zero _ (ne_of_gt ((sub_pos.mpr hB).trans_le (quantileTail_lower q hq hb ht.2)))

lemma quantileA_integrand_bound {B t : ℝ} (q : Time → Time) (hq : Measurable q)
    (hB : B < 1) (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) (ht : t ≤ B) :
    1/(quantileTail q t)^2 ≤ 1/(1-B)^2 := by
  have hd := quantileTail_lower q hq hb ht
  exact one_div_le_one_div_of_le (sq_pos_of_pos (sub_pos.mpr hB))
    (pow_le_pow_left₀ (sub_nonneg.mpr hB.le) hd 2)

lemma quantileA_nonneg (q : Time → Time) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ quantileA q r :=
  intervalIntegral.integral_nonneg hr (fun _ _ => by positivity)

lemma quantileA_mono {B : ℝ} (q : Time → Time) (hq : Measurable q)
    (hB : B < 1) (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) :
    MonotoneOn (quantileA q) (Icc 0 B) := by
  intro r hr s hs hrs
  exact intervalIntegral.integral_mono_interval le_rfl hr.1 hrs
    (ae_of_all _ fun _ => by positivity)
    (((quantileA_integrand_continuous q hq hB hb).mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1)

lemma quantileA_bound {B r : ℝ} (q : Time → Time) (hq : Measurable q)
    (hB : B < 1) (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) (hr : r ∈ Icc 0 B) :
    quantileA q r ≤ B/(1-B)^2 := by
  have h := intervalIntegral.integral_mono_on hr.1
    (((quantileA_integrand_continuous q hq hB hb).mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1)
    (intervalIntegrable_const (μ := volume) (c := 1/(1-B)^2))
    (fun t ht => quantileA_integrand_bound q hq hB hb (ht.2.trans hr.2))
  have he : (∫ _t in (0:ℝ)..r, 1/(1-B)^2)=r/(1-B)^2 := by simp [div_eq_mul_inv]
  rw [he] at h
  exact h.trans (div_le_div_of_nonneg_right hr.2 (sq_nonneg _))

def BoundedField.stationary {B : ℝ} (q : BoundedField B) (hB : B < 1) :
    BoundedField (B/(2*(1-B)^2)) where
  toFun := fun u => quantileA (q.toQuantile hB.le) (q u)/2
  monotone := fun u v huv => div_le_div_of_nonneg_right
    (quantileA_mono _ (q.toQuantile_measurable hB.le) hB (ae_of_all _ q.le_bound)
      ⟨q.nonneg u,q.le_bound u⟩ ⟨q.nonneg v,q.le_bound v⟩ (q.monotone huv)) (by norm_num)
  nonneg := fun u => div_nonneg (quantileA_nonneg _ (q.nonneg u)) (by norm_num)
  le_bound := by
    intro u
    have h := (quantileA_bound _ (q.toQuantile_measurable hB.le) hB (ae_of_all _ q.le_bound)
      ⟨q.nonneg u,q.le_bound u⟩)
    calc
      _ ≤ (B/(1-B)^2)/2 := div_le_div_of_nonneg_right h (by norm_num)
      _ = _ := by rw [div_div,mul_comm]

def clippedQuantile (q : Time → Time) (hq : Monotone q) (B : ℝ) (hB0 : 0 ≤ B) : BoundedField B where
  toFun := fun u => min (q u:ℝ) B
  monotone := fun _ _ huv => min_le_min (hq huv) le_rfl
  nonneg := fun u => le_min (q u).2.1 hB0
  le_bound := fun _ => min_le_right _ _

def stationaryQuantileField (q : Time → Time) (hq : Monotone q) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1) :
    BoundedField (B/(2*(1-B)^2)) := (clippedQuantile q hq B hB0).stationary hB1

def SphericalLinearFieldFormula : Prop :=
  (∀ (k : ℕ) (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1),
    (∀ h : Fin (k+1) → ℝ, Monotone h → 0 ≤ h 0 →
      ∃ q : Fin (k+1) → Time, Monotone q ∧ (q (Fin.last k):ℝ) < 1 ∧
        IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
          (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q)) ∧
    (∀ K : Set (Fin (k+1) → ℝ), IsCompact K →
      (∀ h ∈ K, Monotone h ∧ 0 ≤ h 0) →
      TendstoUniformlyOn (fun n h => finiteSphericalFieldValue n k w h)
        (fun h => sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)) atTop K)) ∧
  (∀ (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1) (ε : ℝ), 0 < ε →
    ∀ᶠ n : ℕ in atTop, ∀ (q : Time → Time) (hq : Monotone q),
      (∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B) →
      entropy (quantileTrial q) < ∞ ∧
      (∀ᵐ u ∂timeLaw, 2*stationaryQuantileField q hq B hB0 hB1 u=quantileA q (q u)) ∧
      |boundedSphericalFieldValue (stationaryQuantileField q hq B hB0 hB1) n-
        ((entropy (quantileTrial q)).toReal-
          ∫ u, stationaryQuantileField q hq B hB0 hB1 u*(q u:ℝ) ∂timeLaw)| < ε)

end SphericalPerceptron

end

namespace SphericalPerceptron


end SphericalPerceptron
end OAI


