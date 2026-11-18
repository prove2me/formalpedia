-- Prove2me | Definitions.Def_Kyprianou_Ch08_ProcessAndExponent
-- name    : Kyprianou_Ch08_ProcessAndExponent
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T07:13:47.705989+00:00
-- url     : https://prove2.me/theorems/1c8b091f-7b43-4729-b2e6-61f7434c8053
-- title:
--   Kyprianou Chapter 8: ProcessAndExponent
-- statement:
--   Source-law-bound spectrally negative Levy process, its actual Levy-Khintchine triplet, full real moment Laplace exponent and lawful Esscher density families.
-- source:
--   Kyprianou (2006), first edition, Chapter 8, original physical pages 219-246; source SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08

/-- Chapter 8, pp. 211-213. This is explicit path/law/triplet DATA.
It is not, on its own, a proof of the Levy axioms. The published
SpectrallyNegativeLevy interface requires a separately checked bridge. -/
structure ProcessData (Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  probabilityLaw : IsProbabilityMeasure law
  X : ℝ≥0 → Ω → ℝ
  tripletA : ℝ
  gaussian : ℝ
  jumps : Measure ℝ

/-- Genuine source-law model. The imported Chapter 1/LeanLevy process
predicate supplies the Levy axioms; the characteristic-function relation
identifies the actual Levy-Khintchine triplet and fixes the book sign.
This does not assume Chapter 8 exit or scale-function theorems. -/
structure SpectrallyNegativeModel (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  X : ℝ≥0 → Ω → ℝ
  levy : ProbabilityTheory.IsLevyProcess X P
  triplet : ProbabilityTheory.LevyKhintchineTriple
  characteristic : ∀ (t : ℝ≥0) (ξ : ℝ),
    charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) *
        Kyprianou.Ch01.levyTripleExponent triplet ξ)
  negativeJumps : triplet.levyMeasure (Set.Ici (0 : ℝ)) = 0
  gaussianCoefficient : ℝ
  gaussianNonnegative : 0 ≤ gaussianCoefficient
  gaussianVarianceMatch :
    gaussianCoefficient ^ 2 = (triplet.gaussianVariance : ℝ)
  excludesNegativeSubordinator :
    ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => X t ω))

/-- A completed natural filtration is required as a separate,
published Chapter 3 predicate; it is not inferred from marginal measurability. -/
def HasCompletedNaturalFiltration {Ω : Type} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (F : Filtration ℝ≥0 m) : Prop :=
  Kyprianou.Ch03.IsCompletedNaturalFiltration P D.X F

/-- Canonical bridge from the actual Levy model to its numerical triplet
and probability-law fields. No new process existence is postulated. -/
noncomputable def SpectrallyNegativeModel.toData
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) : ProcessData Ω :=
  { law := P
    probabilityLaw := inferInstance
    X := D.X
    tripletA := D.triplet.drift
    gaussian := D.gaussianCoefficient
    jumps := D.triplet.levyMeasure }

/-- Spectral negativity means the Levy measure charges no positive jumps. -/
def HasNegativeJumpSupport (jumpMeasure : Measure ℝ) : Prop :=
  jumpMeasure (Set.Ici (0 : ℝ)) = 0

/-- The Levy measure integrability and negative-jump support are obligations,
not consequences of the existence of the above data structure. -/
def IsNegativeLevyMeasure (jumpMeasure : Measure ℝ) : Prop :=
  HasNegativeJumpSupport jumpMeasure ∧
  (∫⁻ x : ℝ, ENNReal.ofReal (min (x ^ 2) 1) ∂jumpMeasure) < ⊤

/-- Stationary-increment distributional law; one of the Levy axioms. -/
def HasStationaryIncrementLaws {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) : Prop :=
  ∀ s t : ℝ≥0,
    Measure.map (fun ω => D.X (s + t) ω - D.X s ω) D.law =
    Measure.map (D.X t) D.law

/-- The triplet convention is psi(beta)=-a beta+sigma² beta²/2 +
integral (exp(beta*x)-1-beta*x 1_{x>-1}) Pi(dx).
Chapter 8 excludes negative subordinators and assumes a positive
drift in the bounded-variation case. -/
noncomputable def tripletLaplace (a σ : ℝ) (jumpMeasure : Measure ℝ) (β : ℝ) : ℝ :=
  -a * β + σ ^ 2 * β ^ 2 / 2 +
    ∫ x : ℝ, (Real.exp (β * x) - 1 -
      (if -1 < x then β * x else 0)) ∂jumpMeasure

/-- Laplace exponent from the entire nonnegative moment-generating
family. The original Chapter 8 convention is E exp(beta X_t)=exp(t psi(beta)).
Integrability is part of this predicate, not an assumed theorem conclusion. -/
def IsLaplaceExponent {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) : Prop :=
  ∀ (β : ℝ) (t : ℝ≥0), 0 ≤ β → 0 < t →
    Integrable (fun ω => Real.exp (β * D.X t ω)) D.law ∧
    ψ β = Real.log (∫ ω, Real.exp (β * D.X t ω) ∂D.law) / (t : ℝ)

/-- Exponent on the WHOLE real moment domain of the original Levy law.
At each finite positive time the moment is strictly positive and its log
equals t*psi(c). The generator must prove this from the process; an
arbitrary negative extension of an otherwise correct psi is excluded.
For c outside that domain no value of psi(c) is asserted. -/
def IsFullMomentLaplaceExponent {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) : Prop :=
  IsLaplaceExponent D ψ ∧
  ∀ (c : ℝ) (t : ℝ≥0), 0 < t →
    Integrable (fun ω => Real.exp (c * D.X t ω)) D.law →
      0 < (∫ ω, Real.exp (c * D.X t ω) ∂D.law) ∧
      ψ c = Real.log
        (∫ ω, Real.exp (c * D.X t ω) ∂D.law) / (t : ℝ)

/-- The corresponding source Esscher parameter is any real number
whose exponential moment is finite and strictly positive. -/
def HasLawfulEsscherMoment {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFullMomentLaplaceExponent D ψ ∧
  Integrable (fun ω => Real.exp (c * D.X 1 ω)) D.law ∧
  0 < (∫ ω, Real.exp (c * D.X 1 ω) ∂D.law)

/-- Actual law-normalisation and positivity of the Esscher density
at EACH finite time, not merely an arbitrary algebraic shift.
Measurability and filtration consistency remain separate proofs. -/
def HasLawfulEsscherDensities {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) (c : ℝ) : Prop :=
  HasLawfulEsscherMoment D ψ c ∧
  ∀ t : ℝ≥0, 0 < t →
    Integrable (fun ω => Real.exp (c * D.X t ω)) D.law ∧
    Integrable (fun ω => Real.exp
      (c * D.X t ω - ψ c * (t : ℝ))) D.law ∧
    (∀ ω, 0 < Real.exp
      (c * D.X t ω - ψ c * (t : ℝ))) ∧
    (∫ ω, Real.exp
      (c * D.X t ω - ψ c * (t : ℝ)) ∂D.law) = 1

/-- Source triplet and actual law exponent bridge. The function is
bound to the process via IsLaplaceExponent and explicitly to the
truncated negative-jump triplet. No theorem asserting this bridge is
silently imported; proving it is a separately planned obligation. -/
def HasLawTripletLaplaceBridge {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) : Prop :=
  IsNegativeLevyMeasure D.jumps ∧
  IsLaplaceExponent D (tripletLaplace D.tripletA D.gaussian D.jumps) ∧
  ∀ β : ℝ, 0 ≤ β →
    tripletLaplace D.tripletA D.gaussian D.jumps β =
      AvramDividend.Classical.laplaceExponent
        (-D.tripletA) D.gaussian D.jumps β

/-- Pairwise independence of separated increments, expressible without
asserting that pairwise independence suffices for the Levy property.
Full joint independence remains an explicit bridge obligation. -/
def HasPairwiseIndependentDisjointIncrements {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) : Prop :=
  ∀ s t u v : ℝ≥0, s ≤ t → t ≤ u → u ≤ v →
    Measure.map
      (fun ω => (D.X t ω - D.X s ω, D.X v ω - D.X u ω)) D.law =
    (Measure.map (fun ω => D.X t ω - D.X s ω) D.law).prod
      (Measure.map (fun ω => D.X v ω - D.X u ω) D.law)

/-- The rightmost nonnegative zero set of psi(lambda)-q. -/
def RightRootSet (ψ : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {β | 0 ≤ β ∧ ψ β = q}

/-- Supremum construction; existence and root properties are separate. -/
noncomputable def Phi (ψ : ℝ → ℝ) (q : ℝ) : ℝ :=
  sSup (RightRootSet ψ q)

/-- Domain-sensitive predicate for Phi(q); q=0 may also have root 0. -/
def PhiIsLargestRoot (ψ : ℝ → ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ (Phi ψ q ∈ RightRootSet ψ q) ∧
  ∀ β ∈ RightRootSet ψ q, β ≤ Phi ψ q

/-- BV variation criterion: sigma=0 and finite small-jump first moment. -/
def HasBoundedVariationTriplet (σ : ℝ) (jumpMeasure : Measure ℝ) : Prop :=
  σ = 0 ∧
  (∫⁻ x in Set.Ioo (-1 : ℝ) 0, ENNReal.ofReal |x| ∂jumpMeasure) < ⊤

/-- Positive drift d = -a - integral_{(-1,0)} x Pi(dx);
strict positivity is an additional standing assumption. -/
noncomputable def bvDrift (a : ℝ) (jumpMeasure : Measure ℝ) : ℝ :=
  -a - ∫ x in Set.Ioo (-1 : ℝ) 0, x ∂jumpMeasure

/-- Strictly positive bounded-variation drift: the exceptional negative
subordinator regime is excluded here as an EXPLICIT predicate, without
assuming the positivity lemma or any Chapter 8 exit identity. -/
def HasPositiveBVDrift (a σ : ℝ) (jumpMeasure : Measure ℝ) : Prop :=
  HasBoundedVariationTriplet σ jumpMeasure ∧ 0 < bvDrift a jumpMeasure

/-- The BV Laplace representation from equation (8.1). -/
noncomputable def bvLaplace (d : ℝ) (jumpMeasure : Measure ℝ) (β : ℝ) : ℝ :=
  d * β - ∫ x in Set.Iio (0 : ℝ),
    (1 - Real.exp (β * x)) ∂jumpMeasure

/-- Finite-time Esscher density exp(c X_t - t psi(c)), on the real finite-moment domain.
Normalisation and consistency in t remain proof obligations. -/
noncomputable def esscherDensity {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ) (c : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c * D.X t ω - ψ c * (t : ℝ))

/-- Historical nonnegative parameter convention for restricted proofs.
The actual source also allows negative finite-moment Esscher parameters;
use HasLawfulEsscherMoment for those. -/
def IsEsscherParameter (c : ℝ) : Prop := 0 ≤ c

/-- Shifted exponent on the valid real moment domain: psi(beta+c)-psi(c).
Both psi evaluations must be anchored by IsFullMomentLaplaceExponent. -/
def shiftedExponent (ψ : ℝ → ℝ) (c beta : ℝ) : ℝ :=
  ψ (beta + c) - ψ c

/-- Finite-time Esscher measure, defined by the normalised
candidate density. Its probability normalisation and consistency on
the completed natural filtration are separate obligations. -/
noncomputable def esscherFiniteTimeLaw {Ω : Type*} [MeasurableSpace Ω]
    (D : ProcessData Ω) (ψ : ℝ → ℝ)
    (c : ℝ) (t : ℝ≥0) : Measure Ω :=
  D.law.withDensity (fun ω => ENNReal.ofReal
    (esscherDensity D ψ c t ω))

end Kyprianou.Ch08


