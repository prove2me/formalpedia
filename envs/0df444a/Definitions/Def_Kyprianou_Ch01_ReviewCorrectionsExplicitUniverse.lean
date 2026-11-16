-- Prove2me | Definitions.Def_Kyprianou_Ch01_ReviewCorrectionsExplicitUniverse
-- name    : Kyprianou_Ch01_ReviewCorrectionsExplicitUniverse
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:13:35.635583+00:00
-- url     : https://prove2.me/theorems/d8ab2637-1b1a-4b4a-a9b0-250200037707
-- title:
--   Chapter 1 reviewed certification with explicit universe binders
-- statement:
--   Seven exact proposition certificates for reviewed Chapter 1 theorem targets. Corrects strict first passage to the right-continuous filtration and makes the stable exponent synthesis, branching rate generator, non-finite-mean Lamperti scope, exponent sign conversion and almost-sure continuity bridge explicit.
-- source:
--   Kyprianou (2006), Chapter 1, Theorem 1.3, §1.2.5–1.2.6, §1.3.4 and Exercises 1.4, 1.6, 1.11; Sousi (2011) Proposition 3.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ChapterCertification
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u v
namespace Kyprianou.Ch01

/-- Exact proposition for Kyprianou.Ch01.inverseGaussianFirstPassageLaplaceRightContinuous. -/
noncomputable def certificate_inverseGaussianFirstPassageLaplaceRightContinuous : Prop :=
  ∀     {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)),
    IsNaturalRightStoppingTime X (firstUpperPassage X s) ∧
      ∀ q : ℝ, 0 ≤ q →
        (∫ ω, passageLaplace (firstUpperPassage X s) q ω ∂P) =
          Real.exp (-(s * (Real.sqrt (b ^ 2 + 2 * q) - b)))

/-- Exact proposition for Kyprianou.Ch01.stableLevyExponentFormAwayFromOne. -/
noncomputable def certificate_stableLevyExponentFormAwayFromOne : Prop :=
  ∀     (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ha1 : alpha ≠ 1)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg),
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          ((c * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((beta * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ))

/-- Exact proposition for Kyprianou.Ch01.stableLevyExponentFormIndexOne. -/
noncomputable def certificate_stableLevyExponentFormIndexOne : Prop :=
  ∀     (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg),
    let alpha : ℝ := 1;
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          ((c * |xi| : ℝ) : ℂ) *
            (1 + Complex.I *
              (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ))

/-- Exact proposition for Kyprianou.Ch01.branchingOneAncestorGeneratorFromRates. -/
noncomputable def certificate_branchingOneAncestorGeneratorFromRates : Prop :=
  ∀     (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hrate : 0 < rate) (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring),
    ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism (rate : ℝ) offspring q) * Real.exp (-q))
        (Set.Ici 0) 0

/-- Exact proposition for Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLawWithoutMoment. -/
noncomputable def certificate_lampertiBranchingToCompoundPoissonPathLawWithoutMoment : Prop :=
  ∀     {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω))
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k),
    ∀ y : ℕ,
      (P y).map
        (fun ω => fun t : ℝ≥0 => (branchingToPoisson Y t ω : ℤ)) =
      Q.map
        (fun ω => fun t : ℝ≥0 =>
          stoppedIntegerCompoundPoisson y arrival marks t ω)

/-- Exact proposition for Kyprianou.Ch01.levyTripletExponentSignBridge. -/
noncomputable def certificate_levyTripletExponentSignBridge : Prop :=
  ∀     (T : ProbabilityTheory.LevyKhintchineTriple) (xi : ℝ),
    -levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) +
      (((T.gaussianVariance : ℝ) * xi ^ 2 / 2 : ℝ) : ℂ) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure)

/-- Exact proposition for Kyprianou.Ch01.continuousRepresentativeForAlmostSurePaths. -/
noncomputable def certificate_continuousRepresentativeForAlmostSurePaths : Prop :=
  ∀     {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContSet : MeasurableSet {ω | Continuous (fun t : ℝ≥0 => X t ω)})
    (hAE : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)),
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = X t ω)

end Kyprianou.Ch01


