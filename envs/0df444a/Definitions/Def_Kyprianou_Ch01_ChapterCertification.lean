-- Prove2me | Definitions.Def_Kyprianou_Ch01_ChapterCertification
-- name    : Kyprianou_Ch01_ChapterCertification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T00:16:16.445731+00:00
-- url     : https://prove2.me/theorems/7a3aa19b-0896-48f2-b391-feab03e6bc13
-- title:
--   Chapter 1 source theorem certification propositions
-- statement:
--   Full nonvacuous proposition forms of all forty-eight source-specific theorem drafts currently in the Chapter 1 draft. These encode the exact quantified mathematical obligations as conjunction components; no obligation is an assumption or proof. The remaining exercise subresults and detailed Lamperti proofs are not yet covered, so this certificate bundle is provisional pending additional obligations.
-- source:
--   Kyprianou (2006), Chapter 1, Theorems 1.3, 1.6, 1.8–1.13, Lemma 1.7, compound Poisson examples and Exercise 1.11.

import Mathlib

import Definitions.Def_LeanLevy_Levy_LevyKhintchine

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw

import Definitions.Def_LeanLevy_Processes_LevyProcess

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore

import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

import Definitions.Def_Kyprianou_Ch01_BranchingClocks

import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples

import Definitions.Def_Kyprianou_Ch01_LampertiInverse

import Definitions.Def_Kyprianou_Ch01_BranchingGenerator

import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter

open scoped NNReal ENNReal BigOperators

set_option autoImplicit false

universe u v

namespace Kyprianou.Ch01

/-- Source obligation: Kyprianou.Ch01.levyKhintchineLaw. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_levyKhintchineLaw : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    ProbabilityTheory.IsInfinitelyDivisible μ ↔
      ∃ T : ProbabilityTheory.LevyKhintchineTriple,
        ∀ (ξ : ℝ), charFun μ ξ = Complex.exp (Kyprianou.Ch01.levyTripleExponent T ξ)

/-- Source obligation: Kyprianou.Ch01.levy_khintchine_process_exists. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_levy_khintchine_process_exists : Prop :=
  ∀ (T : ProbabilityTheory.LevyKhintchineTriple),
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (X : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (μ.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) * Kyprianou.Ch01.levyTripleExponent T ξ)

/-- Source obligation: Kyprianou.Ch01.compoundPoissonCharExponent. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_compoundPoissonCharExponent : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0) (ξ : ℝ),
    charFun (μ.map (compoundPoisson b τ Y (t : ℝ))) ξ =
      Complex.exp (((t : ℝ) : ℂ) *
        (Complex.I * ((b * ξ : ℝ) : ℂ) +
          ((r : ℝ) : ℂ) * (charFun ν' ξ - 1)))

/-- Source obligation: Kyprianou.Ch01.compoundPoissonInfinitelyDivisible. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_compoundPoissonInfinitelyDivisible : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0),
    IsInfinitelyDivisible
      (μ.map (compoundPoisson b τ Y (t : ℝ)))

/-- Source obligation: Kyprianou.Ch01.frullani_complex. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_frullani_complex : Prop :=
  ∀ (α β : ℝ) (z : ℂ) (hα : 0 < α) (hβ : 0 < β) (hz : z.re ≤ 0),
    (IntegrableOn
      (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))
      (Ioi (0 : ℝ))) ∧
      Complex.exp (-(β : ℂ) * Complex.log (1 - z / (α : ℂ))) =
        Complex.exp
          (-(∫ x in Ioi (0 : ℝ),
            ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
              ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ))))

/-- Source obligation: Kyprianou.Ch01.pollaczekKhintchineRuin. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_pollaczekKhintchineRuin : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x →
      (P (ruinEvent arrival claims premium 0 ∩
        {ω | ruinDeficit arrival claims premium 0 ω ≤ x})).toReal =
        ruinProbability P arrival claims premium 0 *
          (eta (Set.Iic x)).toReal),
    ∀ x : ℝ, 0 ≤ x →
      1 - ruinProbability P arrival claims premium x =
        pkCDF eta (ruinProbability P arrival claims premium 0) x

/-- Source obligation: Kyprianou.Ch01.ruinDeficitIntegratedTail. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_ruinDeficitIntegratedTail : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium),
    ruinProbability P arrival claims premium 0 =
        (rate : ℝ) * mu / premium ∧
      ∀ x : ℝ, 0 ≤ x →
        (P (ruinEvent arrival claims premium 0 ∩
          {ω | ruinDeficit arrival claims premium 0 ω ≤ x})).toReal =
          ruinProbability P arrival claims premium 0 *
            integratedTailCDF F mu x

/-- Source obligation: Kyprianou.Ch01.lundbergBound. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_lundbergBound : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hint : Integrable
      (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) P)
    (hroot : (∫ ω, Real.exp
      (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) = 1),
    ∀ x : ℝ, 0 < x →
      ruinProbability P arrival claims premium x ≤ Real.exp (-nu * x)

/-- Source obligation: Kyprianou.Ch01.lundbergAsymptotic. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_lundbergAsymptotic : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hnonlattice : IsNonLattice F)
    (hint : Integrable
      (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) P)
    (hroot : (∫ ω, Real.exp
      (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) = 1),
    let weightedTail : ℝ≥0∞ :=
      ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (y * Real.exp (nu * y) * (F (Set.Ioi y)).toReal) ∂volume
    Tendsto (fun x : ℝ => Real.exp (nu * x) *
      ruinProbability P arrival claims premium x) atTop
      (nhds (if weightedTail = ⊤ then 0 else
        (((rate : ℝ) * nu / (premium - (rate : ℝ) * mu)) *
          weightedTail.toReal)⁻¹))

/-- Source obligation: Kyprianou.Ch01.mg1IdleOverloaded. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_mg1IdleOverloaded : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (hoverload : 1 < (rate : ℝ) * mu),
    ∃ theta : ℝ,
      0 < theta ∧ queueLaplaceExponent rate F theta = 0 ∧
      (∀ u : ℝ, theta < u → queueLaplaceExponent rate F u ≠ 0) ∧
      ∀ w : ℝ, 0 ≤ w →
        (P {ω | totalIdleTime arrival claims w ω = 0}).toReal =
          1 - Real.exp (-theta * w) ∧
        ∀ x : ℝ, 0 ≤ x →
          (P {ω | (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ∧
            totalIdleTime arrival claims w ω ≤ ENNReal.ofReal x}).toReal =
              Real.exp (-theta * w) * (1 - Real.exp (-theta * x))

/-- Source obligation: Kyprianou.Ch01.mg1IdleCriticalAndLight. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_mg1IdleCriticalAndLight : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (hload : (rate : ℝ) * mu ≤ 1),
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = ⊤}).toReal = 1

/-- Source obligation: Kyprianou.Ch01.mg1StationaryWorkload. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_mg1StationaryWorkload : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (hlight : (rate : ℝ) * mu < 1)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x →
      (eta (Set.Iic x)).toReal = integratedTailCDF F mu x),
    ∀ w : ℝ, 0 ≤ w → ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun t : ℝ≥0 =>
        (P {ω | queueWorkload arrival claims w t ω ≤ x}).toReal)
        atTop (nhds (pkCDF eta ((rate : ℝ) * mu) x))

/-- Source obligation: Kyprianou.Ch01.mg1UnboundedLimsup. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_mg1UnboundedLimsup : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (hheavy : 1 ≤ (rate : ℝ) * mu),
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | ∀ M : ℝ, ∀ T : ℝ≥0,
        ∃ t : ℝ≥0, T ≤ t ∧
          M < queueWorkload arrival claims w t ω}).toReal = 1

/-- Source obligation: Kyprianou.Ch01.mckeanBrownianPutOptimal. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_mckeanBrownianPutOptimal : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)),
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    let tauStar : Ω → WithTop ℝ≥0 :=
      firstLowerPassage X x barrier
    0 < phi ∧
      IsNaturalStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) ∧
      HasDerivAt (mckeanValue K barrier phi)
        (-Real.exp barrier) barrier

/-- Source obligation: Kyprianou.Ch01.branchingLaplaceExponential. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_branchingLaplaceExponential : Prop :=
  ∀ (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi),
    ∀ (y : ℕ) (t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingLaplace law y t phi =
        Real.exp (-(y : ℝ) * branchingU law t phi)

/-- Source obligation: Kyprianou.Ch01.branchingLaplaceSemigroup. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_branchingLaplaceSemigroup : Prop :=
  ∀ (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hmarkov : IsPopulationMarkovSemigroup law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi ∧
        branchingLaplace law 1 t phi < 1),
    ∀ (s t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingU law (s + t) phi =
        branchingU law s (branchingU law t phi)

/-- Source obligation: Kyprianou.Ch01.gammaLevyExponent. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_gammaLevyExponent : Prop :=
  ∀ (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta),
    IsLevyMeasure (gammaLevyMeasure alpha beta) ∧
      gammaLevyMeasure alpha beta Set.univ = ⊤ ∧
      ∀ theta : ℝ,
        IntegrableOn (fun x : ℝ =>
          ((1 : ℂ) - Complex.exp (Complex.I * (theta : ℂ) * (x : ℂ))) *
            ((beta : ℂ) * Complex.exp (-(alpha : ℂ) * (x : ℂ)) / (x : ℂ)))
          (Set.Ioi (0 : ℝ)) ∧
        (∫ x in Set.Ioi (0 : ℝ),
          ((1 : ℂ) - Complex.exp (Complex.I * (theta : ℂ) * (x : ℂ))) *
            ((beta : ℂ) * Complex.exp (-(alpha : ℂ) * (x : ℂ)) / (x : ℂ))
          ∂volume) =
            (beta : ℂ) *
              Complex.log (1 - Complex.I * (theta : ℂ) / (alpha : ℂ))

/-- Source obligation: Kyprianou.Ch01.gammaProcessStrictIncreaseAndInfiniteActivity. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_gammaProcessStrictIncreaseAndInfiniteActivity : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (hAlpha : 0 < alpha) (hBeta : 0 < beta)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hGammaLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ))),
    (∀ᵐ ω ∂P, StrictMono (fun t : ℝ≥0 => X t ω)) ∧
      IsLevyMeasure (Kyprianou.Ch01.gammaLevyMeasure alpha beta) ∧
      (Kyprianou.Ch01.gammaLevyMeasure alpha beta)
        (Set.Ioi (0 : ℝ)) = (⊤ : ℝ≥0∞)

/-- Source obligation: Kyprianou.Ch01.inverseGaussianFirstPassageLaplace. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_inverseGaussianFirstPassageLaplace : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)),
    IsNaturalStoppingTime X (firstUpperPassage X s) ∧
      ∀ q : ℝ, 0 ≤ q →
        (∫ ω, passageLaplace (firstUpperPassage X s) q ω ∂P) =
          Real.exp (-(s * (Real.sqrt (b ^ 2 + 2 * q) - b)))

/-- Source obligation: Kyprianou.Ch01.inverseGaussianPassageLevySubordinator. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_inverseGaussianPassageLevySubordinator : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)),
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    (∀ s : ℝ≥0, 0 < s →
      ∀ᵐ ω ∂P,
        Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤) ∧
      ProbabilityTheory.IsLevyProcess T P ∧
      (∀ (s : ℝ≥0) (q : ℝ), 0 < s → 0 ≤ q →
        Integrable (fun ω => Real.exp (-q * T s ω)) P ∧
        (∫ ω, Real.exp (-q * T s ω) ∂P) =
          Real.exp (-(s : ℝ) *
            (Real.sqrt (b ^ 2 + 2 * q) - b)))

/-- Source obligation: Kyprianou.Ch01.strictStableTimeScaling. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_strictStableTimeScaling : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (alpha : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (hX : IsLevyProcess X P)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (Psi : ℝ → ℂ)
    (hchar : ∀ (t : ℝ≥0) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (-((t : ℝ) : ℂ) * Psi xi))
    (hhomog : ∀ c : ℝ, 0 < c → ∀ xi : ℝ,
      Psi (c * xi) = ((c ^ alpha : ℝ) : ℂ) * Psi xi),
    ∀ (scale t : ℝ≥0), 0 < scale →
      P.map (X (scale * t)) =
        P.map (fun ω => (scale : ℝ) ^ (1 / alpha) * X t ω)

/-- Source obligation: Kyprianou.Ch01.branchingLaplaceEvolution. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_branchingLaplaceEvolution : Prop :=
  ∀ (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hrate : 0 < rate)
    (hbranch : HasBranchingProperty law)
    (hsemigroup : IsPopulationMarkovSemigroup law)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ =>
          branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0),
    ∀ q : ℝ, 0 < q →
      branchingU law 0 q = q ∧
      ∀ t : ℝ≥0,
        HasDerivWithinAt
          (fun s : ℝ => branchingU law (Real.toNNReal s) q)
          (branchingMechanism rate offspring (branchingU law t q))
          (Set.Ici 0) (t : ℝ)

/-- Source obligation: Kyprianou.Ch01.independentLevySum. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_independentLevySum : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P),
    IsLevyProcess (fun t ω => X t ω + Y t ω) P

/-- Source obligation: Kyprianou.Ch01.lampertiForwardClockRecovery. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_lampertiForwardClockRecovery : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ≥0 → Ω → ℕ)
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun s : ℝ≥0 => Y s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (Y t ω)))
    (hlocalint : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ))
    (hpositive : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < populationExtinction Y ω →
        0 < Y t ω),
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < populationExtinction Y ω →
      branchingToPoisson Y
          (Real.toNNReal (branchingOccupation Y t ω)) ω = Y t ω

/-- Source obligation: Kyprianou.Ch01.lampertiReverseClockRecovery. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_lampertiReverseClockRecovery : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℤ)
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun s : ℝ≥0 => X s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (X t ω)))
    (hlocalint : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ =>
          if 0 < X (Real.toNNReal s) ω then
            1 / (X (Real.toNNReal s) ω : ℝ)
          else 0)
        volume 0 (t : ℝ)),
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∀ s : ℝ≥0, s ≤ t → 0 < X s ω) →
        compoundPoissonToBranching X
          (Real.toNNReal
            (reciprocalOccupation X t ω).toReal) ω = X t ω

/-- Source obligation: Kyprianou.Ch01.characteristicExponentialMartingale. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_characteristicExponentialMartingale : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ t : ℝ≥0,
      charFun (P.map (X t)) theta =
        Complex.exp (-((t : ℝ) : ℂ) * Psi)),
    let M : ℝ≥0 → Ω → ℂ :=
      fun t ω =>
        Complex.exp (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
          ((t : ℝ) : ℂ) * Psi)
    ∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
          (∫ ω in A, M t ω ∂P) =
            (∫ ω in A, M s ω ∂P)

/-- Source obligation: Kyprianou.Ch01.brownianFirstPassageStableHalf. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_brownianFirstPassageStableHalf : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsLinearBrownian P B 1 0)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t)),
    ∀ (s q : ℝ), 0 < s → 0 ≤ q →
      Integrable (passageLaplace (firstUpperPassage B s) q) P ∧
      (∫ ω, passageLaplace (firstUpperPassage B s) q ω ∂P) =
        Real.exp (-s * Real.sqrt (2 * q))

/-- Source obligation: Kyprianou.Ch01.lampertiCompoundPoissonToBranchingLaw. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_lampertiCompoundPoissonToBranchingLaw : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (hFiniteMean : Summable
      (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k),
    ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      law y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}

/-- Source obligation: Kyprianou.Ch01.geometricLawInfinitelyDivisible. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_geometricLawInfinitelyDivisible : Prop :=
  ∀ (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (G : Measure ℕ) [IsProbabilityMeasure G]
    (hGeom : ∀ k : ℕ,
      G {k} = ENNReal.ofReal (p * (1 - p) ^ k)),
    LevyFoundations.isInfinitelyDivisibleLaw
      (G.map (fun k : ℕ => (k : ℝ)))

/-- Source obligation: Kyprianou.Ch01.geometricStoppedRandomWalkInfinitelyDivisible. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_geometricStoppedRandomWalkInfinitelyDivisible : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P),
    LevyFoundations.isInfinitelyDivisibleLaw
      (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω))

/-- Source obligation: Kyprianou.Ch01.stableGammaIntegral. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_stableGammaIntegral : Prop :=
  ∀ (alpha u : ℝ)
    (hα0 : 0 < alpha) (hα1 : alpha < 1)
    (hu : 0 < u),
    IntegrableOn
      (fun x : ℝ =>
        (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) ∧
      (∫ x in Set.Ioi (0 : ℝ),
        (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1) ∂volume) =
          Real.Gamma (-alpha) * u ^ alpha

/-- Source obligation: Kyprianou.Ch01.randomWalkReversalLadderIdentity. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_randomWalkReversalLadderIdentity : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ i : ℕ, Measurable (increment i))
    (hindep : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hLaw : ∀ i : ℕ, HasLaw (increment i) jumpLaw P),
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    ∀ (n : ℕ), 1 ≤ n →
      ∀ B : Set ℝ, MeasurableSet B →
        P {ω | S n ω ∈ B ∧
          ∀ j : ℕ, j < n → S j ω < S n ω} =
        P {ω | S n ω ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω}

/-- Source obligation: Kyprianou.Ch01.mg1IdleRegulatorIdentity. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_mg1IdleRegulatorIdentity : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hRate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPositiveClaims : F (Set.Iic (0 : ℝ)) = 0),
    ∀ w : ℝ, 0 ≤ w →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        (∫ s in (0 : ℝ)..(t : ℝ),
          (if queueWorkload arrival claims w (Real.toNNReal s) ω = 0
            then (1 : ℝ) else 0) ∂volume) =
        max
          ((sSup {x : ℝ | ∃ s : ℝ≥0,
            s ≤ t ∧
              x = riskSurplus arrival claims 1 0 s ω}) - w) 0

/-- Source obligation: Kyprianou.Ch01.lampertiBranchingToCompoundPoissonPathLaw. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_lampertiBranchingToCompoundPoissonPathLaw : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hFiniteOffspringMean : Summable
      (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
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

/-- Source obligation: Kyprianou.Ch01.generalFrullaniImproper. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_generalFrullaniImproper : Prop :=
  ∀ (f f' : ℝ → ℝ) (fInfinity : ℝ)
    (hfderiv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hfprime : Continuous f')
    (hlimit : Tendsto f atTop (nhds fInfinity))
    (a b : ℝ) (ha : 0 < a) (hab : a < b),
    Tendsto
      (fun R : ℝ =>
        ∫ x in (1 / R)..R,
          (f (a * x) - f (b * x)) / x)
      atTop
      (nhds ((f 0 - fInfinity) * Real.log (b / a)))

/-- Source obligation: Kyprianou.Ch01.stableAlphaOneCosineIntegral. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_stableAlphaOneCosineIntegral : Prop :=
  IntegrableOn
      (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (1 - Real.cos r) / r ^ 2 ∂volume) = Real.pi / 2

/-- Source obligation: Kyprianou.Ch01.stableAlphaAboveOneIntegral. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_stableAlphaAboveOneIntegral : Prop :=
  ∀ (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2),
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
        ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))

/-- Source obligation: Kyprianou.Ch01.inverseGaussianDensityLaplace. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_inverseGaussianDensityLaplace : Prop :=
  ∀ (s b : ℝ) (hs : 0 < s) (hb : 0 < b),
    let IG : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    IG Set.univ = 1 ∧
    ∀ q : ℝ, 0 ≤ q →
      Integrable (fun x : ℝ => Real.exp (-q * x)) IG ∧
      (∫ x, Real.exp (-q * x) ∂IG) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b))

/-- Source obligation: Kyprianou.Ch01.brownianDiscountedLowerPassage. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_brownianDiscountedLowerPassage : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q a : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (ha : 0 ≤ a)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)),
    Integrable
      (passageLaplace (firstLowerPassage X 0 (-a)) q) P ∧
    (∫ ω, passageLaplace (firstLowerPassage X 0 (-a)) q ω ∂P) =
      Real.exp (-a * ((Real.sqrt
        (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2))

/-- Source obligation: Kyprianou.Ch01.queueLaplaceExponentStrictConvexAndRoot. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_queueLaplaceExponentStrictConvexAndRoot : Prop :=
  ∀ (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu),
    StrictConvexOn ℝ (Set.Ici (0 : ℝ))
      (queueLaplaceExponent rate F) ∧
    queueLaplaceExponent rate F 0 = 0 ∧
    Tendsto (queueLaplaceExponent rate F) atTop atTop ∧
    ((∃ theta : ℝ, 0 < theta ∧
      queueLaplaceExponent rate F theta = 0) ↔
        1 < (rate : ℝ) * mu) ∧
    (∀ theta theta' : ℝ,
      0 < theta → 0 < theta' →
      queueLaplaceExponent rate F theta = 0 →
      queueLaplaceExponent rate F theta' = 0 →
      theta = theta')

/-- Source obligation: Kyprianou.Ch01.queueExponentialMartingaleAndPassage. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_queueExponentialMartingaleAndPassage : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPos : F (Set.Iic (0 : ℝ)) = 0)
    (hIntegrable : Integrable (fun z : ℝ => z) F)
    (mu : ℝ) (hMean : (∫ z, z ∂F) = mu)
    (hOverload : 1 < (rate : ℝ) * mu)
    (theta : ℝ) (hTheta : 0 < theta)
    (hRoot : queueLaplaceExponent rate F theta = 0),
    let X : ℝ≥0 → Ω → ℝ := riskSurplus arrival claims 1 0
    let M : ℝ≥0 → Ω → ℝ :=
      fun t ω =>
        Real.exp (theta * X t ω -
          queueLaplaceExponent rate F theta * (t : ℝ))
    (∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
        (∫ ω in A, M t ω ∂P) =
          (∫ ω in A, M s ω ∂P)) ∧
    ∀ x : ℝ, 0 < x →
      (P {ω | ∃ t : ℝ≥0, 0 < t ∧ x < X t ω}).toReal =
        Real.exp (-theta * x)

/-- Source obligation: Kyprianou.Ch01.mckeanBarrierCalculusOptimality. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_mckeanBarrierCalculusOptimality : Prop :=
  ∀ (K phi x : ℝ) (hK : 0 < K) (hphi : 0 < phi),
    let b : ℝ := Real.log (K * phi / (1 + phi))
    let barrierPayoff : ℝ → ℝ := fun a =>
      (K - Real.exp a) * Real.exp (-phi * (x - a))
    HasDerivAt barrierPayoff 0 b ∧
    (∀ a : ℝ, a ≤ x →
      barrierPayoff a ≤ mckeanValue K b phi x) ∧
    barrierPayoff (min x b) = mckeanValue K b phi x

/-- Source obligation: Kyprianou.Ch01.stableAlphaOneLogPhase. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_stableAlphaOneLogPhase : Prop :=
  ∃ k : ℝ, ∀ z : ℝ, 0 < z →
      IntegrableOn
        (fun r : ℝ =>
          ((1 : ℂ) -
              Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
            ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) -
            Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
          Complex.I * (((z * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)
          ∂volume) =
        (((Real.pi * z / 2 : ℝ) : ℂ)) +
          Complex.I * (((z * Real.log z : ℝ) : ℂ)) -
          Complex.I * (((k * z : ℝ) : ℂ))

/-- Source obligation: Kyprianou.Ch01.inverseGaussianLevyExponent. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_inverseGaussianLevyExponent : Prop :=
  ∀ (b : ℝ) (hb : 0 < b),
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    IsLevyMeasure Pi ∧
      ∀ theta : ℝ,
        IntegrableOn
          (fun x : ℝ => (1 - Complex.exp
              (Complex.I * ((theta * x : ℝ) : ℂ))))
          (Set.Ioi (0 : ℝ)) Pi ∧
        (∫ x in Set.Ioi (0 : ℝ),
          ((1 : ℂ) -
            Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
          Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
            2 * Complex.I * (theta : ℂ)) - (b : ℂ)

/-- Source obligation: Kyprianou.Ch01.firstWeakDescendingRenewalPotential. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_firstWeakDescendingRenewalPotential : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (hindep : iIndepFun increment P)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hLaw : ∀ n : ℕ, HasLaw (increment n) mu P),
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    ∀ B : Set ℝ, MeasurableSet B →
      B ⊆ Set.Iic (0 : ℝ) →
        P {ω | ∃ n : ℕ, 1 ≤ n ∧ S n ω ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j < n → 0 < S j ω} =
          ∑' n : ℕ,
            ∫⁻ y : ℝ, mu
              ((fun z : ℝ => y + z) ⁻¹' B) ∂
              (Measure.map (S n)
                (P.restrict {ω | ∀ j : ℕ,
                    1 ≤ j → j ≤ n → 0 < S j ω}))

/-- Source obligation: Kyprianou.Ch01.riskEmbeddedRandomWalkTails. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_riskEmbeddedRandomWalkTails : Prop :=
  ∀ (beta : ℝ) (hbeta : 0 < beta)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hClaims : F (Set.Iic (0 : ℝ)) = 0),
    let Ebeta : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun e : ℝ => ENNReal.ofReal
          (beta * Real.exp (-beta * e)))
    let mu : Measure ℝ :=
      (Ebeta.prod F).map
        (fun pair : ℝ × ℝ => pair.1 - pair.2)
    (∀ z : ℝ, 0 ≤ z →
      (mu (Set.Ioi z)).toReal =
        Real.exp (-beta * z) *
          (∫ u : ℝ, Real.exp (-beta * u) ∂F)) ∧
    (∀ z : ℝ, 0 < z →
      (mu (Set.Iio (-z))).toReal =
        (∫ e : ℝ, (F (Set.Ioi (e + z))).toReal ∂Ebeta))

/-- Source obligation: Kyprianou.Ch01.exponentialAscendingLadderRenewal. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_exponentialAscendingLadderRenewal : Prop :=
  ∀ (beta : ℝ) (hbeta : 0 < beta),
    let mu : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal
          (beta * Real.exp (-beta * x)))
    ∀ x : ℝ, 0 ≤ x →
      (∑' n : ℕ,
        ((QueueingFundamentals.MG1.convPow mu n)
          (Set.Icc (0 : ℝ) x)).toReal) = 1 + beta * x

/-- Source obligation: Kyprianou.Ch01.brownianPassageHalfStableLevyProcess. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_brownianPassageHalfStableLevyProcess : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω)),
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        (match Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    (∀ s : ℝ≥0, 0 < s →
      ∀ᵐ ω ∂P,
        Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω ≠ ⊤) ∧
    ProbabilityTheory.IsLevyProcess T P ∧
    (∀ (s : ℝ≥0) (q : ℝ), 0 < s → 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * T s ω)) P ∧
      (∫ ω, Real.exp (-q * T s ω) ∂P) =
        Real.exp (-(s : ℝ) * Real.sqrt (2 * q)))

end Kyprianou.Ch01


