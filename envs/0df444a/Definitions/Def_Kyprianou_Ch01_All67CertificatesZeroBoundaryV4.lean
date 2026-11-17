-- Prove2me | Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
-- name    : Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T23:39:06.036803+00:00
-- url     : https://prove2.me/theorems/e240f7dd-b912-4294-8496-c7b1fc45e2df
-- title:
--   Chapter 1 source certificates: all 67 obligations with explicit Brownian passage zero-level boundary

import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_MarkovProcess_V3H_Examples_BrownianMotion_c88465db
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Mathlib
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 MarkovProcess Real Complex Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u v u_1 u_2 u_3 u_4
namespace Kyprianou.Ch01

noncomputable def certificate_levyKhintchineLaw : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    ProbabilityTheory.IsInfinitelyDivisible μ ↔
      ∃ T : ProbabilityTheory.LevyKhintchineTriple,
        ∀ (ξ : ℝ), charFun μ ξ = Complex.exp (Kyprianou.Ch01.levyTripleExponent T ξ)

noncomputable def certificate_levy_khintchine_process_existsTargetedV2 : Prop :=
  ∀ (T : ProbabilityTheory.LevyKhintchineTriple),
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (μ.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) * Kyprianou.Ch01.levyTripleExponent T ξ)

noncomputable def certificate_compoundPoissonCharExponent : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_compoundPoissonInfinitelyDivisible : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0),
    IsInfinitelyDivisible
      (μ.map (compoundPoisson b τ Y (t : ℝ)))

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

noncomputable def certificate_mckeanBrownianPutOptimalRightContinuous : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
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
      IsNaturalRightStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) ∧
      HasDerivAt (mckeanValue K barrier phi)
        (-Real.exp barrier) barrier

noncomputable def certificate_branchingLaplaceExponential : Prop :=
  ∀ (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi),
    ∀ (y : ℕ) (t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingLaplace law y t phi =
        Real.exp (-(y : ℝ) * branchingU law t phi)

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

noncomputable def certificate_gammaProcessStrictIncreaseAndInfiniteActivity : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_inverseGaussianPassageLevySubordinatorZeroBoundaryV2 : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)),
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
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

noncomputable def certificate_strictStableTimeScaling : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_independentLevySum : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P),
    IsLevyProcess (fun t ω => X t ω + Y t ω) P

noncomputable def certificate_lampertiForwardClockRecovery : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_lampertiReverseClockRecovery : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_characteristicExponentialMartingale : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_brownianFirstPassageStableHalf : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : IsLinearBrownian P B 1 0)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t)),
    ∀ (s q : ℝ), 0 < s → 0 ≤ q →
      Integrable (passageLaplace (firstUpperPassage B s) q) P ∧
      (∫ ω, passageLaplace (firstUpperPassage B s) q ω ∂P) =
        Real.exp (-s * Real.sqrt (2 * q))

noncomputable def certificate_lampertiCompoundPoissonToBranchingLawNonexplosive : Prop :=
  ∀     {Ω : Type u} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
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
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω),
    ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      law y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}

noncomputable def certificate_geometricLawInfinitelyDivisible : Prop :=
  ∀ (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (G : Measure ℕ) [IsProbabilityMeasure G]
    (hGeom : ∀ k : ℕ,
      G {k} = ENNReal.ofReal (p * (1 - p) ^ k)),
    LevyFoundations.isInfinitelyDivisibleLaw
      (G.map (fun k : ℕ => (k : ℝ)))

noncomputable def certificate_geometricStoppedRandomWalkInfinitelyDivisible : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_randomWalkReversalLadderIdentity : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_mg1IdleRegulatorIdentity : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_stableAlphaOneCosineIntegral : Prop :=
  IntegrableOn
      (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (1 - Real.cos r) / r ^ 2 ∂volume) = Real.pi / 2

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

noncomputable def certificate_brownianDiscountedLowerPassage : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_queueExponentialMartingaleAndPassage : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_mckeanBarrierCalculusOptimality : Prop :=
  ∀ (K phi x : ℝ) (hK : 0 < K) (hphi : 0 < phi),
    let b : ℝ := Real.log (K * phi / (1 + phi))
    let barrierPayoff : ℝ → ℝ := fun a =>
      (K - Real.exp a) * Real.exp (-phi * (x - a))
    HasDerivAt barrierPayoff 0 b ∧
    (∀ a : ℝ, a ≤ x →
      barrierPayoff a ≤ mckeanValue K b phi x) ∧
    barrierPayoff (min x b) = mckeanValue K b phi x

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

noncomputable def certificate_firstWeakDescendingRenewalPotential : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
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

noncomputable def certificate_brownianPassageHalfStableLevyProcessZeroBoundaryV2 : Prop :=
  ∀ {Ω : Type u_4} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω)),
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω with
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

noncomputable def certificate_levyTripletExponentSignBridgeReviewed : Prop :=
  ∀ (T : ProbabilityTheory.LevyKhintchineTriple) (xi : ℝ),
-levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) +
      (((T.gaussianVariance : ℝ) * xi ^ 2 / 2 : ℝ) : ℂ) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure)

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

noncomputable def certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal : Prop :=
  ∀ {Ω : Type u_2} [inst : MeasurableSpace Ω] {E : Type u_3} [inst_1 : NormedAddCommGroup E]
  [@InnerProductSpace Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)]
  [inst_3 : MeasurableSpace E]
  [@BorelSpace E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      inst_3]
  [@SecondCountableTopology E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))]
  [@MeasurableAdd₂ E inst_3
      (@AddCommMagma.toAdd E
        (@AddCommSemigroup.toAddCommMagma E
          (@AddCommMonoid.toAddCommSemigroup E
            (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst_1)))))]
  {X : NNReal → Ω → E} {μ : @MeasureTheory.Measure Ω inst} [@MeasureTheory.IsProbabilityMeasure Ω inst μ],
  @ProbabilityTheory.IsLevyProcess Ω E inst inst_3
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst_1)) X μ →
    (∀ (t : NNReal), @Measurable Ω E inst inst_3 (X t)) →
      ∀ (t : NNReal),
        @ProbabilityTheory.IsInfinitelyDivisible E
          (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst_1)) inst_3
          (@MeasureTheory.Measure.map Ω E inst inst_3 (X t) μ)

noncomputable def certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul : Prop :=
  ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {E : Type u_3} [inst_1 : NormedAddCommGroup E]
  [inst_2 : @InnerProductSpace Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)]
  [inst_3 : MeasurableSpace E]
  [@BorelSpace E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      inst_3]
  [@SecondCountableTopology E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))]
  [@MeasurableAdd₂ E inst_3
      (@AddCommMagma.toAdd E
        (@AddCommSemigroup.toAddCommMagma E
          (@AddCommMonoid.toAddCommSemigroup E
            (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst_1)))))]
  {X : NNReal → Ω → E} {μ : @MeasureTheory.Measure Ω inst} [@MeasureTheory.IsProbabilityMeasure Ω inst μ]
  (h :
    @ProbabilityTheory.IsLevyProcess Ω E inst inst_3
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst_1)) X μ),
  (∀ (t : NNReal), @Measurable Ω E inst inst_3 (X t)) →
    ∀ (t : NNReal) (ξ : E),
      @Eq Complex
        (@MeasureTheory.charFun E inst_3
          (@InnerProductSpace.toInner Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)
            inst_2)
          (@MeasureTheory.Measure.map Ω E inst inst_3 (X t) μ) ξ)
        (Complex.exp
          (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) (↑↑t)
            (@ProbabilityTheory.IsLevyProcess.charExponent Ω E inst inst_3
              (@UniformSpace.toTopologicalSpace E
                (@PseudoMetricSpace.toUniformSpace E
                  (@SeminormedAddCommGroup.toPseudoMetricSpace E
                    (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
              (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst_1))
              (@InnerProductSpace.toInner Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)
                inst_2)
              X μ h ξ)))

noncomputable def certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : NNReal → Ω → ℕ} {rate : NNReal} {μ : Measure Ω},
∀ (h : IsPoissonProcess N rate μ)
    (hcadlag : ∀ᵐ ω ∂μ, IsCadlag (fun t => (N t ω : ℤ))),
IsLevyProcess (fun t ω => (N t ω : ℤ)) μ

noncomputable def certificate_reuse_levy_foundations_poissonLaw_infinitelyDivisible : Prop :=
  ∀ (r : ℝ≥0),
LevyFoundations.isInfinitelyDivisibleLaw
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ))

noncomputable def certificate_reuse_ProbabilityTheory_compoundPoisson_ae_isCadlag : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {b : ℝ} {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r),
∀ᵐ ω ∂μ, IsCadlag (fun t => compoundPoisson b τ Y t ω)

noncomputable def certificate_reuse_levy_foundations_compoundPoissonMarginalInfinitelyDivisible : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν']
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0) (b : ℝ) (t : ℝ≥0),
LevyFoundations.isInfinitelyDivisible
      (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ)))

noncomputable def certificate_reuse_MarkovProcess_isBrownianReal_brownianMotion : Prop :=
  ∀ (x : ℝ),
MarkovProcess.IsBrownianReal (fun (t : NNReal) (omega : ContinuousPath ℝ) ↦ omega t - x)
      (MarkovProcess.brownianMotion x)

noncomputable def certificate_brownianRealExponentialMartingale : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)),
let psi : ℝ := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
    let M : ℝ≥0 → Ω → ℝ :=
      fun t ω => Real.exp (theta * X t ω - psi * (t : ℝ))
    ∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
        (∫ ω in A, M t ω ∂P) = (∫ ω in A, M s ω ∂P)

noncomputable def certificate_brownianDiscountedUpperPassage : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)),
Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) =
      Real.exp (-x * ((Real.sqrt
        (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2))

noncomputable def certificate_firstUpperPassageNaturalRightStoppingContinuousV2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
        (X : ℝ≥0 → Ω → ℝ)
        (hMeas : ∀ t : ℝ≥0, Measurable (X t))
        (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
        (s : ℝ) (hs : 0 < s),
    Kyprianou.Ch01.IsNaturalRightStoppingTime X
      (Kyprianou.Ch01.firstUpperPassage X s)

noncomputable def certificate_stableGammaIntegralComplexExtensionV2 : Prop :=
  ∀ (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
        (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0),
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (w * (r : ℂ)) - 1) *
          ((r ^ (-alpha - 1) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha - 1) : ℝ)) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w))

noncomputable def certificate_inverseGaussianFullLevyTripletV2 : Prop :=
  ∀ (s b : ℝ) (hs : 0 < s) (hb : 0 < b),
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))));
    let drift : ℝ :=
      -(2 * s / b) *
        (∫ y in (0 : ℝ)..b,
          Real.exp (-(y ^ 2 / 2)) / Real.sqrt (2 * Real.pi) ∂volume);
    (s * ∫ x in Set.Ioo (0 : ℝ) (1 : ℝ), x ∂Pi) = -drift ∧
      ∃ T : ProbabilityTheory.LevyKhintchineTriple,
        T.gaussianVariance = 0 ∧
          T.levyMeasure = (ENNReal.ofReal s) • Pi ∧
          T.drift = drift

noncomputable def certificate_brownianFirstPassageStableParametersV2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ)
        (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
        (hMeas : ∀ t : ℝ≥0, Measurable (B t))
        (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω))
        (s : ℝ) (hs : 0 < s),
    let T : Ω → ℝ :=
      fun ω => match Kyprianou.Ch01.firstUpperPassage B s ω with
        | none => 0
        | some t => (t : ℝ);
    ∀ xi : ℝ,
      charFun (P.map T) xi =
        Complex.exp
          (-(((s * Real.sqrt (|xi|) : ℝ) : ℂ) *
            (1 - Complex.I *
              (((if 0 < xi then (1 : ℝ)
                  else if xi < 0 then -1 else 0) : ℝ) : ℂ))))

noncomputable def certificate_mg1IdleJointLawsExercise19vV2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (arrival claims : ℕ → Ω → ℝ)
        (rate : ℝ≥0) (hrate : 0 < rate)
        (F : Measure ℝ) [IsProbabilityMeasure F]
        (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
        (hPositive : F (Set.Iic (0 : ℝ)) = 0)
        (hMean : Integrable (fun x : ℝ => x) F)
        (mu : ℝ) (hMu : (∫ x, x ∂F) = mu)
        (hOverloaded : 1 < (rate : ℝ) * mu)
        (theta : ℝ) (hTheta : 0 < theta)
        (hRoot : queueLaplaceExponent rate F theta = 0)
        (w : ℝ) (hw : 0 ≤ w),
    let busyEnds : Set Ω :=
      {ω | ∃ t : ℝ≥0, 0 < t ∧
        w < riskSurplus arrival claims 1 0 t ω};
    (P {ω | ω ∉ busyEnds ∧
      totalIdleTime arrival claims w ω = 0}).toReal =
        1 - Real.exp (-theta * w) ∧
      ∀ x : ℝ, 0 ≤ x →
        (P {ω | ω ∈ busyEnds ∧
          (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ∧
          totalIdleTime arrival claims w ω ≤ ENNReal.ofReal x}).toReal =
        Real.exp (-theta * w) * (1 - Real.exp (-theta * x))
end Kyprianou.Ch01


