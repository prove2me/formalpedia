-- Prove2me | Definitions.Def_Kyprianou_Ch08_GOUAndSpecial
-- name    : Kyprianou_Ch08_GOUAndSpecial
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T07:16:34.234301+00:00
-- url     : https://prove2.me/theorems/ccfeeba8-d4ea-45f5-b76a-f62281d31e1f
-- title:
--   Kyprianou Chapter 8: GOUAndSpecial
-- statement:
--   Adapted cadlag generalised Ornstein-Uhlenbeck Ito integral, GOU first passage, H transforms and valid positive-discount and zero-discount boundary conditions, stable processes and risk-system data.
-- source:
--   Kyprianou (2006), first edition, Chapter 8, original physical pages 219-246; source SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_ProcessAndExponent
import Definitions.Def_Kyprianou_Ch08_PassageAndPotentials
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08

/-- Left-endpoint stochastic Riemann sums for
∫_0^t exp(lambda*s) dX_s. The denominator n+1 prevents a zero mesh.
For an actual Levy semimartingale these converge in probability to
the Ito integral. No expression in Theorem 8.12 is assumed. -/
noncomputable def gouItoApprox {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (reversion : ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Real.exp (reversion * (t : ℝ) * ((k : ℝ) / (n + 1))) *
      (X (t * ((↑(k + 1) : ℝ≥0) / (↑(n + 1) : ℝ≥0))) ω -
       X (t * ((↑k : ℝ≥0) / (↑(n + 1) : ℝ≥0))) ω)

/-- A fixed-time stochastic Ito integral is a convergence-in-probability
limit of left sums against THIS X and THIS probability law. Values on
a null event are immaterial. Existence and jointly adapted modification
are genuine open construction obligations, not assumptions of 8.12. -/
def IsGouItoIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (reversion : ℝ) (I : ℝ≥0 → Ω → ℝ) : Prop :=
  0 < reversion ∧
  ∀ (t : ℝ≥0) (eps : ℝ), 0 < eps →
    Filter.Tendsto
      (fun n : ℕ =>
        P {ω | eps ≤ |gouItoApprox X reversion n t ω - I t ω|})
      Filter.atTop (nhds (0 : ENNReal))

/-- Càdlàg, as one probability-one assertion quantifying over EVERY
time, not a family of separately almost-sure fixed-time assertions.
Right-continuity is essential to exclude random-time spikes. -/
def HasAlmostSureCadlagIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
    ContinuousWithinAt (fun s : ℝ≥0 => I s ω) (Set.Ici t) t ∧
    (0 < t → ∃ left : ℝ,
      Filter.Tendsto (fun s : ℝ≥0 => I s ω)
        (nhdsWithin t (Set.Iio t)) (nhds left))

/-- Adaptedness is with respect to the actual source filtration, not
a free sigma-algebra unrelated to the Levy driver. -/
def HasGOUAdaptedIntegral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (I : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t : ℝ≥0, @Measurable Ω ℝ (ℱ t) inferInstance (I t)

/-- Right-continuity of the augmented filtration, expressed through
the sigma-algebras of events at all strictly later times. -/
def IsGOURightContinuousFiltration {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ) : Prop :=
  ∀ (t : ℝ≥0) (A : Set Ω),
    @MeasurableSet Ω (ℱ t) A ↔
      ∀ s : ℝ≥0, t < s → @MeasurableSet Ω (ℱ s) A

/-- A genuine GOU candidate requires a single càdlàg and adapted
stochastic-integral version of the original Levy driver. In particular,
J_t=I_t+10*1_{t=U} with continuously distributed U is excluded:
it agrees at every deterministic t a.s. but is not right-continuous at U.
Constructing a version from the source hypotheses remains a theorem goal. -/
structure GOUInput (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  driver : SpectrallyNegativeModel Ω P
  meanReversion : ℝ
  positiveMeanReversion : 0 < meanReversion
  filtration : Filtration ℝ≥0 mΩ
  filtrationIsCompletedNatural :
    HasCompletedNaturalFiltration P driver filtration
  filtrationRightContinuous :
    IsGOURightContinuousFiltration filtration
  stochasticIntegral : ℝ≥0 → Ω → ℝ
  integralIsIto :
    IsGouItoIntegral P driver.X meanReversion stochasticIntegral
  integralAdapted :
    HasGOUAdaptedIntegral filtration stochasticIntegral
  integralCadlag :
    HasAlmostSureCadlagIntegral P stochasticIntegral

/-- Formula (8.33), using the actual original Levy driver and
the convergence-in-probability certified stochastic integral. -/
noncomputable def GOUPath {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : GOUInput Ω P)
    (y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-M.meanReversion * (t : ℝ)) *
    (y + M.stochasticIntegral t ω)

/-- Strict GOU first passage, zero payoff on infinite crossing time. -/
noncomputable def GOUExit {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : GOUInput Ω P)
    (y a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  tauPlus (GOUPath M y) a ω

/-- Construction and representative selection are a full existence
obligation on the actual model, with no exit formula in the premises. -/
def HasGOUConstruction {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (reversion : ℝ) : Prop :=
  0 < reversion ∧
  ∃ M : GOUInput Ω P, M.driver = D ∧ M.meanReversion = reversion

/-- Process versions are indistinguishable when one null set suffices
for equality at all times, rather than separately at each t. -/
def GOUIndistinguishable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I J : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0, I t ω = J t ω

/-- Explicit OPEN uniqueness theorem obligation. Right-continuous paths
agree indistinguishably when their values agree a.s. at every
deterministic time: prove via a countable dense set of rational times.
This named obligation must be proved before treating exit laws of any
two constructed GOU versions as identical. -/
def GOUVersionUniquenessObligation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) : Prop :=
  ∀ I J : ℝ≥0 → Ω → ℝ,
    HasAlmostSureCadlagIntegral P I →
    HasAlmostSureCadlagIntegral P J →
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, I t ω = J t ω) →
    GOUIndistinguishable P I J

/-- Distinct versions of the same Levy process and rate have identical
upcrossing times a.s. once process indistinguishability is available.
No hitting identity is included in the model assumptions. -/
def GOUExitVersionLawObligation {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] : Prop :=
  ∀ (M N : GOUInput Ω P) (y a : ℝ),
    M.driver = N.driver →
    M.meanReversion = N.meanReversion →
    GOUIndistinguishable P M.stochasticIntegral N.stochasticIntegral →
    ∀ᵐ ω ∂P, GOUExit M y a ω = GOUExit N y a ω

/-- H^(nu)(x), for lambda>0, nu>0, eq. (8.34).
Well-definedness at v=0 and integrability at infinity must be proved.
Do not use the ratio asserted by Theorem 8.12 as a definition. -/
noncomputable def Htransform (ψ : ℝ → ℝ)
    (reversion ν x : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    Real.exp (x * u -
      (1 / reversion) * (∫ v in (0 : ℝ)..u, ψ v / v)) *
      u ^ (ν - 1 : ℝ) ∂volume

/-- Actual H integrability obligation for nu>0 and lambda>0.
This prevents the totalised real integral from silently substituting zero
for a divergent, extended-real improper integral. -/
def HIsIntegrable (ψ : ℝ → ℝ) (reversion ν x : ℝ) : Prop :=
  0 < reversion ∧ 0 < ν ∧
  IntegrableOn
    (fun u : ℝ => Real.exp (x * u -
        (1 / reversion) * (∫ v in (0 : ℝ)..u, ψ v / v)) * u ^ (ν - 1))
    (Set.Ioi (0 : ℝ)) volume

/-- The book defines H^(nu) for nu>0. The positive-theta ratio
requires BOTH improper H integrals to converge and the denominator to
be nonzero. These are conclusions to establish under Theorem 8.12's
standing assumptions, never extra standing hypotheses. -/
def IsGOUPositiveHDomain (ψ : ℝ → ℝ)
    (reversion θ y a : ℝ) : Prop :=
  0 < reversion ∧ 0 < θ ∧
  HIsIntegrable ψ reversion (θ / reversion) y ∧
  HIsIntegrable ψ reversion (θ / reversion) a ∧
  Htransform ψ reversion (θ / reversion) a ≠ 0

/-- Ratio for θ>0, only to be used once IsGOUPositiveHDomain
has been established. Never instantiate this as H^(0)/H^(0). -/
noncomputable def GOUPositiveHRatio (ψ : ℝ → ℝ)
    (reversion θ y a : ℝ) : ℝ :=
  Htransform ψ reversion (θ / reversion) y /
    Htransform ψ reversion (θ / reversion) a

/-- The zero-transform boundary is a separate right-limit THEOREM
OBLIGATION. The target p is the actual zero-discount first-passage
expectation, including the zero payoff for infinite passage.
There is no totalised H^(0) and no 0/0 convention. -/
def IsGOUZeroHBoundary (ψ : ℝ → ℝ)
    (reversion y a p : ℝ) : Prop :=
  (∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Ioi 0),
    IsGOUPositiveHDomain ψ reversion θ y a) ∧
  Filter.Tendsto
    (fun θ : ℝ => GOUPositiveHRatio ψ reversion θ y a)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds p)

/-- Source-strength conclusion package for Theorem 8.12 once a
canonical GOU process has been constructed from the driver. Crucially
positive-θ integrability and the θ=0 boundary are to be PROVED, not
assumed. The theorem must also prove HasGOUConstruction from its own
source standing conditions rather than quantify over a free version. -/
def IsGOUTheorem812TransformConclusion {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (M : GOUInput Ω P) (ψ : ℝ → ℝ) (y a : ℝ) : Prop :=
  (∀ θ : ℝ, 0 < θ →
    IsGOUPositiveHDomain ψ M.meanReversion θ y a ∧
    (∫ ω, discountedAt θ (GOUExit M y a ω) ∂P) =
      GOUPositiveHRatio ψ M.meanReversion θ y a) ∧
  IsGOUZeroHBoundary ψ M.meanReversion y a
    (∫ ω, discountedAt 0 (GOUExit M y a ω) ∂P)

/-- A stable spectrally-negative Laplace exponent for 1<alpha<=2
is c*beta^alpha on beta>=0. The domain is recorded separately. -/
noncomputable def stableLaplace (c α β : ℝ) : ℝ :=
  c * β ^ α

/-- Canonical one-parameter Mittag-Leffler series E_alpha(z), using the
pinned Mathlib Real.Gamma function, α>0. The t-sum converges for
positive alpha; its analytic convergence proof is an open obligation. -/
noncomputable def mittagLeffler (α z : ℝ) : ℝ :=
  ∑' n : ℕ, z ^ n / Real.Gamma (1 + α * n)

/-- Valid parameter domain and actual summability obligation for E_alpha. -/
def MittagLefflerSummable (α z : ℝ) : Prop :=
  0 < α ∧ Summable (fun n : ℕ =>
    z ^ n / Real.Gamma (1 + α * n))

/-- Height measure of excursions from the supremum. The measure n may be
sigma-finite; its atomlessness is NOT an assumed smoothness theorem. -/
def HasNonnegativeHeightSupport (n : Measure ℝ) : Prop :=
  n (Set.Iio (0 : ℝ)) = 0

/-- Positive expected claim-size rate -int x Pi_i(dx); for the
printed Exercise 8.9(iii), E[X_1^(i)]-d_i has the OPPOSITE sign. -/
noncomputable def claimLossRate (componentJumpMeasure : Measure ℝ) : ℝ :=
  ∫ x in Set.Iio (0 : ℝ), -x ∂componentJumpMeasure

/-- Components are mutually distinguishable by their jump laws.
The independence, additive process decomposition and compensation
proofs must be supplied at the later exercise theorem. -/
structure CompetingClaimData (n : ℕ) where
  drift : Fin n → ℝ
  jumpLaw : Fin n → Measure ℝ

/-- The actual logarithmic large-negative-jump integrability
hypothesis of Theorem 8.12, without assuming its H-ratio conclusion. -/
def GOUHasLogJumpIntegrability (jumpMeasure : Measure ℝ) : Prop :=
  (∫⁻ x in Set.Iio (-1 : ℝ),
    ENNReal.ofReal (Real.log |x|) ∂jumpMeasure) < ⊤

/-- Spectrally negative stable-family domain and source exponent;
does not assert existence or a hitting theorem. -/
def IsStableExponent (ψ : ℝ → ℝ) (c α : ℝ) : Prop :=
  0 < c ∧ 1 < α ∧ α ≤ 2 ∧
  ∀ β : ℝ, 0 ≤ β → ψ β = stableLaplace c α β

/-- Positive stable subordinator, including index one-half in
Exercise 8.8. It has positive jumps and is a separate family from the
spectrally negative alpha-stable drivers of Exercise 8.2. -/
def IsStableSubordinatorExponent (phi : ℝ → ℝ)
    (c α : ℝ) : Prop :=
  0 < c ∧ 0 < α ∧ α < 1 ∧
  ∀ β : ℝ, 0 ≤ β → phi β = stableLaplace c α β

/-- A genuine excursion-height pushforward measure on the height axis.
Identification of the excursion law with the underlying Levy driver
remains a separate (nontrivial) construction. -/
structure ExcursionSystem (E : Type*) [MeasurableSpace E] where
  excursionLaw : Measure E
  height : E → ℝ
  heightMeasurable : Measurable height

noncomputable def excursionHeightMeasure {E : Type*}
    [MeasurableSpace E] (S : ExcursionSystem E) : Measure ℝ :=
  Measure.map S.height S.excursionLaw

/-- Tagged component path decomposition for competing-risk exercises.
Claims, jump-process independence and compensation remain obligations. -/
structure CompetingRiskPathData (Ω : Type*) (n : ℕ) where
  total : ℝ≥0 → Ω → ℝ
  component : Fin n → ℝ≥0 → Ω → ℝ
  pathSum : ∀ (t : ℝ≥0) (ω : Ω),
    total t ω = ∑ i : Fin n, component i t ω

end Kyprianou.Ch08


