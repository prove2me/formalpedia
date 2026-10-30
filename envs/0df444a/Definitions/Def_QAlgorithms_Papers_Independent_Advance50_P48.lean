-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P48
-- name    : QAlgorithms_Papers_Independent_Advance50_P48
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:01:59.354433+00:00
-- url     : https://prove2.me/theorems/e2eaf565-c38b-4821-923f-610b4562a3b1
-- title:
--   Definitions for Gaussian quantum discord
-- statement:
--   The objects the formalized statements of *Gaussian quantum discord* (arXiv:1003.3207) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OneKernel`: PDF pp.1--2: one complete oscillator, with no photon cutoff.
--   - `TwoKernel`: PDF pp.1--2: the completed two-oscillator number basis.
--   - `IsDiscordCovariance`: PDF p.2: finite real symmetric covariance with sigma+i Omega/2>=0.
--   - `weylArg`: PDF p.2: exp(i(qx q+px p))=D((-px+i qx)/sqrt(2)).
--   - `characteristicOne`: PDF pp.1--2: actual one-mode Weyl trace; the density precedes D.
--   - `characteristicTwo`: PDF p.2: actual two-mode Weyl trace on trace-class inputs.
--   - `stateGaussianCharacteristic`: PDF p.2: Gaussian characteristic, vacuum covariance I/2.
--   - `GaussianTwo`: PDF p.2: actual Gaussian density and its physical moments; no entropy, spectrum, optimization or Schur-complement identity is an assumption.
--   - `GaussianSeed`: PDF p.2: all centered normalized mixed or pure one-mode Gaussian seeds. Characteristic equality determines the covariance of the actual density.
--   - `swapOscillators`: PDF p.3: exchange physical parties, keeping the measurement convention.
--   - `oneModeVacuum`: PDF p.2: vacuum and the harmless conditional state on zero-Born-law sets.
--   - `seedEffect`: PDF p.2: actual D(z) rho_M D(z)^dagger density, relative to d^2z/pi.
--   - `unnormalizedConditional`: PDF p.2: Tr_B[rho (I tensor E)], with both retained A indices.
--   - `bornDensity`: PDF p.2: actual Born density, not an assumed Gaussian law.
--   - `posteriorDensity`: PDF p.2: normalize the posterior exactly when the Born density is positive.
--   - `seedLaw`: PDF p.2: actual Born outcome measure. Probability normalization is concluded.
--   - `seedAverage`: PDF p.2: integrated independent full-space von Neumann entropy.
--   - `gaussianConditionalInf`: PDF p.2: Gaussian conditional entropy optimized over actual seed densities. Empty infima are infinity, not real zero; finiteness is a conclusion below.
--   - `gaussianDiscordA`: PDF p.2: A-discord means measuring B. Finite real conversion is interpreted on the Gaussian domain, whose entropy finiteness is established below.
--   - `gaussianClassicalCorrelationA`: PDF pp.1--2: Gaussian extractable information from the same independent measurement optimization, retaining A and measuring B.
--   - `heterodyneEffect`: PDF pp.2--3: actual vacuum-seed heterodyne effect; no optimality is built in.
--   - `heterodyneAverage`: PDF pp.2--3: actual heterodyne conditional entropy.
--   - `NoncovariantMeasurement`: PDF pp.2--3: weakly normalized variable-seed POVMs, including their actual weights and reference measure. Normalization tests every finite superposition. This excludes arbitrary independently varying seeds integrated against plain dX dY.
--   - `variableEffect`: PDF p.3: actual weighted POVM density.
--   - `variableLaw`: PDF p.3: actual normalized Born law for a weakly normalized experiment.
--   - `variableAverage`: PDF p.3: outcome-averaged independent von Neumann entropy.
--   - `halfUnitEntropy`: PDF p.2: the entropy function, with Mathlib's 0*log(0)=0 convention.
--   - `covarianceModeBlock`: PDF p.2: covariance block on physical modes i,j.
--   - `covarianceInvariant`: PDF p.2: the four symplectic invariants in their source order.
--   - `symplecticDiscriminant`: PDF p.2: Delta=I1+I2+2I3.
--   - `symplecticMinus`: PDF p.2: the smaller and larger symplectic eigenvalues.
--   - `symplecticPlus`: PDF p.2: the plus branch uses the positive inner square-root sign.
--   - `gaussianSchurCovariance`: PDF p.2: Schur complement; physical B+M is invertible.
--   - `covarianceInf`: PDF p.2, Eq.(1): extended covariance-side infimum over physical seed covariances. The missing determinant in the printed h(sqrt(sigma_P)) is restored.
--   - `squeezeCoefficient`: PDF p.2: two-mode squeeze matrix obtained from exp(tanh(r) a^dagger b^dagger) cosh(r)^(-1-na-nb) exp(-tanh(r) ab). The finite sum is per coefficient, not a photon cutoff.
--   - `sts`: PDF p.2: constructed S(r)(nu(N1) tensor nu(N2))S(r)^dagger on the full oscillator space. Density, Gaussianity and the spectrum are conclusions.
--   - `squeezingPhotons`: PDF p.2: mean photons due to canonical nonnegative squeezing.
--   - `stsA`: PDF p.2: STS covariance parameter a.
--   - `stsB`: PDF p.2: STS covariance parameter b.
--   - `stsC`: PDF p.2: c1=-c2=c>=0, including pure inputs and r=0.
--   - `stsCovariance`: PDF p.2: the covariance constructed from the thermal/squeeze parameters.
--   - `closedDiscord`: PDF p.3, Eq.(2): no extra outer square root on the conditional argument.
--   - `tracePurity`: PDF p.3: actual trace purity Tr(rho^2), not a Gaussian determinant definition.
--   - `symmetricState`: PDF p.3: symmetric STS expressed in physical purity mu and PT eigenvalue t. It is used only when 0<mu<=1, t>0 and 2t sqrt(mu)<=1, or eventually as mu->0+.
--   - `SymmetricDomain`: PDF p.3: physical symmetric purity/PT parameter domain.
--   - `ptMinus`: PDF p.3: smaller symplectic eigenvalue after partial transposition.
--   - `totalPhotonEnergy`: PDF p.3: actual total occupation expectation, allowed to diverge off-domain.
--   - `teleportationFidelity`: PDF p.4: coherent-state teleportation fidelity as a function of the PT symplectic eigenvalue for the symmetric STS family discussed here.
--   - `infiniteEnergyDiscord`: PDF p.3: algebraically simplified fixed-PT infinite-energy limit.
--   - `dampedArgument`: PDF p.4: thermal damping acts on each physical Weyl coordinate.
--   - `ThermalEvolution`: PDF p.4: physical independent thermal-attenuator channel, specified on ALL density characteristic functions. This does not assume its covariance identity or the source's undefined/sign-ambiguous Lindblad L convention.
--   - `attenuatedCovariance`: PDF p.4: full covariance map, including off-standard Gaussian inputs.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, https://arxiv.org/abs/1003.3207v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

/-!
Giorda--Paris, arXiv:1003.3207v2. Complete oscillator number spaces,
hbar=1, vacuum I/2, interleaved (q_A,p_A,q_B,p_B), entropy in nats.
Discord below is independently defined by actual Born conditional densities.
The unrestricted local-unitary node is deferred; see HARD.md.
Compilation is pending the separate mechanical batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P48

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsTraceClassChannel IsSeparable productCoeff)
open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix coherentMeasure coherentCoefficient)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase twoModeStandard conditionalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight partialLeft)
open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g thermalProbability)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1--2: one complete oscillator, with no photon cutoff. -/
abbrev OneKernel := Matrix ℕ ℕ ℂ

/-- PDF pp.1--2: the completed two-oscillator number basis. -/
abbrev TwoKernel := Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ

/-- PDF p.2: finite real symmetric covariance with sigma+i Omega/2>=0. -/
def IsDiscordCovariance {n : ℕ} (V : Matrix (modePhase n) (modePhase n) ℝ) : Prop :=
  V.IsSymm ∧ Matrix.PosSemidef (fun i j => (V i j : ℂ) +
    Complex.I * ((canonicalOmega n i j / 2 : ℝ) : ℂ))

/-- PDF p.2: exp(i(qx q+px p))=D((-px+i qx)/sqrt(2)). -/
def weylArg (qx px : ℝ) : ℂ := (-(px : ℂ) + Complex.I * (qx : ℂ)) / (Real.sqrt 2 : ℂ)

/-- PDF pp.1--2: actual one-mode Weyl trace; the density precedes D. -/
def characteristicOne (rho : OneKernel) (x : modePhase 1 → ℝ) : ℂ :=
  ∑' m, ∑' n, rho m n * displacementMatrix (weylArg (x (0,0)) (x (0,1))) n m

/-- PDF p.2: actual two-mode Weyl trace on trace-class inputs. -/
def characteristicTwo (rho : TwoKernel) (x : modePhase 2 → ℝ) : ℂ :=
  ∑' m : ℕ × ℕ, ∑' n : ℕ × ℕ, rho m n *
    displacementMatrix (weylArg (x (0,0)) (x (0,1))) n.1 m.1 *
    displacementMatrix (weylArg (x (1,0)) (x (1,1))) n.2 m.2

/-- PDF p.2: Gaussian characteristic, vacuum covariance I/2. -/
def stateGaussianCharacteristic {n : ℕ} (d : modePhase n → ℝ)
    (V : Matrix (modePhase n) (modePhase n) ℝ) (x : modePhase n → ℝ) : ℂ :=
  Complex.exp (((-(∑ i, ∑ j, x i * V i j * x j) / 2 : ℝ) : ℂ) +
    Complex.I * ((∑ i, d i * x i : ℝ) : ℂ))

/-- PDF p.2: actual Gaussian density and its physical moments; no entropy,
spectrum, optimization or Schur-complement identity is an assumption. -/
def GaussianTwo (rho : TwoKernel) (d : modePhase 2 → ℝ)
    (V : Matrix (modePhase 2) (modePhase 2) ℝ) : Prop :=
  IsDensity rho ∧ IsDiscordCovariance V ∧ ∀ x,
    characteristicTwo rho x = stateGaussianCharacteristic d V x

/-- PDF p.2: all centered normalized mixed or pure one-mode Gaussian seeds.
Characteristic equality determines the covariance of the actual density. -/
structure GaussianSeed where
  density : OneKernel
  covariance : Matrix (modePhase 1) (modePhase 1) ℝ
  normalized : IsDensity density
  physical : IsDiscordCovariance covariance
  characteristic : ∀ x, characteristicOne density x =
    stateGaussianCharacteristic 0 covariance x

/-- Coordinate Borel structure, with physical seeds a measurable subspace.
It does not declare all functions of a seed measurable. -/
instance seedMeasurableSpace : MeasurableSpace GaussianSeed :=
  MeasurableSpace.comap (fun s : GaussianSeed => (s.density, s.covariance))
    ((borel OneKernel).prod (borel (Matrix (modePhase 1) (modePhase 1) ℝ)))

/-- PDF p.3: exchange physical parties, keeping the measurement convention. -/
def swapOscillators (rho : TwoKernel) : TwoKernel := fun m n => rho (m.2,m.1) (n.2,n.1)

/-- PDF p.2: vacuum and the harmless conditional state on zero-Born-law sets. -/
def oneModeVacuum : OneKernel := fun m n =>
  QAlgorithms.Papers.Independent.Next46.P32.vacuum 1 (fun _ => m) (fun _ => n)

/-- PDF p.2: actual D(z) rho_M D(z)^dagger density, relative to d^2z/pi. -/
def seedEffect (s : GaussianSeed) (z : ℂ) : OneKernel := fun m n =>
  ∑' u, ∑' v, displacementMatrix z m u * s.density u v *
    star (displacementMatrix z n v)

/-- PDF p.2: Tr_B[rho (I tensor E)], with both retained A indices. -/
def unnormalizedConditional (rho : TwoKernel) (E : OneKernel) : OneKernel :=
  fun m n => ∑' u, ∑' v, rho (m,u) (n,v) * E v u

/-- PDF p.2: actual Born density, not an assumed Gaussian law. -/
def bornDensity (rho : TwoKernel) (E : OneKernel) : ℝ :=
  (∑' m, unnormalizedConditional rho E m m).re

/-- PDF p.2: normalize the posterior exactly when the Born density is positive. -/
def posteriorDensity (rho : TwoKernel) (E : OneKernel) : OneKernel :=
  if 0 < bornDensity rho E then ((bornDensity rho E)⁻¹ : ℂ) • unnormalizedConditional rho E else oneModeVacuum

/-- PDF p.2: actual Born outcome measure. Probability normalization is concluded. -/
def seedLaw (rho : TwoKernel) (s : GaussianSeed) : Measure ℂ :=
  coherentMeasure.withDensity (fun z => ENNReal.ofReal (bornDensity rho (seedEffect s z)))

/-- PDF p.2: integrated independent full-space von Neumann entropy. -/
def seedAverage (rho : TwoKernel) (s : GaussianSeed) : ℝ≥0∞ :=
  ∫⁻ z, extendedEntropyNats (posteriorDensity rho (seedEffect s z)) ∂seedLaw rho s

/-- PDF p.2: Gaussian conditional entropy optimized over actual seed densities.
Empty infima are infinity, not real zero; finiteness is a conclusion below. -/
def gaussianConditionalInf (rho : TwoKernel) : ℝ≥0∞ := ⨅ s : GaussianSeed, seedAverage rho s

/-- PDF p.2: A-discord means measuring B. Finite real conversion is interpreted
on the Gaussian domain, whose entropy finiteness is established below. -/
def gaussianDiscordA (rho : TwoKernel) : ℝ :=
  (extendedEntropyNats (partialLeft rho)).toReal - (extendedEntropyNats rho).toReal +
    (gaussianConditionalInf rho).toReal

/-- PDF pp.1--2: Gaussian extractable information from the same independent
measurement optimization, retaining A and measuring B. -/
def gaussianClassicalCorrelationA (rho : TwoKernel) : ℝ :=
  (extendedEntropyNats (partialRight rho)).toReal - (gaussianConditionalInf rho).toReal

/-- PDF pp.2--3: actual vacuum-seed heterodyne effect; no optimality is built in. -/
def heterodyneEffect (z : ℂ) : OneKernel := fun m n =>
  coherentCoefficient z m * star (coherentCoefficient z n)

/-- PDF pp.2--3: actual heterodyne conditional entropy. -/
def heterodyneAverage (rho : TwoKernel) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (bornDensity rho (heterodyneEffect z)) *
    extendedEntropyNats (posteriorDensity rho (heterodyneEffect z)) ∂coherentMeasure

/-- PDF pp.2--3: weakly normalized variable-seed POVMs, including their actual
weights and reference measure. Normalization tests every finite superposition.
This excludes arbitrary independently varying seeds integrated against plain dX dY. -/
structure NoncovariantMeasurement where
  outcomeMeasure : Measure (ℂ × GaussianSeed)
  weight : ℂ × GaussianSeed → ℝ
  weight_measurable : Measurable weight
  weight_nonnegative : ∀ z, 0 ≤ weight z
  weak_normalization : ∀ (F : Finset ℕ) (u : ℕ → ℂ),
    Integrable (fun z => (weight z : ℂ) *
      (∑ m ∈ F, ∑ n ∈ F, star (u m) * seedEffect z.2 z.1 m n * u n)) outcomeMeasure ∧
    (∫ z, (weight z : ℂ) *
      (∑ m ∈ F, ∑ n ∈ F, star (u m) * seedEffect z.2 z.1 m n * u n) ∂outcomeMeasure) =
      ∑ m ∈ F, star (u m) * u m

/-- PDF p.3: actual weighted POVM density. -/
def variableEffect (M : NoncovariantMeasurement) (z : ℂ × GaussianSeed) : OneKernel :=
  (M.weight z : ℂ) • seedEffect z.2 z.1

/-- PDF p.3: actual normalized Born law for a weakly normalized experiment. -/
def variableLaw (rho : TwoKernel) (M : NoncovariantMeasurement) : Measure (ℂ × GaussianSeed) :=
  M.outcomeMeasure.withDensity (fun z => ENNReal.ofReal (bornDensity rho (variableEffect M z)))

/-- PDF p.3: outcome-averaged independent von Neumann entropy. -/
def variableAverage (rho : TwoKernel) (M : NoncovariantMeasurement) : ℝ≥0∞ :=
  ∫⁻ z, extendedEntropyNats (posteriorDensity rho (variableEffect M z)) ∂variableLaw rho M

/-- PDF p.2: the entropy function, with Mathlib's 0*log(0)=0 convention. -/
def halfUnitEntropy (x : ℝ) : ℝ := g (x - 1/2)

/-- PDF p.2: covariance block on physical modes i,j. -/
def covarianceModeBlock (V : Matrix (modePhase 2) (modePhase 2) ℝ) (i j : Fin 2) : Matrix (modePhase 1) (modePhase 1) ℝ :=
  fun k l => V (i,k.2) (j,l.2)

/-- PDF p.2: the four symplectic invariants in their source order. -/
def covarianceInvariant (V : Matrix (modePhase 2) (modePhase 2) ℝ) (k : Fin 4) : ℝ :=
  if k = 0 then (covarianceModeBlock V 0 0).det else if k = 1 then (covarianceModeBlock V 1 1).det
  else if k = 2 then (covarianceModeBlock V 0 1).det else V.det

/-- PDF p.2: Delta=I1+I2+2I3. -/
def symplecticDiscriminant (V : Matrix (modePhase 2) (modePhase 2) ℝ) : ℝ :=
  covarianceInvariant V 0 + covarianceInvariant V 1 + 2 * covarianceInvariant V 2

/-- PDF p.2: the smaller and larger symplectic eigenvalues. -/
def symplecticMinus (V : Matrix (modePhase 2) (modePhase 2) ℝ) : ℝ :=
  Real.sqrt ((symplecticDiscriminant V - Real.sqrt ((symplecticDiscriminant V)^2 - 4 * covarianceInvariant V 3)) / 2)

/-- PDF p.2: the plus branch uses the positive inner square-root sign. -/
def symplecticPlus (V : Matrix (modePhase 2) (modePhase 2) ℝ) : ℝ :=
  Real.sqrt ((symplecticDiscriminant V + Real.sqrt ((symplecticDiscriminant V)^2 - 4 * covarianceInvariant V 3)) / 2)

/-- PDF p.2: Schur complement; physical B+M is invertible. -/
def gaussianSchurCovariance (V : Matrix (modePhase 2) (modePhase 2) ℝ)
    (M : Matrix (modePhase 1) (modePhase 1) ℝ) : Matrix (modePhase 1) (modePhase 1) ℝ :=
  conditionalCovariance (covarianceModeBlock V 0 0) (covarianceModeBlock V 1 1)
    (covarianceModeBlock V 0 1) M

/-- PDF p.2, Eq.(1): extended covariance-side infimum over physical seed
covariances. The missing determinant in the printed h(sqrt(sigma_P)) is restored. -/
def covarianceInf (V : Matrix (modePhase 2) (modePhase 2) ℝ) : ℝ≥0∞ :=
  ⨅ M : {M : Matrix (modePhase 1) (modePhase 1) ℝ // IsDiscordCovariance M},
    ENNReal.ofReal (halfUnitEntropy (Real.sqrt ((gaussianSchurCovariance V M.val).det)))

/-- PDF p.2: two-mode squeeze matrix obtained from
exp(tanh(r) a^dagger b^dagger) cosh(r)^(-1-na-nb) exp(-tanh(r) ab).
The finite sum is per coefficient, not a photon cutoff. -/
def squeezeCoefficient (r : ℝ) (out inp : ℕ × ℕ) : ℝ :=
  Real.sqrt ((Nat.factorial out.1 : ℝ) * (Nat.factorial out.2 : ℝ) *
    (Nat.factorial inp.1 : ℝ) * (Nat.factorial inp.2 : ℝ)) *
  ∑ j ∈ Finset.range (min inp.1 inp.2 + 1),
    if inp.1 - j ≤ out.1 ∧ inp.2 - j ≤ out.2 ∧
      out.1 - (inp.1 - j) = out.2 - (inp.2 - j) then
      (-Real.tanh r)^j * (Real.tanh r)^(out.1 - (inp.1 - j)) /
        ((Nat.factorial j : ℝ) * (Nat.factorial (out.1 - (inp.1 - j)) : ℝ) *
          (Nat.factorial (inp.1 - j) : ℝ) * (Nat.factorial (inp.2 - j) : ℝ) *
          (Real.cosh r)^(inp.1 + inp.2 - 2*j + 1))
    else 0

/-- PDF p.2: constructed S(r)(nu(N1) tensor nu(N2))S(r)^dagger on the full
oscillator space. Density, Gaussianity and the spectrum are conclusions. -/
def sts (N1 N2 r : ℝ) : TwoKernel := fun m n =>
  ∑' k : ℕ × ℕ, ((thermalProbability N1 k.1 * thermalProbability N2 k.2 *
    squeezeCoefficient r m k * squeezeCoefficient r n k : ℝ) : ℂ)

/-- PDF p.2: mean photons due to canonical nonnegative squeezing. -/
def squeezingPhotons (r : ℝ) : ℝ := (Real.sinh r)^2

/-- PDF p.2: STS covariance parameter a. -/
def stsA (N1 N2 r : ℝ) : ℝ :=
  squeezingPhotons r + 1/2 + N1 * (1 + squeezingPhotons r) + N2 * squeezingPhotons r

/-- PDF p.2: STS covariance parameter b. -/
def stsB (N1 N2 r : ℝ) : ℝ := stsA N2 N1 r

/-- PDF p.2: c1=-c2=c>=0, including pure inputs and r=0. -/
def stsC (N1 N2 r : ℝ) : ℝ :=
  (1 + N1 + N2) * Real.sqrt (squeezingPhotons r * (1 + squeezingPhotons r))

/-- PDF p.2: the covariance constructed from the thermal/squeeze parameters. -/
def stsCovariance (N1 N2 r : ℝ) : Matrix (modePhase 2) (modePhase 2) ℝ :=
  twoModeStandard (stsA N1 N2 r) (stsB N1 N2 r) (stsC N1 N2 r) (-stsC N1 N2 r)

/-- PDF p.3, Eq.(2): no extra outer square root on the conditional argument. -/
def closedDiscord (V : Matrix (modePhase 2) (modePhase 2) ℝ) : ℝ :=
  halfUnitEntropy (Real.sqrt (covarianceInvariant V 1)) - halfUnitEntropy (symplecticMinus V) - halfUnitEntropy (symplecticPlus V) +
    halfUnitEntropy ((Real.sqrt (covarianceInvariant V 0) +
      2 * Real.sqrt (covarianceInvariant V 0 * covarianceInvariant V 1) + 2 * covarianceInvariant V 2) /
        (1 + 2 * Real.sqrt (covarianceInvariant V 1)))

/-- PDF p.3: actual trace purity Tr(rho^2), not a Gaussian determinant definition. -/
def tracePurity (rho : TwoKernel) : ℝ :=
  (∑' m : ℕ × ℕ, ∑' n : ℕ × ℕ, rho m n * rho n m).re

/-- PDF p.3: symmetric STS expressed in physical purity mu and PT eigenvalue t.
It is used only when 0<mu<=1, t>0 and 2t sqrt(mu)<=1, or eventually as mu->0+. -/
def symmetricState (mu t : ℝ) : TwoKernel :=
  sts ((1 / Real.sqrt mu - 1) / 2) ((1 / Real.sqrt mu - 1) / 2)
    (Real.log (1 / (2 * t * Real.sqrt mu)) / 2)

/-- PDF p.3: physical symmetric purity/PT parameter domain. -/
def SymmetricDomain (mu t : ℝ) : Prop :=
  0 < mu ∧ mu ≤ 1 ∧ 0 < t ∧ 2 * t * Real.sqrt mu ≤ 1

/-- PDF p.3: smaller symplectic eigenvalue after partial transposition. -/
def ptMinus (V : Matrix (modePhase 2) (modePhase 2) ℝ) : ℝ :=
  let D := covarianceInvariant V 0 + covarianceInvariant V 1 - 2 * covarianceInvariant V 2
  Real.sqrt ((D - Real.sqrt (D^2 - 4 * covarianceInvariant V 3)) / 2)

/-- PDF p.3: actual total occupation expectation, allowed to diverge off-domain. -/
def totalPhotonEnergy (rho : TwoKernel) : ℝ≥0∞ :=
  ∑' m : ℕ × ℕ, ENNReal.ofReal (((m.1 : ℝ) + (m.2 : ℝ)) * (rho m m).re)

/-- PDF p.4: coherent-state teleportation fidelity as a function of the PT
symplectic eigenvalue for the symmetric STS family discussed here. -/
def teleportationFidelity (t : ℝ) : ℝ := 1 / (1 + 2*t)

/-- PDF p.3: algebraically simplified fixed-PT infinite-energy limit. -/
def infiniteEnergyDiscord (t : ℝ) : ℝ := (1 + 2*t) * Real.log ((1 + 2*t) / (2*t)) - 1

/-- PDF p.4: thermal damping acts on each physical Weyl coordinate. -/
def dampedArgument (g1 g2 t : ℝ) (x : modePhase 2 → ℝ) : modePhase 2 → ℝ :=
  fun i => Real.exp (-(if i.1 = 0 then g1 else g2) * t / 2) * x i

/-- PDF p.4: physical independent thermal-attenuator channel, specified on ALL
density characteristic functions. This does not assume its covariance identity
or the source's undefined/sign-ambiguous Lindblad L convention. -/
def ThermalEvolution (Phi : TwoKernel → TwoKernel) (g1 g2 M1 M2 t : ℝ) : Prop :=
  IsTraceClassChannel Phi ∧ ∀ rho, IsDensity rho → ∀ x,
    characteristicTwo (Phi rho) x = characteristicTwo rho (dampedArgument g1 g2 t x) *
      Complex.exp (((-(∑ i : modePhase 2,
        (1 - Real.exp (-(if i.1 = 0 then g1 else g2) * t)) *
          ((if i.1 = 0 then M1 else M2) + 1/2) * (x i)^2) / 2 : ℝ) : ℂ))

/-- PDF p.4: full covariance map, including off-standard Gaussian inputs. -/
def attenuatedCovariance (V : Matrix (modePhase 2) (modePhase 2) ℝ)
    (g1 g2 M1 M2 t : ℝ) : Matrix (modePhase 2) (modePhase 2) ℝ := fun i j =>
  Real.exp (-(if i.1 = 0 then g1 else g2) * t / 2) * V i j *
    Real.exp (-(if j.1 = 0 then g1 else g2) * t / 2) +
    if i = j then (1 - Real.exp (-(if i.1 = 0 then g1 else g2) * t)) *
      ((if i.1 = 0 then M1 else M2) + 1/2) else 0

/-! Reuse audit: modePhase is the accepted interleaved index. canonicalOmega
is its unit CCR form; the imported paper's hbar=2 physicality is not reused.
partialRight/partialLeft are full trace-class partial traces. twoModeStandard
is the interleaved covariance array; conditionalCovariance is the generic Schur
operation. thermalProbability uses mean N; halfUnitEntropy adapts the accepted
occupation entropy g by N=x-1/2. oneModeVacuum reindexes the accepted Fock vacuum
to N labels. Distinct local concepts and name collisions are documented in
ASSESSMENT.json and MODERATION_NOTES.md. -/

/-! Sanity examples pin conventions and total-function boundaries. -/

example : canonicalOmega 2 (0,0) (0,1) = 1 := by simp [canonicalOmega]

example : weylArg 0 0 = 0 := by simp [weylArg]

example : oneModeVacuum 0 0 = 1 := by
  simp [oneModeVacuum, QAlgorithms.Papers.Independent.Next46.P32.vacuum]
  rfl

example (rho : TwoKernel) : swapOscillators (swapOscillators rho) = rho := rfl

example (rho : TwoKernel) (E : OneKernel) (hp : ¬ 0 < bornDensity rho E) :
    posteriorDensity rho E = oneModeVacuum := by simp [posteriorDensity, hp]

example : halfUnitEntropy (1/2) = 0 := by norm_num [halfUnitEntropy, g]

example : thermalProbability 0 0 = 1 := by norm_num [thermalProbability]

example : squeezeCoefficient 0 (0,0) (0,0) = 1 := by norm_num [squeezeCoefficient]

example : squeezingPhotons 0 = 0 := by simp [squeezingPhotons]

example : stsA 0 0 0 = 1/2 := by norm_num [stsA, squeezingPhotons]

example : stsC 0 0 0 = 0 := by norm_num [stsC, squeezingPhotons]

example : twoModeStandard (1/2) (1/2) 0 0 (0,0) (1,1) = 0 := by simp [twoModeStandard]

example (V : Matrix (modePhase 2) (modePhase 2) ℝ) : covarianceInvariant V 3 = V.det := by simp [covarianceInvariant]

example : teleportationFidelity (1/2) = 1/2 := by norm_num [teleportationFidelity]

example (x : modePhase 2 → ℝ) : dampedArgument 0 0 0 x = x := by
  funext i
  simp [dampedArgument]

/-! Source statements; every result is deliberately unproved. -/

end QAlgorithms.Papers.Independent.Advance50.P48


