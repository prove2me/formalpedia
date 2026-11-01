-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P02
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P02
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T03:45:49.777251+00:00
-- url     : https://prove2.me/theorems/7fa63ab2-f2d3-4a8c-ab87-1cd68c3895b3
-- title:
--   Definitions for A practical limitation for continuous-variable quantum cryptography using coherent states
-- statement:
--   The objects the formalized statements of *A practical limitation for continuous-variable quantum cryptography using coherent states* (arXiv:quant-ph/0403115) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OscillatorPOVM`: PDF p.2, (6)–(7): a normalized, weakly countably additive POVM on the complete oscillator, with any measurable outcome space. `law` is its scalar Born measure, including on unnormalized vectors. Thus it cannot encode a measurement depending on Alice's secret sign. Finite-register POVMs and the accepted finite-outcome FockPOVM do not cover this domain.
--   - `binaryPosterior`: PDF p.2, (6): equal binary priors give posterior dP+ / d(P+ + P-). Values on null outcomes have no effect on the subsequent integral.
--   - `measurementRenyi`: PDF p.2, (6), cited collision/Rényi leakage convention: the logarithm of twice the average posterior collision probability, in bits. The sum law has mass two for unit input states. This is not Shannon or Holevo information.
--   - `reflectedAmplitude`: PDF pp.1–2, Fig.1 and (7): Eve's two reflected coherent states, after basis announcement. A sign-independent POVM acts on this pair.
--   - `leakageValues`: PDF p.2, (7): values actually attainable by individual POVMs. The outcome space and its sigma algebra are also optimized; no finite-outcome restriction.
--   - `optimalLeakage`: PDF p.2, (7): optimization, independently of its claimed closed form. The theorem asserts an attained greatest value, excluding default real suprema.
--   - `ReflectedPairRealized`: The coefficient realization and unit normalization of the actual pair in (7). This is a conclusion, never an extra hypothesis of the leakage theorem.
--   - `binaryDensity`: PDF p.2, (2): equiprobable positive/negative coherent signal density. `energy` is the received mean photon number, not the emitted intensity.
--   - `homodynePosterior`: PDF p.2, (5): Bayes posterior, defined from the actual two likelihoods. The logistic expression is not assumed as a hypothesis.
--   - `binaryInformation`: PDF p.2, (4): one minus binary entropy, in bits, with 0 log 0 = 0.
--   - `homodyneInformation`: PDF p.2, (4)–(5): Bob's conditional Shannon information at x.
--   - `gainWithLeakage`: PDF p.2, (8): ideal-correction gain per emitted pulse. One half is the basis-match probability. Both tails are integrated without conditioning on acceptance and without clipping a negative gain to zero.
--   - `splittingGain`: PDF p.2, (8): gain against the individual beam-splitting attack, using the genuine measurement optimization rather than its closed form.
--   - `coherentAmplitudeQuadrature`: PDF pp.1,3: specialize the accepted quadrature coordinate to one mode. `false` selects the real coordinate and `true` the imaginary coordinate.
--   - `displacedCoherent`: PDF p.3, (10): full coherent-state mixture kernel. The Gaussian has total complex variance V; each real displacement has variance V/2. At V=0 the accepted Gaussian measure is Dirac at zero. No photon cutoff is imposed.
--   - `MixtureIntegrable`: PDF p.3, (10): scalar integrability of every mixture coefficient prevents default-zero Bochner integrals from representing a channel output.
--   - `displacedHomodyne`: PDF p.3, after (10): actual quadrature law obtained by independent planar Gaussian displacement and intrinsic coherent-state homodyne noise.
--   - `binaryDisplacedLaw`: PDF p.3, (10), with the binary signaling of (2): the observed law is an unconditioned, equally weighted mixture of the two displaced signal laws.
--   - `amplifiedVariance`: PDF p.3, (11): finite quantum-limited intensity gain g>=1.
--   - `splittingAmplifierOutput`: PDF p.3, Fig.3: split first, amplify only Bob's mode, and retain only the reflected coherent mode for Eve. The product kernel makes independence of Bob's amplifier noise explicit. The amplifier's ancillary output is not Eve's.
--   - `amplifiedLeakage`: PDF p.3, after (12): reflected-mode leakage, still an optimization over actual POVMs, at the effective transmissivity eta/g.
--   - `amplifiedGain`: PDF p.3, after (12): gain for this specific reflected-mode attack.
--   - `classicalTeleportationOutput`: PDF pp.3–4: heterodyne result z~CN(alpha,1), coherent resend, then loss. This defines the measure–prepare operation before identifying it with (14).
--   - `classicalTeleportationHomodyne`: PDF p.4: the independent homodyne observation after CT and optional loss.
--   - `aliceEveLaw`: PDF p.4: Eve retains z before attenuation. Alice may use any probability ensemble of coherently encoded classical symbols, including continuous ones.
--   - `aliceBobLaw`: PDF p.4: Bob's record is sampled from a receiver kernel on the coherent amplitude sqrt(eta) z. This permits any measurable receiver or postprocessing; the complete classical z is available to Eve.
--   - `mutualInformationBits`: PDF pp.1,4: classical Shannon mutual information in bits, as relative entropy of the joint law from its product marginals. Infinity is preserved; no differential-entropy subtraction or toReal of infinite information is used.
--   - `normalizedExcess`: PDF p.4: normalized excess quadrature noise, with coherent variance 1/4.
-- source:
--   A practical limitation for continuous-variable quantum cryptography using coherent states, arXiv:quant-ph/0403115v1, https://arxiv.org/abs/quant-ph/0403115v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

/-!
Namiki and Hirano, arXiv:quant-ph/0403115v1, PDF pp.1–4.
The imports above are pinned accepted library modules, not unreviewed chunks.
New interfaces are confined to this paper. Quadratures have coherent variance
1/4; all logarithms used for information have base two. The universal
public-discussion security converse is deferred, not replaced by gain positivity.
Compilation is pending the requested batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P02

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator coherentKet coherentCoefficient)
open QAlgorithms.Papers.Independent.Frontier30.P21 (coherentDensity)
open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal quadrature)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity productCoeff)

/-- PDF p.2, below (2): coherent-state quadrature variance for [x1,x2]=i/2. -/
example : 4 * (1 / 4 : ℝ) = 1 := by norm_num

/-- PDF p.2, (6)–(7): a normalized, weakly countably additive POVM on the
complete oscillator, with any measurable outcome space. `law` is its scalar
Born measure, including on unnormalized vectors. Thus it cannot encode a
measurement depending on Alice's secret sign. Finite-register POVMs and the
accepted finite-outcome FockPOVM do not cover this domain. -/
structure OscillatorPOVM (O : Type) [MeasurableSpace O] where
  effect : Set O → FockOperator
  empty : effect ∅ = 0
  total : effect Set.univ = ContinuousLinearMap.id ℂ Fock
  positive : ∀ S, MeasurableSet S → ∀ u : Fock,
    (inner (𝕜 := ℂ) u (effect S u)).im = 0 ∧
      0 ≤ (inner (𝕜 := ℂ) u (effect S u)).re
  additive : ∀ S : ℕ → Set O, (∀ j, MeasurableSet (S j)) →
    Pairwise (fun i j => Disjoint (S i) (S j)) → ∀ u v : Fock,
    HasSum (fun j => inner (𝕜 := ℂ) u (effect (S j) v))
      (inner (𝕜 := ℂ) u (effect (⋃ j, S j) v))
  law : Fock → Measure O
  finite : ∀ u, IsFiniteMeasure (law u)
  born : ∀ (u : Fock) (S : Set O), MeasurableSet S →
    law u S = ENNReal.ofReal (inner (𝕜 := ℂ) u (effect S u)).re

example {O : Type} [MeasurableSpace O] (E : OscillatorPOVM O) :
    E.law 0 Set.univ = 0 := by
  rw [E.born _ _ MeasurableSet.univ]
  simp

/-- PDF p.2, (6): equal binary priors give posterior dP+ / d(P+ + P-).
Values on null outcomes have no effect on the subsequent integral. -/
def binaryPosterior {O : Type} [MeasurableSpace O]
    (plus minus : Measure O) (o : O) : ℝ :=
  (plus.rnDeriv (plus + minus) o).toReal

/-- PDF p.2, (6), cited collision/Rényi leakage convention: the logarithm of
twice the average posterior collision probability, in bits. The sum law has
mass two for unit input states. This is not Shannon or Holevo information. -/
def measurementRenyi {O : Type} [MeasurableSpace O]
    (E : OscillatorPOVM O) (plus minus : Fock) : ℝ :=
  Real.logb 2 (∫ o,
    (binaryPosterior (E.law plus) (E.law minus) o) ^ 2 +
      (1 - binaryPosterior (E.law plus) (E.law minus) o) ^ 2
    ∂(E.law plus + E.law minus))

/-- PDF pp.1–2, Fig.1 and (7): Eve's two reflected coherent states, after
basis announcement. A sign-independent POVM acts on this pair. -/
def reflectedAmplitude (n eta : ℝ) : ℂ := (Real.sqrt ((1 - eta) * n) : ℂ)

example (n : ℝ) : reflectedAmplitude n 1 = 0 := by
  simp [reflectedAmplitude]

/-- PDF p.2, (7): values actually attainable by individual POVMs. The outcome
space and its sigma algebra are also optimized; no finite-outcome restriction. -/
def leakageValues (n eta : ℝ) : Set ℝ :=
  {r | ∃ (O : Type) (m : MeasurableSpace O) (E : @OscillatorPOVM O m),
    r = @measurementRenyi O m E
      (coherentKet (reflectedAmplitude n eta))
      (coherentKet (-reflectedAmplitude n eta))}

/-- PDF p.2, (7): optimization, independently of its claimed closed form.
The theorem asserts an attained greatest value, excluding default real suprema. -/
def optimalLeakage (n eta : ℝ) : ℝ := sSup (leakageValues n eta)

/-- The coefficient realization and unit normalization of the actual pair in
(7). This is a conclusion, never an extra hypothesis of the leakage theorem. -/
def ReflectedPairRealized (n eta : ℝ) : Prop :=
  ∀ alpha ∈ ({reflectedAmplitude n eta, -reflectedAmplitude n eta} : Set ℂ),
    (∀ j, coherentKet alpha j = coherentCoefficient alpha j) ∧ ‖coherentKet alpha‖ = 1

/-- PDF p.2, (2): equiprobable positive/negative coherent signal density.
`energy` is the received mean photon number, not the emitted intensity. -/
def binaryDensity (v energy x : ℝ) : ℝ :=
  (gaussianPDFReal (Real.sqrt energy) v.toNNReal x + gaussianPDFReal (-Real.sqrt energy) v.toNNReal x) / 2

/-- PDF p.2, (5): Bayes posterior, defined from the actual two likelihoods.
The logistic expression is not assumed as a hypothesis. -/
def homodynePosterior (v energy x : ℝ) : ℝ :=
  gaussianPDFReal (Real.sqrt energy) v.toNNReal x /
    (gaussianPDFReal (Real.sqrt energy) v.toNNReal x + gaussianPDFReal (-Real.sqrt energy) v.toNNReal x)

/-- PDF p.2, (4): one minus binary entropy, in bits, with 0 log 0 = 0. -/
def binaryInformation (p : ℝ) : ℝ :=
  1 + p * Real.logb 2 p + (1 - p) * Real.logb 2 (1 - p)

/-- PDF p.2, (4)–(5): Bob's conditional Shannon information at x. -/
def homodyneInformation (v energy x : ℝ) : ℝ :=
  binaryInformation (homodynePosterior v energy x)

/-- PDF p.2, (8): ideal-correction gain per emitted pulse. One half is the
basis-match probability. Both tails are integrated without conditioning on
acceptance and without clipping a negative gain to zero. -/
def gainWithLeakage (x0 energy v leakage : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in {x : ℝ | x0 < |x|},
    binaryDensity v energy x * (homodyneInformation v energy x - leakage)

/-- PDF p.2, (8): gain against the individual beam-splitting attack, using
the genuine measurement optimization rather than its closed form. -/
def splittingGain (x0 n eta : ℝ) : ℝ :=
  gainWithLeakage x0 (eta * n) (1 / 4 : ℝ) (optimalLeakage n eta)

example : binaryInformation 1 = 1 := by
  simp [binaryInformation]

/-- PDF pp.1,3: specialize the accepted quadrature coordinate to one mode.
`false` selects the real coordinate and `true` the imaginary coordinate. -/
def coherentAmplitudeQuadrature (imaginary : Bool) (alpha : ℂ) : ℝ :=
  quadrature (fun _ : Fin 1 => alpha) (0, if imaginary then 1 else 0)

example (alpha : ℂ) : coherentAmplitudeQuadrature false alpha = alpha.re := by
  rfl

example (alpha : ℂ) : coherentAmplitudeQuadrature true alpha = alpha.im := by
  rfl

/-- PDF p.3, (10): full coherent-state mixture kernel. The Gaussian has total
complex variance V; each real displacement has variance V/2. At V=0 the
accepted Gaussian measure is Dirac at zero. No photon cutoff is imposed. -/
def displacedCoherent (mean : ℂ) (V : ℝ) : Matrix ℕ ℕ ℂ :=
  fun j k => ∫ beta : ℂ, coherentDensity (mean + beta) j k ∂complexNormal V 0

example (mean : ℂ) : displacedCoherent mean 0 = coherentDensity mean := by
  funext j k
  simp [displacedCoherent, complexNormal]

/-- PDF p.3, (10): scalar integrability of every mixture coefficient prevents
default-zero Bochner integrals from representing a channel output. -/
def MixtureIntegrable (mean : ℂ) (V : ℝ) : Prop :=
  ∀ j k, Integrable (fun beta : ℂ => coherentDensity (mean + beta) j k)
    (complexNormal V 0)

/-- PDF p.3, after (10): actual quadrature law obtained by independent planar
Gaussian displacement and intrinsic coherent-state homodyne noise. -/
def displacedHomodyne (mean : ℂ) (V : ℝ) (imaginary : Bool) : Measure ℝ :=
  ((complexNormal V 0).prod (gaussianReal 0 (1 / 4))).map
    (fun z : ℂ × ℝ => coherentAmplitudeQuadrature imaginary (mean + z.1) + z.2)

/-- PDF p.3, (10), with the binary signaling of (2): the observed law is an
unconditioned, equally weighted mixture of the two displaced signal laws. -/
def binaryDisplacedLaw (V energy : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • displacedHomodyne (Real.sqrt energy : ℂ) V false +
    (1 / 2 : ℝ≥0∞) • displacedHomodyne (-((Real.sqrt energy : ℂ))) V false

example (mean : ℂ) : complexNormal 0 mean = Measure.dirac mean := by
  simp [complexNormal]

/-- PDF p.3, (11): finite quantum-limited intensity gain g>=1. -/
def amplifiedVariance (g : ℝ) : ℝ := (2 * g - 1) * (1 / 4 : ℝ)

/-- PDF p.3, Fig.3: split first, amplify only Bob's mode, and retain only the
reflected coherent mode for Eve. The product kernel makes independence of
Bob's amplifier noise explicit. The amplifier's ancillary output is not Eve's. -/
def splittingAmplifierOutput (eta g : ℝ) (alpha : ℂ) :
    Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  productCoeff (displacedCoherent ((Real.sqrt eta : ℂ) * alpha) (g - 1))
    (coherentDensity ((Real.sqrt (1 - eta / g) : ℂ) * alpha))

/-- PDF p.3, after (12): reflected-mode leakage, still an optimization over
actual POVMs, at the effective transmissivity eta/g. -/
def amplifiedLeakage (n eta g : ℝ) : ℝ := optimalLeakage n (eta / g)

/-- PDF p.3, after (12): gain for this specific reflected-mode attack. -/
def amplifiedGain (x0 n eta g : ℝ) : ℝ :=
  gainWithLeakage x0 (eta * n) (amplifiedVariance g) (amplifiedLeakage n eta g)

example : amplifiedVariance 1 = (1 / 4 : ℝ) := by
  norm_num [amplifiedVariance]

/-- PDF pp.3–4: heterodyne result z~CN(alpha,1), coherent resend, then loss.
This defines the measure–prepare operation before identifying it with (14). -/
def classicalTeleportationOutput (eta : ℝ) (alpha : ℂ) : Matrix ℕ ℕ ℂ :=
  fun j k => ∫ z : ℂ, coherentDensity ((Real.sqrt eta : ℂ) * z) j k
    ∂complexNormal 1 alpha

/-- PDF p.4: the independent homodyne observation after CT and optional loss. -/
def classicalTeleportationHomodyne (eta : ℝ) (alpha : ℂ)
    (imaginary : Bool) : Measure ℝ :=
  ((complexNormal 1 alpha).prod (gaussianReal 0 (1 / 4))).map
    (fun z : ℂ × ℝ => Real.sqrt eta * coherentAmplitudeQuadrature imaginary z.1 + z.2)

/-- PDF p.4: Eve retains z before attenuation. Alice may use any probability
ensemble of coherently encoded classical symbols, including continuous ones. -/
def aliceEveLaw {A : Type} [MeasurableSpace A] (mu : Measure A)
    (amplitude : A → ℂ) : Measure (A × ℂ) :=
  (mu.prod (complexNormal 1 0)).map
    (fun z : A × ℂ => (z.1, amplitude z.1 + z.2))

/-- PDF p.4: Bob's record is sampled from a receiver kernel on the coherent
amplitude sqrt(eta) z. This permits any measurable receiver or postprocessing;
the complete classical z is available to Eve. -/
def aliceBobLaw {A O : Type} [MeasurableSpace A] [MeasurableSpace O]
    (mu : Measure A) (amplitude : A → ℂ) (eta : ℝ) (receiver : Kernel ℂ O) :
    Measure (A × O) :=
  ((aliceEveLaw mu amplitude).compProd
    (Kernel.prodMkLeft A (receiver.comap
      (fun z : ℂ => (Real.sqrt eta : ℂ) * z) (by fun_prop)))).map
        (fun z : (A × ℂ) × O => (z.1.1, z.2))

/-- PDF pp.1,4: classical Shannon mutual information in bits, as relative
entropy of the joint law from its product marginals. Infinity is preserved;
no differential-entropy subtraction or toReal of infinite information is used. -/
def mutualInformationBits {A O : Type} [MeasurableSpace A] [MeasurableSpace O]
    (joint : Measure (A × O)) : ℝ≥0∞ :=
  InformationTheory.klDiv joint ((joint.map Prod.fst).prod (joint.map Prod.snd)) /
    ENNReal.ofReal (Real.log 2)

/-- PDF p.4: normalized excess quadrature noise, with coherent variance 1/4. -/
def normalizedExcess (v : ℝ) : ℝ := v / (1 / 4 : ℝ) - 1

example : normalizedExcess (3 * (1 / 4 : ℝ)) = 2 := by
  norm_num [normalizedExcess]

end QAlgorithms.Papers.Independent.Intakethird100.P02


