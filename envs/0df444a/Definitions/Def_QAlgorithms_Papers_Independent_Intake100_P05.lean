-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P05
-- name    : QAlgorithms_Papers_Independent_Intake100_P05
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:42:55.924785+00:00
-- url     : https://prove2.me/theorems/5675a688-125e-4b21-9c4e-49e6297b17c8
-- title:
--   Definitions for Continuous-variable quantum key distribution protocols over noisy channels
-- statement:
--   The objects the formalized statements of *Continuous-variable quantum key distribution protocols over noisy channels* (arXiv:0806.3954) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `normalLaw`: PDF p.2: centered normal law, including the Dirac law when v=0. Negative variances are a total off-domain extension and never used in targets.
--   - `normalPDF`: PDF p.3: ordinary normal density; used only at strictly positive variance.
--   - `IsContinuousDensityKernel`: PDF pp.2–3: density criterion for the full continuous integral kernel. Unlike frozen Dependency50.P17.IsDensityKernel, its arguments are a measure and a position kernel; it does not use counting-measure basis coefficients. Positivity tests all finite Gram matrices; normalization is an actual Lebesgue trace integral. No covariance, spectrum, or proposed identity is a field.
--   - `squeezedWave`: PDF p.2: displacement-modulated squeezed wavefunction in position space. False selects q squeezing, true p squeezing. Position variance is 1/V or V; p displacement a has the phase exp(i a q/2) in the vacuum-I convention.
--   - `preparedKernel`: PDF p.2: actual pure emitted density kernel, independent of global phase.
--   - `averagedKernel`: PDF p.2: ensemble average over Alice's Gaussian displacement.
--   - `thermalPositionKernel`: PDF p.2: position kernel of the centered one-mode thermal density, quadrature variance V. This is not defined by the ensemble identity. Frozen Gap48.P26.thermalKernel instead takes mean photon number and returns number-basis coefficients on Nat; these are different representations.
--   - `eprWave`: PDF p.3, Fig.3: complete two-mode squeezed EPR wavefunction. The q correlation is +sqrt(V²-1), and the p correlation has the opposite sign.
--   - `eprKernel`: PDF p.3, Fig.3: actual initial rank-one EPR density.
--   - `measuredEprWave`: PDF p.3, Fig.3: q_A homodyne is evaluation; p_A homodyne uses the unitary Fourier convention exp(-i x s/2)/sqrt(4 pi). The outcome is x.
--   - `eprBornDensity`: PDF p.3, Fig.3: actual homodyne Born density, computed from the wave.
--   - `eprPosteriorKernel`: PDF p.3, Fig.3: normalize the actual posterior by its own Born density. The targets conclude that this denominator is strictly positive.
--   - `eprDisplacement`: PDF p.3, Fig.3: the displacement induced on B by Alice's outcome x. The minus sign for p is the EPR momentum anticorrelation.
--   - `lossKernel`: PDF p.3, Eq.(3): actual pure-loss channel on B, realized by a vacuum beamsplitter and a trace over its output environment e. The inverse coordinate map is orthogonal, including the endpoints T=1 and T=0.
--   - `channelKernel`: PDF p.3, Eq.(3): complete phase-insensitive attenuator output on AB. A vacuum loss channel is followed by independent classical q,p displacements of variance T chiC-(1-T); these are channel noise, not trusted detector noise. This also includes additive noise at T=1, with no division by 1-T.
--   - `kernelCharacteristic`: PDF p.3: actual Weyl characteristic of a two-mode position kernel. For [q,p]=2i, midpoint coordinates give K(q+u_p,q-u_p) exp(i u_q q). The coordinate order in u is (q_A,p_A,q_B,p_B).
--   - `kernelMean`: PDF p.3: actual first moment from the Weyl characteristic derivative.
--   - `kernelCovariance`: PDF p.3: symmetrized covariance from first and second characteristic moments. Targets conclude smoothness, excluding total-derivative defaults.
--   - `abCovariance`: PDF p.3, Eq.(3): the displayed matrix, independently of the actual channel.
--   - `keyJointLaw`: PDF pp.2–3: selected-quadrature joint law, after announcing r and retaining just its matching Bob component, with gain already calibrated. Alice's displacement has variance V-1/V. The independent noise combines the squeezed quadrature (1/V), input-referred channel noise, and Bob-referred trusted detector noise. Both bases have this same law.
--   - `mutualInformationBits`: PDF p.3, Eq.(4): Shannon mutual information of the actual joint law, as KL to the product of its marginals. Extended values stay extended. Division by ln 2 converts nats to bits; no Gaussian rate formula is a definition.
--   - `positionNumberWave`: PDF p.3, Eq.(5): the accepted complete Hermite basis, rescaled from vacuum position variance 1/2 to the present shot-noise variance 1.
--   - `twoModeNumberWave`: PDF p.3: tensor-product full number basis on L²(R²).
--   - `numberCoefficients`: PDF p.3, Eq.(5): actual integral-operator matrix elements in the full Hermite basis. The integrals, not the covariance formula, determine this density. Integrability and positive trace-one nuclearity are conclusions of the target.
--   - `kernelEntropyBits`: PDF p.3, Eq.(5): actual entropy in bits, by the accepted extended finite-compression von Neumann entropy of the full operator.
--   - `sourceOmega`: PDF p.3: the canonical symplectic matrix in the source coordinate order.
--   - `abDelta`: PDF p.3, Eq.(6): Delta=x²+y²-2z² of the independently displayed CM.
--   - `abD`: PDF p.3, Eq.(6): D=xy-z², so det gamma_AB=D².
--   - `abLambda`: PDF p.3, Eq.(6): nonnegative ordered symplectic root; true selects lambda_1 (the plus sign), false lambda_2. This defines only the displayed scalar; the symplectic and entropy identifications are theorem conclusions.
--   - `AFGPosition`: PDF pp.3–4: the three retained positions (q_A,q_F,q_G).
--   - `afgUnnormalized`: PDF pp.3–4, Fig.3: the actual unnormalized AFG density after the trusted EPR(N) beamsplitter, Bob's q homodyne, and classical gain 1/sqrt(TB). The factor sqrt(TB) is the Born-density Jacobian for the rescaled outcome b. F and G are retained locally, and are not assigned to Eve.
--   - `afgBornDensity`: PDF pp.3–4: actual outcome density, obtained by tracing AFG.
--   - `afgPosterior`: PDF pp.3–4: normalized actual conditional density, not a covariance or entropy selected by the proposed formula. Born positivity is concluded.
--   - `detectorNoise`: PDF p.3, Fig.3: detector-referred noise; TB=0 is off domain.
--   - `conditionalA`: PDF p.4, Eq.(7): the independently displayed coefficient A.
--   - `conditionalB`: PDF p.4, Eq.(8): the independently displayed coefficient B.
--   - `conditionalLambda`: PDF p.4, Eqs.(7)–(8): the two nontrivial symplectic roots. The third AFG root is 1; no mode is discarded from the density.
--   - `afgNumberWave`: PDF pp.3–4: the complete tensor-product number basis of AFG.
--   - `afgNumberCoefficients`: PDF pp.3–4: actual three-mode integral-operator coefficients.
--   - `afgEntropyBits`: PDF pp.3–4: independent von Neumann entropy of the actual AFG posterior.
--   - `afgCharacteristic`: PDF pp.3–4: actual three-mode Weyl characteristic in A,F,G order.
--   - `afgCovariance`: PDF pp.3–4: centered second moments of the actual three-mode posterior. Conditional means are subtracted, so dependence of means on b is allowed.
--   - `afgOmega`: PDF pp.3–4: canonical symplectic form for all three AFG modes.
-- source:
--   Continuous-variable quantum key distribution protocols over noisy channels, arXiv:0806.3954v2, https://arxiv.org/abs/0806.3954v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P30

/-!
García-Patrón and Cerf, arXiv:0806.3954v2, PDF pp.2–4.
Complete Schrödinger integral kernels on L²(R^m); no photon cutoff.
Shot-noise units [q,p]=2i, vacuum covariance I, order (q_A,p_A,q_B,p_B).
The kernel-density criterion below is continuous positive definiteness and
integrable diagonal of integral one, hence specifies a positive trace-class
integral operator. It is independent of covariance and entropy formulas.
Every state identity below concerns the constructed full kernel.
Information and entropies use bits; accepted spectral entropy is converted
from nats. No security/capacity theorem
or reduction from Gaussian collective attacks to general attacks is asserted.
Compilation is pending the separate mechanical batch handoff.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P05

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: centered normal law, including the Dirac law when v=0.
Negative variances are a total off-domain extension and never used in targets. -/
def normalLaw (v : ℝ) : Measure ℝ := gaussianReal 0 v.toNNReal

/-- PDF p.3: ordinary normal density; used only at strictly positive variance. -/
def normalPDF (v x : ℝ) : ℝ := gaussianPDFReal 0 v.toNNReal x

/-- PDF pp.2–3: density criterion for the full continuous integral kernel.
Unlike frozen Dependency50.P17.IsDensityKernel, its arguments are a measure
and a position kernel; it does not use counting-measure basis coefficients.
Positivity tests all finite Gram matrices; normalization is an actual Lebesgue
trace integral. No covariance, spectrum, or proposed identity is a field. -/
def IsContinuousDensityKernel {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (mu : Measure X) (K : X → X → ℂ) : Prop :=
  Continuous (fun p : X × X => K p.1 p.2) ∧
  (∀ x y, K x y = star (K y x)) ∧
  (∀ (s : Finset X) (c : X → ℂ),
    (∑ x ∈ s, ∑ y ∈ s, star (c x) * K x y * c y).im = 0 ∧
    0 ≤ (∑ x ∈ s, ∑ y ∈ s, star (c x) * K x y * c y).re) ∧
  Integrable (fun x => (K x x).re) mu ∧ (∫ x, (K x x).re ∂mu) = 1

/-- PDF p.2: displacement-modulated squeezed wavefunction in position space.
False selects q squeezing, true p squeezing. Position variance is 1/V or V;
p displacement a has the phase exp(i a q/2) in the vacuum-I convention. -/
def squeezedWave (V : ℝ) (r : Bool) (a q : ℝ) : ℂ :=
  let s : ℝ := if r then V else 1 / V
  let m : ℝ := if r then 0 else a
  ((Real.sqrt (Real.sqrt (2 * Real.pi * s)))⁻¹ : ℂ) *
    Complex.exp (((-(q - m) ^ 2 / (4 * s) : ℝ) : ℂ) +
      Complex.I * ((if r then a * q / 2 else 0 : ℝ) : ℂ))

/-- PDF p.2: actual pure emitted density kernel, independent of global phase. -/
def preparedKernel (V : ℝ) (r : Bool) (a : ℝ) : ℝ → ℝ → ℂ :=
  fun q t => squeezedWave V r a q * star (squeezedWave V r a t)

/-- PDF p.2: ensemble average over Alice's Gaussian displacement. -/
def averagedKernel (V Va : ℝ) (r : Bool) : ℝ → ℝ → ℂ :=
  fun q t => ∫ a, preparedKernel V r a q t ∂normalLaw Va

/-- PDF p.2: position kernel of the centered one-mode thermal density,
quadrature variance V. This is not defined by the ensemble identity.
Frozen Gap48.P26.thermalKernel instead takes mean photon number and returns
number-basis coefficients on Nat; these are different representations. -/
def thermalPositionKernel (V : ℝ) : ℝ → ℝ → ℂ :=
  fun q t => ((Real.sqrt (2 * Real.pi * V))⁻¹ : ℂ) *
    Complex.exp (((-(q + t) ^ 2 / (8 * V) - V * (q - t) ^ 2 / 8 : ℝ) : ℂ))

/-- PDF p.3, Fig.3: complete two-mode squeezed EPR wavefunction.
The q correlation is +sqrt(V²-1), and the p correlation has the opposite sign. -/
def eprWave (V : ℝ) (x : ℝ × ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * Complex.exp
    (((-(V * (x.1 ^ 2 + x.2 ^ 2) -
      2 * Real.sqrt (V ^ 2 - 1) * x.1 * x.2) / 4 : ℝ) : ℂ))

/-- PDF p.3, Fig.3: actual initial rank-one EPR density. -/
def eprKernel (V : ℝ) : (ℝ × ℝ) → (ℝ × ℝ) → ℂ :=
  fun x y => eprWave V x * star (eprWave V y)

/-- PDF p.3, Fig.3: q_A homodyne is evaluation; p_A homodyne uses the
unitary Fourier convention exp(-i x s/2)/sqrt(4 pi). The outcome is x. -/
def measuredEprWave (V : ℝ) (r : Bool) (x q : ℝ) : ℂ :=
  if r then
    ((Real.sqrt (4 * Real.pi))⁻¹ : ℂ) *
      ∫ s : ℝ, Complex.exp (-Complex.I * ((x * s / 2 : ℝ) : ℂ)) * eprWave V (s, q)
  else eprWave V (x, q)

/-- PDF p.3, Fig.3: actual homodyne Born density, computed from the wave. -/
def eprBornDensity (V : ℝ) (r : Bool) (x : ℝ) : ℝ :=
  ∫ q : ℝ, Complex.normSq (measuredEprWave V r x q)

/-- PDF p.3, Fig.3: normalize the actual posterior by its own Born density.
The targets conclude that this denominator is strictly positive. -/
def eprPosteriorKernel (V : ℝ) (r : Bool) (x : ℝ) : ℝ → ℝ → ℂ :=
  fun q t => measuredEprWave V r x q * star (measuredEprWave V r x t) /
    (eprBornDensity V r x : ℂ)

/-- PDF p.3, Fig.3: the displacement induced on B by Alice's outcome x.
The minus sign for p is the EPR momentum anticorrelation. -/
def eprDisplacement (V : ℝ) (r : Bool) (x : ℝ) : ℝ :=
  (if r then -1 else 1) * Real.sqrt (V ^ 2 - 1) * x / V

/-- PDF p.3, Eq.(3): actual pure-loss channel on B, realized by a vacuum
beamsplitter and a trace over its output environment e. The inverse coordinate
map is orthogonal, including the endpoints T=1 and T=0. -/
def lossKernel (V T : ℝ) : (ℝ × ℝ) → (ℝ × ℝ) → ℂ :=
  fun x y => ∫ e : ℝ,
    eprKernel V
      (x.1, Real.sqrt T * x.2 - Real.sqrt (1 - T) * e)
      (y.1, Real.sqrt T * y.2 - Real.sqrt (1 - T) * e) *
    thermalPositionKernel 1
      (Real.sqrt (1 - T) * x.2 + Real.sqrt T * e)
      (Real.sqrt (1 - T) * y.2 + Real.sqrt T * e)

/-- PDF p.3, Eq.(3): complete phase-insensitive attenuator output on AB.
A vacuum loss channel is followed by independent classical q,p displacements
of variance T chiC-(1-T); these are channel noise, not trusted detector noise.
This also includes additive noise at T=1, with no division by 1-T. -/
def channelKernel (V T chiC : ℝ) : (ℝ × ℝ) → (ℝ × ℝ) → ℂ :=
  fun x y => ∫ uv : ℝ × ℝ,
    Complex.exp (Complex.I * ((uv.2 * (x.2 - y.2) / 2 : ℝ) : ℂ)) *
      lossKernel V T (x.1, x.2 - uv.1) (y.1, y.2 - uv.1)
    ∂(normalLaw (T * chiC - (1 - T))).prod (normalLaw (T * chiC - (1 - T)))

/-- PDF p.3: actual Weyl characteristic of a two-mode position kernel.
For [q,p]=2i, midpoint coordinates give K(q+u_p,q-u_p) exp(i u_q q).
The coordinate order in u is (q_A,p_A,q_B,p_B). -/
def kernelCharacteristic (K : (ℝ × ℝ) → (ℝ × ℝ) → ℂ)
    (u : Fin 4 → ℝ) : ℂ :=
  ∫ q : ℝ × ℝ, K (q.1 + u 1, q.2 + u 3) (q.1 - u 1, q.2 - u 3) *
    Complex.exp (Complex.I * ((u 0 * q.1 + u 2 * q.2 : ℝ) : ℂ))

/-- PDF p.3: actual first moment from the Weyl characteristic derivative. -/
def kernelMean (K : (ℝ × ℝ) → (ℝ × ℝ) → ℂ) (i : Fin 4) : ℝ :=
  (fderiv ℝ (kernelCharacteristic K) 0 (Pi.single i 1)).im

/-- PDF p.3: symmetrized covariance from first and second characteristic
moments. Targets conclude smoothness, excluding total-derivative defaults. -/
def kernelCovariance (K : (ℝ × ℝ) → (ℝ × ℝ) → ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    -((fderiv ℝ (fun u : Fin 4 → ℝ => fderiv ℝ (kernelCharacteristic K) u) 0)
      (Pi.single i 1) (Pi.single j 1)).re - kernelMean K i * kernelMean K j

/-- PDF p.3, Eq.(3): the displayed matrix, independently of the actual channel. -/
def abCovariance (V T chiC : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let z := Real.sqrt (T * (V ^ 2 - 1))
  let y := T * (V + chiC)
  !![V, 0, z, 0; 0, V, 0, -z; z, 0, y, 0; 0, -z, 0, y]

/-- PDF pp.2–3: selected-quadrature joint law, after announcing r and
retaining just its matching Bob component, with gain already calibrated.
Alice's displacement has variance V-1/V. The independent noise combines the
squeezed quadrature (1/V), input-referred channel noise, and Bob-referred
trusted detector noise. Both bases have this same law. -/
def keyJointLaw (V T chiC chiD : ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun an : ℝ × ℝ => (an.1, Real.sqrt T * an.1 + an.2))
    ((normalLaw (V - 1 / V)).prod (normalLaw (T * (1 / V + chiC) + chiD)))

/-- PDF p.3, Eq.(4): Shannon mutual information of the actual joint law,
as KL to the product of its marginals. Extended values stay extended.
Division by ln 2 converts nats to bits; no Gaussian rate formula is a definition. -/
def mutualInformationBits (mu : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  InformationTheory.klDiv mu
    ((Measure.map Prod.fst mu).prod (Measure.map Prod.snd mu)) /
      ENNReal.ofReal (Real.log 2)

/-- PDF p.3, Eq.(5): the accepted complete Hermite basis, rescaled from
vacuum position variance 1/2 to the present shot-noise variance 1. -/
def positionNumberWave (n : ℕ) (q : ℝ) : ℂ :=
  ((Real.sqrt (Real.sqrt 2))⁻¹ : ℂ) *
    QAlgorithms.Papers.Independent.Renew46.P19.hermiteFunction n
      (fun _ => q / Real.sqrt 2)

/-- PDF p.3: tensor-product full number basis on L²(R²). -/
def twoModeNumberWave (m : ℕ × ℕ) (x : ℝ × ℝ) : ℂ :=
  positionNumberWave m.1 x.1 * positionNumberWave m.2 x.2

/-- PDF p.3, Eq.(5): actual integral-operator matrix elements in the full
Hermite basis. The integrals, not the covariance formula, determine this density.
Integrability and positive trace-one nuclearity are conclusions of the target. -/
def numberCoefficients (K : (ℝ × ℝ) → (ℝ × ℝ) → ℂ) :
    Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun m n => ∫ xy : (ℝ × ℝ) × (ℝ × ℝ),
    star (twoModeNumberWave m xy.1) * K xy.1 xy.2 * twoModeNumberWave n xy.2

/-- PDF p.3, Eq.(5): actual entropy in bits, by the accepted extended
finite-compression von Neumann entropy of the full operator. -/
def kernelEntropyBits (K : (ℝ × ℝ) → (ℝ × ℝ) → ℂ) : ℝ≥0∞ :=
  QAlgorithms.Papers.Independent.Frontier18.P07.extendedEntropyNats
    (numberCoefficients K) / ENNReal.ofReal (Real.log 2)

/-- PDF p.3: the canonical symplectic matrix in the source coordinate order. -/
def sourceOmega : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

/-- PDF p.3, Eq.(6): Delta=x²+y²-2z² of the independently displayed CM. -/
def abDelta (V T chiC : ℝ) : ℝ :=
  V ^ 2 + (T * (V + chiC)) ^ 2 - 2 * T * (V ^ 2 - 1)

/-- PDF p.3, Eq.(6): D=xy-z², so det gamma_AB=D². -/
def abD (V T chiC : ℝ) : ℝ :=
  V * (T * (V + chiC)) - T * (V ^ 2 - 1)

/-- PDF p.3, Eq.(6): nonnegative ordered symplectic root; true selects
lambda_1 (the plus sign), false lambda_2. This defines only the displayed
scalar; the symplectic and entropy identifications are theorem conclusions. -/
def abLambda (V T chiC : ℝ) (upper : Bool) : ℝ :=
  Real.sqrt ((abDelta V T chiC + (if upper then 1 else -1) *
    Real.sqrt ((abDelta V T chiC) ^ 2 - 4 * (abD V T chiC) ^ 2)) / 2)

/-- PDF p.3, Eq.(5): the imported thermal entropy uses bits and G(0)=0. -/
example : thermalEntropyBits 0 = 0 := by
  simp [thermalEntropyBits]

example : abLambda 1 1 0 true = 1 := by
  norm_num [abLambda, abDelta, abD]

/-- PDF pp.3–4: the three retained positions (q_A,q_F,q_G). -/
abbrev AFGPosition := (ℝ × ℝ) × ℝ

/-- PDF pp.3–4, Fig.3: the actual unnormalized AFG density after the
trusted EPR(N) beamsplitter, Bob's q homodyne, and classical gain 1/sqrt(TB).
The factor sqrt(TB) is the Born-density Jacobian for the rescaled outcome b.
F and G are retained locally, and are not assigned to Eve. -/
def afgUnnormalized (V T chiC TB N b : ℝ) : AFGPosition → AFGPosition → ℂ :=
  fun x y => (Real.sqrt TB : ℂ) *
    channelKernel V T chiC
      (x.1.1, TB * b - Real.sqrt (1 - TB) * x.1.2)
      (y.1.1, TB * b - Real.sqrt (1 - TB) * y.1.2) *
    eprKernel N
      (Real.sqrt (1 - TB) * Real.sqrt TB * b + Real.sqrt TB * x.1.2, x.2)
      (Real.sqrt (1 - TB) * Real.sqrt TB * b + Real.sqrt TB * y.1.2, y.2)

/-- PDF pp.3–4: actual outcome density, obtained by tracing AFG. -/
def afgBornDensity (V T chiC TB N b : ℝ) : ℝ :=
  ∫ x : AFGPosition, (afgUnnormalized V T chiC TB N b x x).re

/-- PDF pp.3–4: normalized actual conditional density, not a covariance
or entropy selected by the proposed formula. Born positivity is concluded. -/
def afgPosterior (V T chiC TB N b : ℝ) : AFGPosition → AFGPosition → ℂ :=
  fun x y => afgUnnormalized V T chiC TB N b x y /
    (afgBornDensity V T chiC TB N b : ℂ)

/-- PDF p.3, Fig.3: detector-referred noise; TB=0 is off domain. -/
def detectorNoise (TB N : ℝ) : ℝ := (1 - TB) * N / TB

/-- PDF p.4, Eq.(7): the independently displayed coefficient A. -/
def conditionalA (V T chiC chiD : ℝ) : ℝ :=
  (T * (V + chiC) + V * abD V T chiC + chiD * abDelta V T chiC) /
    (T * (V + chiC) + chiD)

/-- PDF p.4, Eq.(8): the independently displayed coefficient B. -/
def conditionalB (V T chiC chiD : ℝ) : ℝ :=
  abD V T chiC * (V + chiD * abD V T chiC) / (T * (V + chiC) + chiD)

/-- PDF p.4, Eqs.(7)–(8): the two nontrivial symplectic roots.
The third AFG root is 1; no mode is discarded from the density. -/
def conditionalLambda (V T chiC chiD : ℝ) (upper : Bool) : ℝ :=
  Real.sqrt ((conditionalA V T chiC chiD + (if upper then 1 else -1) *
    Real.sqrt ((conditionalA V T chiC chiD) ^ 2 -
      4 * conditionalB V T chiC chiD)) / 2)

/-- PDF pp.3–4: the complete tensor-product number basis of AFG. -/
def afgNumberWave (m : (ℕ × ℕ) × ℕ) (x : AFGPosition) : ℂ :=
  twoModeNumberWave m.1 x.1 * positionNumberWave m.2 x.2

/-- PDF pp.3–4: actual three-mode integral-operator coefficients. -/
def afgNumberCoefficients (K : AFGPosition → AFGPosition → ℂ) :
    Matrix ((ℕ × ℕ) × ℕ) ((ℕ × ℕ) × ℕ) ℂ :=
  fun m n => ∫ xy : AFGPosition × AFGPosition,
    star (afgNumberWave m xy.1) * K xy.1 xy.2 * afgNumberWave n xy.2

/-- PDF pp.3–4: independent von Neumann entropy of the actual AFG posterior. -/
def afgEntropyBits (K : AFGPosition → AFGPosition → ℂ) : ℝ≥0∞ :=
  QAlgorithms.Papers.Independent.Frontier18.P07.extendedEntropyNats
    (afgNumberCoefficients K) / ENNReal.ofReal (Real.log 2)

/-- PDF pp.3–4: actual three-mode Weyl characteristic in A,F,G order. -/
def afgCharacteristic (K : AFGPosition → AFGPosition → ℂ) (u : Fin 6 → ℝ) : ℂ :=
  ∫ q : AFGPosition,
    K ((q.1.1 + u 1, q.1.2 + u 3), q.2 + u 5)
      ((q.1.1 - u 1, q.1.2 - u 3), q.2 - u 5) *
    Complex.exp (Complex.I * ((u 0 * q.1.1 + u 2 * q.1.2 + u 4 * q.2 : ℝ) : ℂ))

/-- PDF pp.3–4: centered second moments of the actual three-mode posterior.
Conditional means are subtracted, so dependence of means on b is allowed. -/
def afgCovariance (K : AFGPosition → AFGPosition → ℂ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j =>
    -((fderiv ℝ (fun u : Fin 6 → ℝ => fderiv ℝ (afgCharacteristic K) u) 0)
      (Pi.single i 1) (Pi.single j 1)).re -
    (fderiv ℝ (afgCharacteristic K) 0 (Pi.single i 1)).im *
      (fderiv ℝ (afgCharacteristic K) 0 (Pi.single j 1)).im

/-- PDF pp.3–4: canonical symplectic form for all three AFG modes. -/
def afgOmega : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => if i.val / 2 = j.val / 2 then
    if i = j then 0 else if i.val % 2 = 0 then 1 else -1
  else 0

example (TB : ℝ) : detectorNoise TB 1 = (1 - TB) / TB := by
  simp [detectorNoise]

example (N : ℝ) : detectorNoise 1 N = 0 := by simp [detectorNoise]

/-! Small physical sanity examples; no source theorem is proved here. -/

example : normalLaw 0 = Measure.dirac 0 := by simp [normalLaw]

example (q : ℝ) : squeezedWave 1 false 0 q = squeezedWave 1 true 0 q := by
  simp [squeezedWave]

example (r : Bool) (x : ℝ) : eprDisplacement 1 r x = 0 := by
  simp [eprDisplacement]

example (T chiC : ℝ) : abCovariance 1 T chiC 0 2 = 0 := by
  simp [abCovariance]

end QAlgorithms.Papers.Independent.Intake100.P05


