-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
-- name    : QAlgorithms_Papers_Independent_Claimed50_P35
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:26:42.219668+00:00
-- url     : https://prove2.me/theorems/3df46dc6-d76c-4944-b4ca-4ae2fff545fd
-- title:
--   Definitions for Evaluating Capacities of Bosonic Gaussian Channels
-- statement:
--   The objects the formalized statements of *Evaluating Capacities of Bosonic Gaussian Channels* (arXiv:quant-ph/9912067) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TraceLinear`: II.A--B, pp.2--3: linearity on full trace class, without CP.
--   - `stabilizedTraceClassNorm`: II.B, p.3: stabilized induced trace norm, no half; retains infinity.
--   - `transpose`: II.B, p.3: basis transpose on the complete operator space.
--   - `normLog2`: II.B, pp.3--4: base-two log on channel norms >=1; infinity is preserved. The total value at zero is unused for nonzero-system channels.
--   - `transposeBound`: II.B, (2.9), p.3: input transpose then channel.
--   - `traceClassTensorMap`: II.B, p.3: tensor product, retaining every off-diagonal block.
--   - `traceClassChannelPower`: II.B, p.3: memoryless powers, extending the accepted endomorphism-only interface to unequal input and output spaces.
--   - `EpsilonAttainable`: II.B, (2.7), p.3: every diverging block sequence of the specified rate admits fixed CPTP codes with eventual diamond error <=epsilon. Codes precede all logical inputs and reference systems, which the diamond norm quantifies.
--   - `VanishingAttainable`: II.B, p.3: the same operational definition with vanishing cb error.
--   - `epsilonCapacity`: II.B, p.3: extended supremum; empty rates give zero, unbounded rates infinity.
--   - `traceClassQuantumCapacity`: II.B, p.3: operational quantum capacity, in qubits per use.
--   - `tracePair`: II.A, p.2: trace-class/bounded pairing; row products precede the trace sum.
--   - `DensityOutcomeMeasurement`: II.B, p.4: POVM with actual countably additive outcome laws for every state. Their pairing with bounded effects expresses weak countable additivity. No discrete-outcome restriction is imposed.
--   - `MeasurePrepare`: II.B, p.4: measurement followed by preparation, including continuous outcomes. Coefficient integrability and actual normalized prepared densities exclude default-zero integrals.
--   - `InterleavedPhase`: III.A, pp.4--5: interleaved finite phase-space coordinates (mode,q/p).
--   - `physicalCommutationMatrix`: III.A, (3.14), p.4: the printed commutation matrix.
--   - `phaseArgument`: III.A, p.4: interleaved physical coordinates become the accepted grouped coordinates by multiplication by sqrt(hbar), so the CCR cocycle is unchanged.
--   - `ScaledWeylRepresentation`: III.A, (3.11)--(3.14), p.4: reuse the accepted regular irreducible Weyl system on a complete Hilbert space; only coordinates and hbar are adapted.
--   - `ScaledWeylRepresentation.operator`: III.A, p.4: bounded Weyl operator in the paper's physical coordinates.
--   - `weylTraceCharacteristic`: III.A, (3.17), p.4: characteristic function of an actual trace-class input.
--   - `gaussianFunction`: III.A, (3.17), p.4: Gaussian characteristic, allowing arbitrary mean.
--   - `MultimodeGaussianDensity`: III.A, p.4: a Gaussian is a normalized density, not an arbitrary symbol.
--   - `LinearBosonic`: IV.A, (4.35)--(4.36), pp.6--7: fixed Weyl law on every trace-class operator, equivalent to the normal dual law on bounded observables.
--   - `phaseSpaceShift`: IV.A(C), p.7: printed negative-sign shift convention.
--   - `unitaryTraceDilation`: IV.B, pp.7--8: reduction after a fixed unitary; unequal spaces are allowed.
--   - `CanonicalRows`: IV.B, (4.37), p.7: canonical system rows on bounded Weyl observables, independent of every input density.
--   - `weylDefectPair`: IV.D, (4.42), p.9: weylDefectPair bilinear form on output arguments.
--   - `generalizedThermal`: IV.D, (4.46), p.9: generalized thermal operator, possibly nonpositive.
--   - `NoiseNormalModes`: IV.D, p.9: normal-mode parameters belong to the weylDefectPair form. S is an actual invertible coordinate change, not an unrelated output covariance.
--   - `gaussianDisplacementLaw`: V.A, p.9: independent circular Gaussian noise; at Nc=0 use Dirac zero.
--   - `vacuumChannelTerm`: V.A, p.9: fixed vacuum ancillary mode, through accepted full Fock Kraus entries.
--   - `vacuumChannel`: V.A, p.9: full quantum-limited map; coefficient convergence is concluded below.
--   - `noisyChannel`: V.A, p.9: Gaussian displacements after the vacuum channel. Coefficient integrability is a conclusion, not an assumed default-zero integral.
--   - `oneModeCharacteristic`: III.A and V.A, pp.4,9: V(x,y)=D(i sqrt(hbar/2)(x+iy)).
--   - `vacuumOutput`: V.A, p.10: vacuum output photon number.
--   - `outputOccupation`: V.A, p.10: thermal output photon number.
--   - `exchangeD`: V.A, (5.49), p.10: complete radical.
--   - `thermalInput`: V.A, p.10: thermal state in the full Fock basis.
--   - `thermalPurificationDensity`: II.A and III.D, pp.2,6: actual rank-one thermal purification, with Schmidt coefficients the square roots of the number probabilities.
--   - `thermalExchangeOutput`: II.A, (2.2), p.2: actual joint output on the purification.
--   - `RealizedDensity`: II.A, p.2: actual normalized trace-class density and its bounded realization.
--   - `spectralEntropyBits`: II.A, (2.1), p.2: extended spectral entropy in bits, via continuous functional calculus of the actual bounded density. The function -x ln x is zero at zero. No covariance-only entropy or infinity-to-real default is used.
--   - `thermalCoherentInformation`: II.A and V.B, pp.2,11: thermal coherent information; all uses below have finite entropies, as the theorem conclusions explicitly establish.
--   - `coherentGaussianExpression`: V.A, p.10: scalar underlined coherent-Gaussian rate expression. This definition asserts no optimization over ensembles.
--   - `exchangeMatrix`: V.A, p.10: two-by-two complex representation of the real four-by-four exchange covariance operator; its two roots account for the paired real spectrum.
--   - `defectRescale`: V.B, (5.52), p.10: inverse weylDefectPair scale, including the amplifier reflection.
--   - `oneModeMultiplier`: V.A, (5.47), p.9: fixed Weyl multiplier, with physical hbar.
--   - `densityLine`: Appendix A, p.11: physical affine line in the real vector space of arrays.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, https://arxiv.org/abs/quant-ph/9912067v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

/-! Holevo--Werner, quant-ph/9912067v1. Full Hilbert-space trace class, no
photon cutoff. All new definitions are paper-local. Compilation and independent
moderation are pending. Deferred nodes are recorded individually in HARD.md. -/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)
open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-! The accepted `operatorCoeff` and `boundedOperator` are reused exactly.
Other flagged basenames denote different accepted objects: finite-matrix norms,
tensor maps and powers; finite-dimensional/fidelity capacities; finite POVMs;
a grouped phase INDEX; a one-mode Fock characteristic/Gaussian predicate; a
finite clock shift; an amplitude-damping dilation; entropy/trace defects; and a
purification COVARIANCE. The distinct names below retain this paper's full
trace-class domain, arbitrary outcome spaces and physical coordinates. The
scaled Weyl adapter contains the accepted regular irreducible Weyl system.
The positive-noise measure is imported; only its zero-noise Dirac endpoint is
added. See ASSESSMENT.json for declaration-specific type comparisons. -/

/-- II.A--B, pp.2--3: linearity on full trace class, without CP. -/
def TraceLinear {I J : Type} (T : Operation I J) : Prop :=
  (∀ X, IsTraceClass X → IsTraceClass (T X)) ∧
  (∀ X Y, IsTraceClass X → IsTraceClass Y → T (X + Y) = T X + T Y) ∧
  (∀ (c : ℂ) X, IsTraceClass X → T (c • X) = c • T X)

/-- II.B, p.3: stabilized induced trace norm, no half; retains infinity. -/
def stabilizedTraceClassNorm {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ X : {X : Matrix (I × Fin n) (I × Fin n) ℂ //
    IsTraceClass X ∧ traceSize X ≤ 1}, traceSize (tensorApply T X.val)

/-- II.B, p.3: basis transpose on the complete operator space. -/
def transpose {I : Type} (X : Matrix I I ℂ) : Matrix I I ℂ := fun i j => X j i

/-- II.B, pp.3--4: base-two log on channel norms >=1; infinity is preserved.
The total value at zero is unused for nonzero-system channels. -/
def normLog2 (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else ENNReal.ofReal (Real.logb 2 x.toReal)

/-- II.B, (2.9), p.3: input transpose then channel. -/
def transposeBound {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  normLog2 (stabilizedTraceClassNorm (T ∘ transpose))

/-- II.B, p.3: tensor product, retaining every off-diagonal block. -/
def traceClassTensorMap {I J K L : Type} (S : Operation I J) (T : Operation K L) :
    Operation (I × K) (J × L) :=
  fun X p q => S (fun i j => T (fun k l => X (i, k) (j, l)) p.2 q.2) p.1 q.1

/-- II.B, p.3: memoryless powers, extending the accepted endomorphism-only
interface to unequal input and output spaces. -/
def traceClassChannelPower {I J : Type} (T : Operation I J) :
    (m : ℕ) → Operation (Fin m → I) (Fin m → J)
  | 0 => fun X _ _ => X Fin.elim0 Fin.elim0
  | m + 1 => fun X a b => traceClassChannelPower T m
      (fun s t => T (fun i j => X (Fin.cons i s) (Fin.cons j t)) (a 0) (b 0))
      (Fin.tail a) (Fin.tail b)

/-- II.B, (2.7), p.3: every diverging block sequence of the specified rate
admits fixed CPTP codes with eventual diamond error <=epsilon. Codes precede
all logical inputs and reference systems, which the diamond norm quantifies. -/
def EpsilonAttainable {I J : Type} (T : Operation I J) (eps : ℝ) (r : ℝ≥0) : Prop :=
  ∀ n m : ℕ → ℕ, Tendsto m atTop atTop →
    Tendsto (fun a => (n a : ℝ) / (m a : ℝ)) atTop (𝓝 (r : ℝ)) →
    ∃ (E : (a : ℕ) → Operation (Fin (2 ^ n a)) (Fin (m a) → I))
      (D : (a : ℕ) → Operation (Fin (m a) → J) (Fin (2 ^ n a))),
      (∀ a, IsTraceClassChannel (E a) ∧ IsTraceClassChannel (D a)) ∧
      ∀ᶠ a in atTop, stabilizedTraceClassNorm
        (fun X => X - D a (traceClassChannelPower T (m a) (E a X))) ≤ ENNReal.ofReal eps

/-- II.B, p.3: the same operational definition with vanishing cb error. -/
def VanishingAttainable {I J : Type} (T : Operation I J) (r : ℝ≥0) : Prop :=
  ∀ n m : ℕ → ℕ, Tendsto m atTop atTop →
    Tendsto (fun a => (n a : ℝ) / (m a : ℝ)) atTop (𝓝 (r : ℝ)) →
    ∃ (E : (a : ℕ) → Operation (Fin (2 ^ n a)) (Fin (m a) → I))
      (D : (a : ℕ) → Operation (Fin (m a) → J) (Fin (2 ^ n a))),
      (∀ a, IsTraceClassChannel (E a) ∧ IsTraceClassChannel (D a)) ∧
      Tendsto (fun a => stabilizedTraceClassNorm
        (fun X => X - D a (traceClassChannelPower T (m a) (E a X)))) atTop (𝓝 0)

/-- II.B, p.3: extended supremum; empty rates give zero, unbounded rates infinity. -/
def epsilonCapacity {I J : Type} (T : Operation I J) (eps : ℝ) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ≥0 // EpsilonAttainable T eps r}, (r.val : ℝ≥0∞)

/-- II.B, p.3: operational quantum capacity, in qubits per use. -/
def traceClassQuantumCapacity {I J : Type} (T : Operation I J) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ≥0 // VanishingAttainable T r}, (r.val : ℝ≥0∞)

/-- II.A, p.2: trace-class/bounded pairing; row products precede the trace sum. -/
def tracePair {I : Type} (X A : Matrix I I ℂ) : ℂ := ∑' i, ∑' j, X i j * A j i

/-- II.B, p.4: POVM with actual countably additive outcome laws for every
state. Their pairing with bounded effects expresses weak countable additivity.
No discrete-outcome restriction is imposed. -/
structure DensityOutcomeMeasurement (I X : Type) [MeasurableSpace X] where
  povm : QAlgorithms.Papers.Independent.Frontier30.P10.HilbertPOVM (Hilbert I) X
  law : State I → Measure X
  probability : ∀ rho, IsProbabilityMeasure (law rho)
  law_eq : ∀ rho A, MeasurableSet A →
    law rho A = ENNReal.ofReal (tracePair rho.coefficients (operatorCoeff (povm.effect A))).re

/-- II.B, p.4: measurement followed by preparation, including continuous
outcomes. Coefficient integrability and actual normalized prepared densities
exclude default-zero integrals. -/
def MeasurePrepare {I J : Type} (T : Operation I J) : Prop :=
  ∃ (X : Type) (mX : MeasurableSpace X) (M : @DensityOutcomeMeasurement I X mX)
    (sigma : X → State J),
    (∀ i j, @Measurable X ℂ mX inferInstance (fun x => (sigma x).coefficients i j)) ∧
    ∀ rho : State I, @IsBarycenter J X mX (M.law rho)
      (fun x => (sigma x).coefficients) (T rho.coefficients)

example {I : Type} (X : Matrix I I ℂ) : transpose (transpose X) = X := by rfl

example {I J : Type} (T : Operation I J)
    (X : Matrix (Fin 0 → I) (Fin 0 → I) ℂ) (a b : Fin 0 → J) :
    traceClassChannelPower T 0 X a b = X Fin.elim0 Fin.elim0 := by rfl

example : normLog2 ⊤ = ⊤ := by simp [normLog2]

/-- III.A, pp.4--5: interleaved finite phase-space coordinates (mode,q/p). -/
abbrev InterleavedPhase (s : ℕ) := (Fin s × Fin 2) → ℝ

/-- III.A, (3.14), p.4: the printed commutation matrix. -/
def physicalCommutationMatrix (s : ℕ) (hbar : ℝ) : Matrix (Fin s × Fin 2) (Fin s × Fin 2) ℝ :=
  fun i j => if i.1 = j.1 then
    if i.2 = 0 ∧ j.2 = 1 then hbar
    else if i.2 = 1 ∧ j.2 = 0 then -hbar else 0 else 0

/-- III.A, p.4: interleaved physical coordinates become the accepted grouped
coordinates by multiplication by sqrt(hbar), so the CCR cocycle is unchanged. -/
def phaseArgument {s : ℕ} (hbar : ℝ) (z : InterleavedPhase s) :
    QAlgorithms.Papers.Independent.Dependency50.P10.Phase s → ℝ :=
  fun i => match i with
    | Sum.inl j => Real.sqrt hbar * z (j, 0)
    | Sum.inr j => Real.sqrt hbar * z (j, 1)

/-- III.A, (3.11)--(3.14), p.4: reuse the accepted regular irreducible
Weyl system on a complete Hilbert space; only coordinates and hbar are adapted. -/
structure ScaledWeylRepresentation (I : Type) (s : ℕ) (hbar : ℝ) where
  hbar_pos : 0 < hbar
  normalized : QAlgorithms.Papers.Independent.Frontier30.P10.WeylSystem (Hilbert I) s

/-- III.A, p.4: bounded Weyl operator in the paper's physical coordinates. -/
def ScaledWeylRepresentation.operator {I : Type} {s : ℕ} {hbar : ℝ}
    (W : ScaledWeylRepresentation I s hbar) (z : InterleavedPhase s) : Hilbert I →L[ℂ] Hilbert I :=
  (W.normalized.operator (phaseArgument hbar z)).toLinearIsometry.toContinuousLinearMap

example {s : ℕ} : phaseArgument (s := s) 1 0 = 0 := by
  funext i
  cases i <;> simp [phaseArgument]

/-- III.A, (3.17), p.4: characteristic function of an actual trace-class input. -/
def weylTraceCharacteristic {I : Type} {s : ℕ} {hbar : ℝ}
    (W : ScaledWeylRepresentation I s hbar) (X : Matrix I I ℂ) (z : InterleavedPhase s) : ℂ :=
  tracePair X (operatorCoeff (W.operator z))

/-- III.A, (3.17), p.4: Gaussian characteristic, allowing arbitrary mean. -/
def gaussianFunction {s : ℕ} (m : InterleavedPhase s)
    (alpha : Matrix (Fin s × Fin 2) (Fin s × Fin 2) ℝ) (z : InterleavedPhase s) : ℂ :=
  Complex.exp (Complex.I * ((dotProduct m z : ℝ) : ℂ) -
    ((dotProduct z (alpha.mulVec z) / 2 : ℝ) : ℂ))

/-- III.A, p.4: a Gaussian is a normalized density, not an arbitrary symbol. -/
def MultimodeGaussianDensity {I : Type} {s : ℕ} {hbar : ℝ}
    (W : ScaledWeylRepresentation I s hbar) (X : Matrix I I ℂ) : Prop :=
  IsDensity X ∧ ∃ m alpha, alpha.transpose = alpha ∧
    ∀ z, weylTraceCharacteristic W X z = gaussianFunction m alpha z

/-- IV.A, (4.35)--(4.36), pp.6--7: fixed Weyl law on every trace-class
operator, equivalent to the normal dual law on bounded observables. -/
def LinearBosonic {I J : Type} {s t : ℕ} {hbar : ℝ}
    (W : ScaledWeylRepresentation I s hbar) (Wout : ScaledWeylRepresentation J t hbar)
    (T : Operation I J) (K : Matrix (Fin t × Fin 2) (Fin s × Fin 2) ℝ)
    (f : InterleavedPhase t → ℂ) : Prop :=
  ∀ X, IsTraceClass X → ∀ z,
    weylTraceCharacteristic Wout (T X) z = weylTraceCharacteristic W X (K.transpose.mulVec z) * f z

/-- IV.A(C), p.7: printed negative-sign shift convention. -/
def phaseSpaceShift {I : Type} {s : ℕ} {hbar : ℝ} (W : ScaledWeylRepresentation I s hbar)
    (z : InterleavedPhase s) (X : Matrix I I ℂ) : Matrix I I ℂ :=
  conjugateKernel (operatorCoeff (W.operator (-((physicalCommutationMatrix s hbar)⁻¹.mulVec z)))) X

example : physicalCommutationMatrix 1 2 (0, 0) (0, 1) = 2 := by norm_num [physicalCommutationMatrix]

example {s : ℕ} : gaussianFunction (0 : InterleavedPhase s) 0 0 = 1 := by
  simp [gaussianFunction]

/-- IV.B, pp.7--8: reduction after a fixed unitary; unequal spaces are allowed. -/
def unitaryTraceDilation {I J E F : Type}
    (U : Hilbert (I × E) ≃ₗᵢ[ℂ] Hilbert (J × F)) (sigma : Matrix E E ℂ) : Operation I J :=
  fun X => partialRight (conjugateKernel (isometryCoeff U.toLinearIsometry)
    (productCoeff X sigma))

/-- IV.B, (4.37), p.7: canonical system rows on bounded Weyl observables,
independent of every input density. -/
def CanonicalRows {I J E F : Type} {s t e : ℕ} {hbar : ℝ}
    (W : ScaledWeylRepresentation I s hbar) (Wout : ScaledWeylRepresentation J t hbar) (WE : ScaledWeylRepresentation E e hbar)
    (U : Hilbert (I × E) ≃ₗᵢ[ℂ] Hilbert (J × F))
    (K : Matrix (Fin t × Fin 2) (Fin s × Fin 2) ℝ)
    (KE : Matrix (Fin t × Fin 2) (Fin e × Fin 2) ℝ) : Prop :=
  ∀ z, composeKernel (isometryCoeff U.symm.toLinearIsometry)
    (composeKernel (productCoeff (operatorCoeff (Wout.operator z)) (identityCoeff F))
      (isometryCoeff U.toLinearIsometry)) =
    productCoeff (operatorCoeff (W.operator (K.transpose.mulVec z)))
      (operatorCoeff (WE.operator (KE.transpose.mulVec z)))

example {I J E F : Type} (U : Hilbert (I × E) ≃ₗᵢ[ℂ] Hilbert (J × F))
    (sigma : Matrix E E ℂ) (X : Matrix I I ℂ) :
    unitaryTraceDilation U sigma X = partialRight
      (conjugateKernel (isometryCoeff U.toLinearIsometry) (productCoeff X sigma)) := by rfl

/-- IV.D, (4.42), p.9: weylDefectPair bilinear form on output arguments. -/
def weylDefectPair {s : ℕ} (hbar : ℝ)
    (K : Matrix (Fin s × Fin 2) (Fin s × Fin 2) ℝ) (z w : InterleavedPhase s) : ℝ :=
  dotProduct z ((physicalCommutationMatrix s hbar).mulVec w) -
    dotProduct (K.transpose.mulVec z) ((physicalCommutationMatrix s hbar).mulVec (K.transpose.mulVec w))

/-- IV.D, (4.46), p.9: generalized thermal operator, possibly nonpositive. -/
def generalizedThermal (gamma : ℝ) : Matrix ℕ ℕ ℂ := thermalMatrix (2 * gamma)

example : generalizedThermal (1 / 2) 0 0 = 1 := by
  norm_num [generalizedThermal, thermalMatrix]

/-- IV.D, p.9: normal-mode parameters belong to the weylDefectPair form. S is an
actual invertible coordinate change, not an unrelated output covariance. -/
def NoiseNormalModes {s : ℕ} (hbar : ℝ)
    (K B : Matrix (Fin s × Fin 2) (Fin s × Fin 2) ℝ)
    (S : InterleavedPhase s ≃ₗ[ℝ] InterleavedPhase s) (gamma : Fin s → ℝ) : Prop :=
  (∀ j, 0 < gamma j) ∧
  (∀ z w, weylDefectPair hbar K (S z) (S w) = dotProduct z ((physicalCommutationMatrix s hbar).mulVec w)) ∧
  ∀ z, dotProduct (S z) (B.mulVec (S z)) =
    hbar * ∑ j : Fin s, gamma j * (z (j, 0) ^ 2 + z (j, 1) ^ 2)

/-- V.A, p.9: independent circular Gaussian noise; at Nc=0 use Dirac zero. -/
def gaussianDisplacementLaw (Nc : ℝ) : Measure ℂ :=
  if Nc = 0 then Measure.dirac 0
  else QAlgorithms.Papers.Independent.Frontier30.P07.noiseMeasure Nc

example : gaussianDisplacementLaw 0 = Measure.dirac 0 := by
  simp [gaussianDisplacementLaw]

/-- V.A, p.9: fixed vacuum ancillary mode, through accepted full Fock Kraus entries. -/
def vacuumChannelTerm (k : ℝ) (ell : ℕ) (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  conjugateKernel (if k ≤ 1 then attenuatorMatrix k ell else amplifierMatrix k ell) X

/-- V.A, p.9: full quantum-limited map; coefficient convergence is concluded below. -/
def vacuumChannel (k : ℝ) : Operation ℕ ℕ :=
  fun X i j => ∑' ell : ℕ, vacuumChannelTerm k ell X i j

/-- V.A, p.9: Gaussian displacements after the vacuum channel. Coefficient
integrability is a conclusion, not an assumed default-zero integral. -/
def noisyChannel (k Nc : ℝ) : Operation ℕ ℕ :=
  fun X i j => ∫ z, conjugateKernel (displacementMatrix z) (vacuumChannel k X) i j
    ∂gaussianDisplacementLaw Nc

/-- III.A and V.A, pp.4,9: V(x,y)=D(i sqrt(hbar/2)(x+iy)). -/
def oneModeCharacteristic (hbar : ℝ) (X : Matrix ℕ ℕ ℂ) (z : ℂ) : ℂ :=
  tracePair X (displacementMatrix (Complex.I * (Real.sqrt (hbar / 2) : ℂ) * z))

/-- V.A, p.10: vacuum output photon number. -/
def vacuumOutput (k Nc : ℝ) : ℝ := max 0 (k ^ 2 - 1) + Nc

/-- V.A, p.10: thermal output photon number. -/
def outputOccupation (N k Nc : ℝ) : ℝ := k ^ 2 * N + vacuumOutput k Nc

/-- V.A, (5.49), p.10: complete radical. -/
def exchangeD (N k Nc : ℝ) : ℝ :=
  Real.sqrt ((N + outputOccupation N k Nc + 1) ^ 2 - 4 * k ^ 2 * N * (N + 1))

/-- V.A, p.10: thermal state in the full Fock basis. -/
def thermalInput (N : ℝ) : Matrix ℕ ℕ ℂ := thermalMatrix (2 * N + 1)

/-- II.A and III.D, pp.2,6: actual rank-one thermal purification, with
Schmidt coefficients the square roots of the number probabilities. -/
def thermalPurificationDensity (N : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then
    ((Real.sqrt ((thermalInput N) p.1 p.1).re *
      Real.sqrt ((thermalInput N) q.1 q.1).re : ℝ) : ℂ) else 0

/-- II.A, (2.2), p.2: actual joint output on the purification. -/
def thermalExchangeOutput (N k Nc : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  tensorApply (noisyChannel k Nc) (thermalPurificationDensity N)

/-- II.A, p.2: actual normalized trace-class density and its bounded realization. -/
def RealizedDensity {I : Type} (X : Matrix I I ℂ) : Prop :=
  IsDensity X ∧ operatorCoeff (boundedOperator X) = X

/-- II.A, (2.1), p.2: extended spectral entropy in bits, via continuous
functional calculus of the actual bounded density. The function -x ln x is
zero at zero. No covariance-only entropy or infinity-to-real default is used. -/
def spectralEntropyBits {I : Type} (X : Matrix I I ℂ) : ℝ≥0∞ :=
  (∑' i : I, ENNReal.ofReal ((cfc (fun z : ℂ => ((-z.re * Real.log z.re : ℝ) : ℂ))
    (boundedOperator X)) (lp.single 2 i 1) i).re) / ENNReal.ofReal (Real.log 2)

/-- II.A and V.B, pp.2,11: thermal coherent information; all uses below have
finite entropies, as the theorem conclusions explicitly establish. -/
def thermalCoherentInformation (N k Nc : ℝ) : ℝ :=
  (spectralEntropyBits (noisyChannel k Nc (thermalInput N))).toReal -
    (spectralEntropyBits (thermalExchangeOutput N k Nc)).toReal

/-- V.A, p.10: scalar underlined coherent-Gaussian rate expression. This
definition asserts no optimization over ensembles. -/
def coherentGaussianExpression (N k Nc : ℝ) : ℝ :=
  bosonicEntropy (outputOccupation N k Nc) - bosonicEntropy (vacuumOutput k Nc)

example : vacuumOutput 0 0 = 0 := by norm_num [vacuumOutput]

example (N : ℝ) : outputOccupation N 1 0 = N := by
  simp [outputOccupation, vacuumOutput]

example : thermalInput 0 0 0 = 1 := by norm_num [thermalInput, thermalMatrix]

example (k Nc : ℝ) : coherentGaussianExpression 0 k Nc = 0 := by
  simp [coherentGaussianExpression, outputOccupation]

example (N : ℝ) : thermalPurificationDensity N (0, 1) (0, 0) = 0 := by
  simp [thermalPurificationDensity]

/-- V.A, p.10: two-by-two complex representation of the real four-by-four
exchange covariance operator; its two roots account for the paired real spectrum. -/
def exchangeMatrix (N k Nc : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![Complex.I * ((outputOccupation N k Nc + 1 / 2 : ℝ) : ℂ),
       ((k * Real.sqrt (N * (N + 1)) : ℝ) : ℂ)],
    ![((k * Real.sqrt (N * (N + 1)) : ℝ) : ℂ), -Complex.I * ((N + 1 / 2 : ℝ) : ℂ)]]

/-- V.B, (5.52), p.10: inverse weylDefectPair scale, including the amplifier reflection. -/
def defectRescale (k : ℝ) (z : ℂ) : ℂ :=
  (if k ≤ 1 then z else star z) / (Real.sqrt |k ^ 2 - 1| : ℂ)

/-- V.A, (5.47), p.9: fixed Weyl multiplier, with physical hbar. -/
def oneModeMultiplier (k Nc hbar : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((-hbar / 2 * (|k ^ 2 - 1| / 2 + Nc) * Complex.normSq z : ℝ) : ℂ))

example (z : ℂ) : defectRescale 0 z = z := by simp [defectRescale]

/-- Appendix A, p.11: physical affine line in the real vector space of arrays. -/
def densityLine {I : Type} (rho sigma : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  (1 - t) • rho + t • sigma

example {I : Type} (rho sigma : Matrix I I ℂ) : densityLine rho sigma 0 = rho := by
  simp [densityLine]

end QAlgorithms.Papers.Independent.Claimed50.P35


