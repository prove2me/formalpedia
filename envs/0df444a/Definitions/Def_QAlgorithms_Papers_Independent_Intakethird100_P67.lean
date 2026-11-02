-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P67
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:50:05.438736+00:00
-- url     : https://prove2.me/theorems/c6016b4d-705d-4155-bf0b-a1a030ec9756
-- title:
--   Definitions for Universal Quantum Emulator
-- statement:
--   The objects the formalized statements of *Universal Quantum Emulator* (arXiv:1606.02734) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `densityConjugation`: PDF p.2: unitary conjugation, also for subnormalized branches.
--   - `sampleAlgebra`: PDF p.2: complex span of all nonempty sample words (supported nonunital algebra).
--   - `samplePi`: PDF p.2: the support projector of the sum of PSD sample densities is the projector onto the span of their supports. CFC is evaluated on a finite spectrum.
--   - `Generates`: PDF p.2, Eq.(6): equality with the full supported matrix algebra.
--   - `InSampleSupport`: PDF p.2: density support contained in the input span.
--   - `sampleDimension`: PDF p.2, Eq.(2): dimension of the sample support.
--   - `pureSamples`: PDF p.2: pure sample density records.
--   - `sampleReflection`: PDF p.3, Eq.(9): the sample reflection sign is I-2P.
--   - `systemControlled`: PDF p.3, Eq.(10): frozen control-first gate reindexed into system-first order.
--   - `erasureGate`: PDF p.3, Eq.(11), R(k) H R(anchor), with the rightmost gate first.
--   - `minusRegister`: PDF p.4: |minus> tensor T, including the empty tensor.
--   - `minusVector`: PDF p.3: the normalized one-qubit |minus>.
--   - `onAncilla`: PDF p.4: a system/one-qubit operator placed on ancilla j.
--   - `historyUnitary`: PDF p.13: ordered forward history, recalled unchanged in the reverse circuit.
--   - `historyWeight`: PDF p.14: iid history weight.
--   - `coherentErasureChannel`: PDF p.14, A5: the generalized averaged erasure channel.
--   - `nonanchorProbability`: PDF pp.4–5: fixed anchor excluded from the uniform random indices.
--   - `jointBranchHistory`: PDF pp.13–16: a Fig.5 branch, including measurement, replacement of the system by the output anchor, then reverse output history. False means b=0.
--   - `jointBranch`: PDF p.14: averaged subnormalized joint branch.
--   - `jointEmulator`: PDF p.14, A10: nonselective joint output in the Appendix A convention.
--   - `transportedGate`: PDF pp.6,15, Eq.(18)/A12: covariance has U-dagger on the right, correcting printed A1's U. This does not impose U squared equal to the identity.
--   - `eraseProbability`: PDF p.6, Eq.(20): actual erasure success probability.
--   - `emulate`: PDF p.6: pure-sample main-system emulator, Appendix A output convention.
--   - `compressedReflection`: PDF p.7, Eq.(25): compression to H_in intersect anchor-perp.
--   - `compressedReflectionChannel`: PDF p.7, Eq.(24): compressed sampleReflection channel.
--   - `lambdaPerp`: PDF p.7, Eq.(26): norm of the vectorized compressed channel.
--   - `residual`: PDF p.8, Eq.(35): exact, unnormalized residual.
--   - `unaryWord`: PDF p.8: unary address, including residual t=T.
--   - `coordinateExpansion`: PDF p.8, Eq.(34): the full expansion retains its residual term.
--   - `meanSampleDensity`: PDF p.32, H3: average sample density.
--   - `projectionBranch`: PDF pp.31–32: actual Fig.7 branch. Same history is used forward and backward; false is span detection, true is the all-minus outcome.
--   - `projectionChannel`: PDF p.32: channel discarding the Fig.7 label.
--   - `gentleChannel`: PDF p.33, H19: randomized conjugated projective measurement.
--   - `gentleProbability`: PDF p.34, H21: actual expected outcome probability.
--   - `ProjectiveFamily`: PDF p.33: complete orthogonal projectors; zero projectors are allowed.
--   - `positivePhaseEvolution`: PDF p.20: positive-sign matrix exponential, e^(i theta H).
--   - `pureFisherInformation`: PDF pp.7–8, Eq.(31): quantum Fisher information of a differentiable normalized pure-state family. The theorem uses the actual analytic exp(i alpha P) family, so no nondifferentiability default of deriv is involved.
--   - `referenceVector`: PDF p.24: n independently prepared pure reference registers.
--   - `swapReference`: PDF p.24, E1: SWAP of system with reference j, identity on other references.
--   - `swapHamiltonian`: PDF p.24, E1: full continuous interaction.
--   - `swapJoint`: PDF p.24, E2: actual joint positivePhaseEvolution.
--   - `effectiveHamiltonian`: PDF p.24, E3: effective Hamiltonian with the n+1 coefficient.
--   - `wireBranch`: PDF p.4, Fig.2: unsuccessful output is the old system wire from the SWAP. The successful wire is reconstructed. These differ from Appendix A on failure.
--   - `mixedGate`: PDF p.28, G1: systemControlled density-matrix translations.
--   - `mixedSampleErasureChannel`: PDF p.28: entrywise Lebesgue integration of the continuous one-round body. For density samples the matrix exponential body is continuous on the compact interval.
--   - `mixedHistory`: PDF p.28: history unitary for fixed mixed-sample indices and real times.
--   - `mixedHistoryOutput`: PDF p.28: fixed mixed-history output after system replacement and reconstruction.
--   - `mixedEmulate`: PDF p.28: actual mixed-sample emulator, with independent uniform times and indices. Entrywise integrals are over a compact cube of a continuous finite-matrix body.
--   - `bridgeSamples`: PDF p.28, G2: tagged sample densities plus a pure bridge (none).
--   - `conjugateBasis`: PDF p.29, G3: positive-sign Fourier-densityConjugation basis.
--   - `uniformAddress`: PDF pp.29–30: normalized uniform address state.
--   - `negativeFourier`: PDF p.30, G7: negative-sign normalized DFT. This corrects G7's missing normalization and ket index; G6 and G11 determine this sign.
--   - `basisPhase`: PDF pp.29–30, G4/G8: full spectral exponential, hence identity on H_in-perp.
--   - `increment`: PDF p.22, D5: cyclic increment on the binary address.
--   - `binaryMeasure`: PDF p.22, D6: Fig.6 effective operation on system/address, with the helper returned to |minus>. The address is initialized at zero, correcting D8's printed |t>.
--   - `addressedReflection`: PDF p.23, D7: address-selective sampleReflection; t is a natural address.
--   - `binaryHistory`: PDF pp.22–23: actual binary history F(t+1,k) V, using addresses 1 through T.
--   - `encodeUnary`: PDF pp.22–23: linear reencoding of the unary subspace, extended by zero elsewhere.
--   - `registerSwap`: PDF p.11: SWAP between two equal-dimensional registers.
--   - `doubleControlledSwap`: PDF p.11: double-systemControlled full-register SWAP, with both controls ancillary.
--   - `ElementaryGate`: PDF pp.19–21: source elementary gate set, one-qubit unitaries and two-control SWAPs acting on four distinct qubit wires.
--   - `elementaryMatrix`: PDF pp.19–21: complete matrix semantics of the counted elementary gates.
--   - `SampleCircuit`: PDF pp.19–21: a circuit using supplied indexed density copies and fixed ancillary bits. Ports are disjoint by one injection; gates do not receive the unknown U or samples. The output is the main system and all other wires are traced out.
--   - `SampleCircuit.initial`: PDF pp.19–21: product input with actual independent supplied sample copies.
--   - `SampleCircuit.output`: PDF pp.19–21: source circuit channel; gate cost is literally gates.length.
--   - `inputOutputRecords`: PDF p.19: actual supplied input/output records, with no coherent phase reference.
--   - `EmulatorFamily`: PDF pp.19–21: one uniform family of sample circuits, fixed before the unknown sample vectors, U, and the new input. T and m are precision controls; history is classical.
--   - `precisionRounds`: PDF p.19: fixed ideal-error allocation eps/2 and at most eps/2 for all DME calls. For rank one no erasure rounds are needed. This corrects the printed allocation after B21, whose substitution into B19 gives more than eps. Constants only are rescaled.
--   - `slowFactor`: PDF pp.7,19: explicit polylogarithmic multiplier used to spell out O-tilde.
--   - `BinaryEmulatorFamily`: PDF p.22: binary circuits also accept the number of address qubits q.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, https://arxiv.org/abs/1606.02734v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Learning

/-! Universal Quantum Emulator, arXiv:1606.02734v2. Page numbers are PDF pages.
All new constructions are paper-local. Tensor factors put the system first.
Generated algebras use nonempty words: the ambient identity is not silently adjoined. -/

noncomputable section
open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.2: unitary conjugation, also for subnormalized branches. -/
def densityConjugation (V : Matrix I I ℂ) (rho : Matrix I I ℂ) : Matrix I I ℂ := V * rho * Vᴴ

/-- PDF p.2: complex span of all nonempty sample words (supported nonunital algebra). -/
def sampleAlgebra (S : K → Matrix I I ℂ) : Submodule ℂ (Matrix I I ℂ) :=
  Submodule.span ℂ {X | ∃ w : List K, w ≠ [] ∧ X = (w.map S).prod}

/-- PDF p.2: the support projector of the sum of PSD sample densities is the projector
onto the span of their supports. CFC is evaluated on a finite spectrum. -/
def samplePi (S : K → Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else 1) (∑ k, S k)

/-- PDF p.2, Eq.(6): equality with the full supported matrix algebra. -/
def Generates (S : K → Matrix I I ℂ) : Prop :=
  ∀ X : Matrix I I ℂ, X ∈ sampleAlgebra S ↔ samplePi S * X * samplePi S = X

/-- PDF p.2: density support contained in the input span. -/
def InSampleSupport (S : K → Matrix I I ℂ) (rho : Matrix I I ℂ) : Prop :=
  samplePi S * rho * samplePi S = rho

/-- PDF p.2, Eq.(2): dimension of the sample support. -/
def sampleDimension (S : K → Matrix I I ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (samplePi S)))

/-- PDF p.2: pure sample density records. -/
def pureSamples (phi : K → EuclideanSpace ℂ I) : K → Matrix I I ℂ := fun k => pureDensity (phi k)

/-- PDF p.3, Eq.(9): the sample reflection sign is I-2P. -/
def sampleReflection (phi : EuclideanSpace ℂ I) : Matrix I I ℂ := 1 - 2 • pureDensity phi

/-- PDF p.3, Eq.(10): frozen control-first gate reindexed into system-first order. -/
def systemControlled (V : Matrix I I ℂ) : Matrix (I × Bool) (I × Bool) ℂ :=
  (QAlgorithms.controlled V).submatrix Prod.swap Prod.swap

/-- PDF p.3, Eq.(11), R(k) H R(anchor), with the rightmost gate first. -/
def erasureGate (phi : K → EuclideanSpace ℂ I) (a k : K) : Matrix (I × Bool) (I × Bool) ℂ :=
  systemControlled (sampleReflection (phi k)) * Matrix.kronecker (1 : Matrix I I ℂ) hadamard *
    systemControlled (sampleReflection (phi a))

/-- PDF p.4: |minus> tensor T, including the empty tensor. -/
def minusRegister (T : ℕ) : EuclideanSpace ℂ (Qubits T) :=
  WithLp.toLp 2 fun z => ∏ j : Fin T,
    if z j then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)

/-- PDF p.3: the normalized one-qubit |minus>. -/
def minusVector : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun b => if b then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)

/-- PDF p.4: a system/one-qubit operator placed on ancilla j. -/
def onAncilla {T : ℕ} (V : Matrix (I × Bool) (I × Bool) ℂ) (j : Fin T) : Matrix (I × Qubits T) (I × Qubits T) ℂ :=
  fun x y => if ∀ l, l ≠ j → x.2 l = y.2 l then V (x.1,x.2 j) (y.1,y.2 j) else 0

/-- PDF p.13: ordered forward history, recalled unchanged in the reverse circuit. -/
def historyUnitary {T : ℕ} (W : L → Matrix (I × Bool) (I × Bool) ℂ) (h : Fin T → L) : Matrix (I × Qubits T) (I × Qubits T) ℂ :=
  (List.ofFn fun j : Fin T => onAncilla (W (h j)) j).foldl (fun V G => G * V) 1

/-- PDF p.14: iid history weight. -/
def historyWeight {T : ℕ} (p : L → ℝ) (h : Fin T → L) : ℝ := ∏ j, p (h j)

/-- PDF p.14, A5: the generalized averaged erasure channel. -/
def coherentErasureChannel (p : L → ℝ) (W : L → Matrix (I × Bool) (I × Bool) ℂ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ l, (p l : ℂ) • traceRight (densityConjugation (W l) (Matrix.kronecker rho (pureDensity minusVector)))

/-- PDF pp.4–5: fixed anchor excluded from the uniform random indices. -/
def nonanchorProbability (a k : K) : ℝ :=
  if k = a then 0 else ((Fintype.card K - 1 : ℕ) : ℝ)⁻¹

/-- PDF pp.13–16: a Fig.5 branch, including measurement, replacement of the system
by the output anchor, then reverse output history. False means b=0. -/
def jointBranchHistory {T : ℕ} (Win : L → Matrix (I × Bool) (I × Bool) ℂ)
    (Wout : L → Matrix (J × Bool) (J × Bool) ℂ) (phi : EuclideanSpace ℂ I) (phiout : EuclideanSpace ℂ J)
    (h : Fin T → L) (b : Bool) (rho : Matrix I I ℂ) : Matrix (J × Qubits T) (J × Qubits T) ℂ :=
  let X := densityConjugation (historyUnitary Win h) (Matrix.kronecker rho (pureDensity (minusRegister T)))
  let P := if b then 1 - pureDensity phi else pureDensity phi
  let measured := densityConjugation (Matrix.kronecker P (1 : Matrix (Qubits T) (Qubits T) ℂ)) X
  densityConjugation (historyUnitary Wout h)ᴴ
    (Matrix.kronecker (pureDensity phiout) (traceLeft measured))

/-- PDF p.14: averaged subnormalized joint branch. -/
def jointBranch (p : L → ℝ) (Win : L → Matrix (I × Bool) (I × Bool) ℂ)
    (Wout : L → Matrix (J × Bool) (J × Bool) ℂ) (phi : EuclideanSpace ℂ I) (phiout : EuclideanSpace ℂ J)
    (T : ℕ) (b : Bool) (rho : Matrix I I ℂ) : Matrix (J × Qubits T) (J × Qubits T) ℂ :=
  ∑ h : Fin T → L, (historyWeight p h : ℂ) • jointBranchHistory Win Wout phi phiout h b rho

/-- PDF p.14, A10: nonselective joint output in the Appendix A convention. -/
def jointEmulator (p : L → ℝ) (Win : L → Matrix (I × Bool) (I × Bool) ℂ)
    (Wout : L → Matrix (J × Bool) (J × Bool) ℂ) (phi : EuclideanSpace ℂ I) (phiout : EuclideanSpace ℂ J)
    (T : ℕ) (rho : Matrix I I ℂ) : Matrix (J × Qubits T) (J × Qubits T) ℂ :=
  jointBranch p Win Wout phi phiout T false rho + jointBranch p Win Wout phi phiout T true rho

/-- PDF pp.6,15, Eq.(18)/A12: covariance has U-dagger on the right, correcting
printed A1's U. This does not impose U squared equal to the identity. -/
def transportedGate (U : Matrix I I ℂ) (W : L → Matrix (I × Bool) (I × Bool) ℂ) : L → Matrix (I × Bool) (I × Bool) ℂ :=
  fun l => densityConjugation (Matrix.kronecker U (1 : Matrix Bool Bool ℂ)) (W l)

/-- PDF p.6, Eq.(20): actual erasure success probability. -/
def eraseProbability (p : L → ℝ) (W : L → Matrix (I × Bool) (I × Bool) ℂ)
    (phi : EuclideanSpace ℂ I) (T : ℕ) (rho : Matrix I I ℂ) : ℝ :=
  effectProb (pureDensity phi) ((coherentErasureChannel p W)^[T] rho)

/-- PDF p.6: pure-sample main-system emulator, Appendix A output convention. -/
def emulate (phi : K → EuclideanSpace ℂ I) (a : K) (U : Matrix I I ℂ) (T : ℕ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  traceRight (jointEmulator (nonanchorProbability a) (erasureGate phi a)
    (transportedGate U (erasureGate phi a)) (phi a) (act U (phi a)) T rho)

/-- PDF p.7, Eq.(25): compression to H_in intersect anchor-perp. -/
def compressedReflection (phi : K → EuclideanSpace ℂ I) (a k : K) : Matrix I I ℂ :=
  let Q := samplePi (pureSamples phi) - pureDensity (phi a)
  Q * sampleReflection (phi k) * Q

/-- PDF p.7, Eq.(24): compressed sampleReflection channel. -/
def compressedReflectionChannel (phi : K → EuclideanSpace ℂ I) (a : K) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ k, (nonanchorProbability a k : ℂ) •
    (compressedReflection phi a k * rho * compressedReflection phi a k)

/-- PDF p.7, Eq.(26): norm of the vectorized compressed channel. -/
def lambdaPerp (phi : K → EuclideanSpace ℂ I) (a : K) : ℝ :=
  QAlgorithms.specNorm (∑ k, (nonanchorProbability a k : ℂ) • Matrix.kronecker
    (compressedReflection phi a k) (fun i j => conj (compressedReflection phi a k i j)))

/-- PDF p.8, Eq.(35): exact, unnormalized residual. -/
def residual (phi : K → EuclideanSpace ℂ I) (a : K) (psi : EuclideanSpace ℂ I) (h : List K) : EuclideanSpace ℂ I :=
  h.foldl (fun v k => act (sampleReflection (phi k) * (1 - pureDensity (phi a))) v) psi

/-- PDF p.8: unary address, including residual t=T. -/
def unaryWord (T t : ℕ) : Qubits T := fun j => decide ((j : ℕ) < t)

/-- PDF p.8, Eq.(34): the full expansion retains its residual term. -/
def coordinateExpansion {T : ℕ} (phi : K → EuclideanSpace ℂ I) (a : K)
    (h : Fin T → K) (psi : EuclideanSpace ℂ I) : EuclideanSpace ℂ (I × Qubits T) :=
  (∑ t : Fin T, (inner ℂ (phi a) (residual phi a psi ((List.ofFn h).take t.val))) •
    tensorVec (phi a) (ket (unaryWord T t.val))) +
    tensorVec (residual phi a psi (List.ofFn h)) (ket (unaryWord T T))

/-- PDF p.32, H3: average sample density. -/
def meanSampleDensity (phi : K → EuclideanSpace ℂ I) : Matrix I I ℂ := (Fintype.card K : ℂ)⁻¹ • ∑ k, pureDensity (phi k)

/-- PDF pp.31–32: actual Fig.7 branch. Same history is used forward and backward;
false is span detection, true is the all-minus outcome. -/
def projectionBranch (phi : K → EuclideanSpace ℂ I) (T : ℕ) (b : Bool) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  ((Fintype.card K : ℂ) ^ T)⁻¹ • ∑ h : Fin T → K,
    let V := historyUnitary (fun k => systemControlled (sampleReflection (phi k))) h
    let P := Matrix.kronecker (1 : Matrix I I ℂ) (pureDensity (minusRegister T))
    let Q := if b then P else 1 - P
    traceRight (densityConjugation Vᴴ (densityConjugation Q
      (densityConjugation V (Matrix.kronecker rho (pureDensity (minusRegister T))))))

/-- PDF p.32: channel discarding the Fig.7 label. -/
def projectionChannel (phi : K → EuclideanSpace ℂ I) (T : ℕ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  projectionBranch phi T false rho + projectionBranch phi T true rho

/-- PDF p.33, H19: randomized conjugated projective measurement. -/
def gentleChannel (p : L → ℝ) (V : L → Matrix I I ℂ) (P : A → Matrix I I ℂ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ l, (p l : ℂ) • ∑ a, densityConjugation ((V l)ᴴ * P a * V l) rho

/-- PDF p.34, H21: actual expected outcome probability. -/
def gentleProbability (p : L → ℝ) (V : L → Matrix I I ℂ) (P : A → Matrix I I ℂ)
    (rho : Matrix I I ℂ) (a : A) : ℝ := ∑ l, p l * effectProb (P a) (densityConjugation (V l) rho)

/-- PDF p.33: complete orthogonal projectors; zero projectors are allowed. -/
def ProjectiveFamily (P : A → Matrix I I ℂ) : Prop :=
  (∀ a, (P a).IsHermitian ∧ P a * P a = P a) ∧
    (∀ a b, a ≠ b → P a * P b = 0) ∧ ∑ a, P a = 1

/-- PDF p.20: positive-sign matrix exponential, e^(i theta H). -/
def positivePhaseEvolution (H : Matrix I I ℂ) (theta : ℝ) : Matrix I I ℂ := NormedSpace.exp ((Complex.I * theta) • H)

/-- PDF pp.7–8, Eq.(31): quantum Fisher information of a differentiable normalized
pure-state family. The theorem uses the actual analytic exp(i alpha P) family, so no
nondifferentiability default of deriv is involved. -/
def pureFisherInformation (v : ℝ → EuclideanSpace ℂ I) (alpha : ℝ) : ℝ :=
  4 * (‖deriv v alpha‖ ^ 2 - ‖inner ℂ (v alpha) (deriv v alpha)‖ ^ 2)

/-- PDF p.24: n independently prepared pure reference registers. -/
def referenceVector (phi : EuclideanSpace ℂ I) (n : ℕ) : EuclideanSpace ℂ (Fin n → I) :=
  WithLp.toLp 2 fun x => ∏ j, phi (x j)

/-- PDF p.24, E1: SWAP of system with reference j, identity on other references. -/
def swapReference {n : ℕ} (j : Fin n) : Matrix (I × (Fin n → I)) (I × (Fin n → I)) ℂ :=
  fun x y => if x.1 = y.2 j ∧ x.2 = Function.update y.2 j y.1 then 1 else 0

/-- PDF p.24, E1: full continuous interaction. -/
def swapHamiltonian (n : ℕ) (coupling : ℝ) : Matrix (I × (Fin n → I)) (I × (Fin n → I)) ℂ :=
  (coupling : ℂ) • ∑ j : Fin n, swapReference j

/-- PDF p.24, E2: actual joint positivePhaseEvolution. -/
def swapJoint (phi : EuclideanSpace ℂ I) (n : ℕ) (coupling t : ℝ) (rho : Matrix I I ℂ) : Matrix (I × (Fin n → I)) (I × (Fin n → I)) ℂ :=
  densityConjugation (positivePhaseEvolution (swapHamiltonian n coupling) (-t))
    (Matrix.kronecker rho (pureDensity (referenceVector phi n)))

/-- PDF p.24, E3: effective Hamiltonian with the n+1 coefficient. -/
def effectiveHamiltonian (phi : EuclideanSpace ℂ I) (n : ℕ) (coupling : ℝ) : Matrix I I ℂ :=
  ((coupling * (n + 1) : ℝ) : ℂ) • pureDensity phi

/-! Construction sanity checks. -/

example (v : EuclideanSpace ℂ I) (alpha : ℝ) : pureFisherInformation (fun _ : ℝ => v) alpha = 0 := by
  simp [pureFisherInformation]

example (phi : K → EuclideanSpace ℂ I) (a : K) (psi : EuclideanSpace ℂ I) : residual phi a psi [] = psi := rfl

example (W : L → Matrix (I × Bool) (I × Bool) ℂ) (h : Fin 0 → L) : historyUnitary W h = 1 := by
  simp [historyUnitary]

example (x : Qubits 0) : minusRegister 0 x = 1 := by simp [minusRegister]

example (T : ℕ) (j : Fin T) : unaryWord T 0 j = false := by simp [unaryWord]

example (T : ℕ) (j : Fin T) : unaryWord T T j = true := by simp [unaryWord, j.isLt]

example (V : Matrix I I ℂ) (i j : I) : systemControlled V (i,false) (j,true) = 0 := rfl

example (phi : K → EuclideanSpace ℂ I) (a : K) : nonanchorProbability a a = 0 := by simp [nonanchorProbability]

example (phi : EuclideanSpace ℂ I) (n : ℕ) (t : ℝ) (rho : Matrix I I ℂ) :
    swapJoint phi n 0 t rho = Matrix.kronecker rho (pureDensity (referenceVector phi n)) := by
  simp [swapJoint, swapHamiltonian, positivePhaseEvolution, densityConjugation]

/-- PDF p.4, Fig.2: unsuccessful output is the old system wire from the SWAP.
The successful wire is reconstructed. These differ from Appendix A on failure. -/
def wireBranch (phi : K → EuclideanSpace ℂ I) (a : K) (U : Matrix I I ℂ) (T : ℕ) (b : Bool) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  if b then
    ∑ h : Fin T → K, (historyWeight (nonanchorProbability a) h : ℂ) •
      traceRight (densityConjugation (Matrix.kronecker (1 - pureDensity (phi a)) (1 : Matrix (Qubits T) (Qubits T) ℂ))
        (densityConjugation (historyUnitary (erasureGate phi a) h)
          (Matrix.kronecker rho (pureDensity (minusRegister T)))))
  else traceRight (jointBranch (nonanchorProbability a) (erasureGate phi a)
    (transportedGate U (erasureGate phi a)) (phi a) (act U (phi a)) T false rho)

/-- PDF p.28, G1: systemControlled density-matrix translations. -/
def mixedGate (S : K → Matrix I I ℂ) (a k : K) (t : ℝ) : Matrix (I × Bool) (I × Bool) ℂ :=
  systemControlled (positivePhaseEvolution (S k) (-t)) * Matrix.kronecker (1 : Matrix I I ℂ) hadamard *
    systemControlled (positivePhaseEvolution (S a) (-Real.pi))

/-- PDF p.28: entrywise Lebesgue integration of the continuous one-round body.
For density samples the matrix exponential body is continuous on the compact interval. -/
def mixedSampleErasureChannel (S : K → Matrix I I ℂ) (a : K) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  (Fintype.card K : ℂ)⁻¹ • ∑ k,
    fun i j => ∫ t in Set.Icc (0 : ℝ) 1,
      traceRight (densityConjugation (mixedGate S a k t) (Matrix.kronecker rho (pureDensity minusVector))) i j

/-- PDF p.28: history unitary for fixed mixed-sample indices and real times. -/
def mixedHistory {T : ℕ} (S : K → Matrix I I ℂ) (a : K) (h : Fin T → K) (ts : Fin T → ℝ) :
    Matrix (I × Qubits T) (I × Qubits T) ℂ :=
  (List.ofFn fun j : Fin T => onAncilla (mixedGate S a (h j) (ts j)) j).foldl (fun V G => G * V) 1

/-- PDF p.28: fixed mixed-history output after system replacement and reconstruction. -/
def mixedHistoryOutput {T : ℕ} (S : K → Matrix I I ℂ) (a : K) (phi : EuclideanSpace ℂ I)
    (U : Matrix I I ℂ) (rho : Matrix I I ℂ) (h : Fin T → K) (ts : Fin T → ℝ) : Matrix I I ℂ :=
  let Vin := mixedHistory S a h ts
  let Vout := Matrix.kronecker U (1 : Matrix (Qubits T) (Qubits T) ℂ) * Vin *
    Matrix.kronecker Uᴴ (1 : Matrix (Qubits T) (Qubits T) ℂ)
  traceRight (densityConjugation Voutᴴ (Matrix.kronecker (pureDensity (act U phi))
    (traceLeft (densityConjugation Vin (Matrix.kronecker rho (pureDensity (minusRegister T)))))))

/-- PDF p.28: actual mixed-sample emulator, with independent uniform times and indices.
Entrywise integrals are over a compact cube of a continuous finite-matrix body. -/
def mixedEmulate (S : K → Matrix I I ℂ) (a : K) (phi : EuclideanSpace ℂ I) (U : Matrix I I ℂ)
    (T : ℕ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  ((Fintype.card K : ℂ) ^ T)⁻¹ • ∑ h : Fin T → K,
    fun i j => ∫ ts in Set.pi Set.univ (fun _ : Fin T => Set.Icc (0 : ℝ) 1),
      mixedHistoryOutput S a phi U rho h ts i j

/-- PDF p.28, G2: tagged sample densities plus a pure bridge (none). -/
def bridgeSamples (S : K → Matrix I I ℂ) (phi : EuclideanSpace ℂ I) (alpha beta : ℂ) : Option (Bool × K) → Matrix (I × Bool) (I × Bool) ℂ
  | none => pureDensity (tensorVec phi (WithLp.toLp 2 fun b => if b then beta else alpha))
  | some (b,k) => Matrix.kronecker (S k) (pureDensity (ket b))

/-- PDF p.29, G3: positive-sign Fourier-densityConjugation basis. -/
def conjugateBasis {d : ℕ} (theta : Fin d → EuclideanSpace ℂ I) (j : Fin d) : EuclideanSpace ℂ I :=
  ∑ k, ((((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
    Complex.exp (Complex.I * (2 * Real.pi * k.val * j.val / d : ℝ))) • theta k

/-- PDF pp.29–30: normalized uniform address state. -/
def uniformAddress (d : ℕ) : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 fun _ => ((Real.sqrt d)⁻¹ : ℂ)

/-- PDF p.30, G7: negative-sign normalized DFT. This corrects G7's missing
normalization and ket index; G6 and G11 determine this sign. -/
def negativeFourier (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun j k => ((Real.sqrt d)⁻¹ : ℂ) *
    Complex.exp (-Complex.I * (2 * Real.pi * j.val * k.val / d : ℝ))

/-- PDF pp.29–30, G4/G8: full spectral exponential, hence identity on H_in-perp. -/
def basisPhase {d : ℕ} (theta : Fin d → EuclideanSpace ℂ I) : Matrix (I × Fin d) (I × Fin d) ℂ :=
  fun x y => if x.2 = y.2 then
    positivePhaseEvolution (∑ k : Fin d, (k.val : ℂ) • pureDensity (theta k))
      (2 * Real.pi * x.2.val / d) x.1 y.1 else 0

/-- PDF p.22, D5: cyclic increment on the binary address. -/
def increment (q : ℕ) : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ :=
  fun x y => if x.val = (y.val + 1) % (2 ^ q) then 1 else 0

/-- PDF p.22, D6: Fig.6 effective operation on system/address, with the helper
returned to |minus>. The address is initialized at zero, correcting D8's printed |t>. -/
def binaryMeasure (phi : EuclideanSpace ℂ I) (q : ℕ) : Matrix (I × Fin (2 ^ q)) (I × Fin (2 ^ q)) ℂ :=
  Matrix.kronecker (pureDensity phi) 1 + Matrix.kronecker (1 - pureDensity phi) (increment q)

/-- PDF p.23, D7: address-selective sampleReflection; t is a natural address. -/
def addressedReflection (phi : EuclideanSpace ℂ I) (q t : ℕ) : Matrix (I × Fin (2 ^ q)) (I × Fin (2 ^ q)) ℂ :=
  fun x y => if x.2 = y.2 then
    (if x.2.val = t then sampleReflection phi else 1) x.1 y.1 else 0

/-- PDF pp.22–23: actual binary history F(t+1,k) V, using addresses 1 through T. -/
def binaryHistory {T : ℕ} (phi : K → EuclideanSpace ℂ I) (a : K) (q : ℕ) (h : Fin T → K) :
    Matrix (I × Fin (2 ^ q)) (I × Fin (2 ^ q)) ℂ :=
  (List.ofFn fun j : Fin T => addressedReflection (phi (h j)) q (j.val+1) * binaryMeasure (phi a) q).foldl (fun V G => G * V) 1

/-- PDF pp.22–23: linear reencoding of the unary subspace, extended by zero elsewhere. -/
def encodeUnary (q T : ℕ) (v : EuclideanSpace ℂ (I × Qubits T)) : EuclideanSpace ℂ (I × Fin (2 ^ q)) :=
  WithLp.toLp 2 fun x => ∑ t : Fin (T+1),
    if x.2.val = t.val then v (x.1, unaryWord T t.val) else 0

/-- PDF p.11: SWAP between two equal-dimensional registers. -/
def registerSwap : Matrix (I × I) (I × I) ℂ := fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

/-- PDF p.11: double-systemControlled full-register SWAP, with both controls ancillary. -/
def doubleControlledSwap : Matrix ((I × I) × (Bool × Bool)) ((I × I) × (Bool × Bool)) ℂ :=
  fun x y => if x.2 = y.2 then
    (if x.2.1 && x.2.2 then registerSwap else 1) x.1 y.1 else 0

/-- PDF pp.19–21: source elementary gate set, one-qubit unitaries and two-control
SWAPs acting on four distinct qubit wires. -/
inductive ElementaryGate (N : ℕ) where
  | one (wire : Fin N) (U : Matrix.unitaryGroup Bool ℂ)
  | ccswap (wires : Fin 4 ↪ Fin N)

/-- PDF pp.19–21: complete matrix semantics of the counted elementary gates. -/
def elementaryMatrix {N : ℕ} : ElementaryGate N → Matrix (Qubits N) (Qubits N) ℂ
  | .one q U => fun x y =>
      if ∀ l, l ≠ q → x l = y l then (U : Matrix Bool Bool ℂ) (x q) (y q) else 0
  | .ccswap w => fun x y =>
      if x = (if y (w 0) && y (w 1) then
        Function.update (Function.update y (w 2) (y (w 3))) (w 3) (y (w 2)) else y)
      then 1 else 0

/-- PDF pp.19–21: a circuit using supplied indexed density copies and fixed ancillary
bits. Ports are disjoint by one injection; gates do not receive the unknown U or samples.
The output is the main system and all other wires are traced out. -/
structure SampleCircuit (n : ℕ) (K : Type*) where
  N : ℕ
  copies : ℕ
  ports : (Fin n ⊕ (Fin copies × Fin n)) ↪ Fin N
  labels : Fin copies → Bool × K
  auxiliaryBits : Qubits N
  gates : List (ElementaryGate N)

/-- PDF pp.19–21: product input with actual independent supplied sample copies. -/
def SampleCircuit.initial {n : ℕ} (C : SampleCircuit n K)
    (records : Bool × K → Matrix (Qubits n) (Qubits n) ℂ) (rho : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Qubits C.N) (Qubits C.N) ℂ :=
  fun x y => rho (fun j => x (C.ports (.inl j))) (fun j => y (C.ports (.inl j))) *
    (∏ r, records (C.labels r)
      (fun j => x (C.ports (.inr (r,j)))) (fun j => y (C.ports (.inr (r,j))))) *
    (if ∀ q, q ∉ Set.range C.ports → x q = C.auxiliaryBits q ∧ y q = C.auxiliaryBits q then 1 else 0)

/-- PDF pp.19–21: source circuit channel; gate cost is literally gates.length. -/
def SampleCircuit.output {n : ℕ} (C : SampleCircuit n K)
    (records : Bool × K → Matrix (Qubits n) (Qubits n) ℂ) (rho : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  let V := (C.gates.map elementaryMatrix).foldl (fun V G => G * V) 1
  let X := densityConjugation V (C.initial records rho)
  fun i j => ∑ x : Qubits C.N, ∑ y : Qubits C.N,
    if (∀ l, x (C.ports (.inl l)) = i l ∧ y (C.ports (.inl l)) = j l) ∧
      (∀ q, q ∉ Set.range (fun l => C.ports (.inl l)) → x q = y q) then X x y else 0

/-- PDF p.19: actual supplied input/output records, with no coherent phase reference. -/
def inputOutputRecords (phi : K → EuclideanSpace ℂ I) (U : Matrix I I ℂ) : Bool × K → Matrix I I ℂ :=
  fun bk => if bk.1 then densityConjugation U (pureDensity (phi bk.2)) else pureDensity (phi bk.2)

/-- PDF pp.19–21: one uniform family of sample circuits, fixed before the unknown
sample vectors, U, and the new input. T and m are precision controls; history is classical. -/
abbrev EmulatorFamily := ∀ n k : ℕ, Fin k → (T m : ℕ) → (Fin T → Fin k) → SampleCircuit n (Fin k)

example (phi : EuclideanSpace ℂ I) (x : Fin 0 → I) : referenceVector phi 0 x = 1 := by
  simp [referenceVector]

/-- PDF p.19: fixed ideal-error allocation eps/2 and at most eps/2 for all DME calls.
For rank one no erasure rounds are needed. This corrects the printed allocation after B21,
whose substitution into B19 gives more than eps. Constants only are rescaled. -/
def precisionRounds (d : ℕ) (lam eps : ℝ) : ℕ :=
  if d ≤ 1 then 0 else max 1 ⌈Real.log (8 * eps⁻¹ ^ 2 * (d - 1 : ℝ)) / (1-lam)⌉₊

/-- PDF pp.7,19: explicit polylogarithmic multiplier used to spell out O-tilde. -/
def slowFactor (d : ℕ) (eps : ℝ) (power : ℕ) : ℝ :=
  (1 + Real.log (d+1) + Real.log (1+eps⁻¹)) ^ power

/-- PDF p.22: binary circuits also accept the number of address qubits q. -/
abbrev BinaryEmulatorFamily := ∀ n k : ℕ, Fin k → (q T m : ℕ) →
  (Fin T → Fin k) → SampleCircuit n (Fin k)

end QAlgorithms.Papers.Independent.Intakethird100.P67


