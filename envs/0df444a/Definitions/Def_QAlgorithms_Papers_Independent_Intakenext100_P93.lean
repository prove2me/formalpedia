-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P93
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P93
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:32:24.502398+00:00
-- url     : https://prove2.me/theorems/c665e1a0-7977-4514-af28-b9b0acb43f8e
-- title:
--   Definitions for Degenerate Quantum Codes for Pauli Channels
-- statement:
--   The objects the formalized statements of *Degenerate Quantum Codes for Pauli Channels* (arXiv:quant-ph/0604107) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pauliMass`: PDF p.2: the physical one-qubit Pauli law, with Y carrying both bits.
--   - `pauliErrorWordMass`: PDF p.2: reuse the accepted product law on paired physical amplitude/phase labels, so all three Pauli parameters are retained.
--   - `catLogicalSyndromeMass`: PDF p.2, Eq.(6) left side: actual pushforward of physical errors to one logical Pauli and one specific syndrome. No weight multiplicity is inserted.
--   - `iidCatSyndromeMass`: PDF p.2: marginal probability of one syndrome string.
--   - `amplitudeCount`: PDF p.2, Eq.(6): number of physical amplitude errors for fixed logical amplitude and syndrome. The subtraction is only k+1-|s|, always positive.
--   - `noAmplitudeCount`: PDF p.2, Eq.(6): number of positions without amplitude errors.
--   - `orderedPauli`: PDF p.2: matrix of the accepted ordered physical Pauli, on every vector.
--   - `iidPauliNoise`: PDF p.2: the tensor power of the three-parameter Pauli channel.
--   - `decoderBranch`: PDF p.2: accepted cat decoder followed by the indicated syndrome branch; this is a rectangular Kraus matrix, with the logical qubit remaining.
--   - `branchChannel`: PDF p.2: actual encode/noise/measure/decode branch before normalization.
--   - `catBellInput`: PDF p.2: reindex the frozen one-pair Bell vector by Bool, reference first.
--   - `branchBell`: PDF p.2: Bell output of the ACTUAL branch instrument, not a mixture postulated from Eq.(6).
--   - `conditionalChannel`: PDF p.2: the conditional channel; an impossible branch is assigned the identity, whose weighted contribution is zero.
--   - `catInstrumentOutput`: PDF p.2: actual output with the entire classical syndrome in the receiver.
--   - `catRate`: PDF p.2, Eq.(5): signed Bell-input cat rate, without optimizing the input.
--   - `catBlockEncoder`: PDF p.2: tensor product of this fixed inner cat encoder on n blocks.
--   - `CatAchievable`: PDF p.2, Eq.(5): operational fixed-cat/additive-outer achievability. The encoder is fixed before the unknown input. All sufficiently large positive outer blocklengths work, with rate measured per (k+1)n physical qubits. The only resources are the specified encoder, independent noise and a CPTP decoder.
--   - `syndromeWeightMass`: PDF pp.2--3: distribution of the syndrome Hamming weight, summing strings only here.
--   - `concentrationTail`: PDF pp.2--3: mass away from BOTH limiting syndrome-weight centers. The k=0 branch is defined separately, avoiding a meaningless empty-word ratio.
--   - `xCatEncoder`: PDF p.3: X-basis cat, including the logical Hadamard H^tensor(b+1) Enc H.
--   - `concatenatedEncoder`: PDF p.3: encode the outer X cat, then an inner Z cat on EACH output. The physical register consists of b+1 blocks of a+1 qubits.
--   - `concatenatedBlockEncoder`: PDF pp.2--3: tensor copies of the fixed two-level inner encoder. Every physical wire is indexed by (copy, outer-cat wire, inner-cat wire).
--   - `ConcatenatedAchievable`: PDF pp.2--3, Eq.(5) and Concatenated Repetition Codes: communication through the fixed two-level inner cat and an additive random-code outer layer. Rates count (a+1)(b+1)n physical uses; one code handles every unknown input.
--   - `concatenatedRawOutput`: PDF p.3: actual encoded Bell output before the two-level syndrome instrument.
--   - `concatenatedDecoderBranch`: PDF p.3: inner Z-check branches followed by the outer X-check branch. The logical Hadamard is included in the inverse of the X-basis encoder.
--   - `concatenatedOutput`: PDF p.3: actual two-level instrument output. Both the outer X-check syndrome and ALL inner Z-check syndromes are retained at the receiver.
--   - `concatenatedRate`: PDF p.3: signed concatenated-cat rate per (a+1)(b+1) channel uses.
--   - `noiseThreshold`: PDF p.3, Fig.2: zero-rate noise threshold, restricted to physical noise p in [0,3/4]. The explicit zero ensures a nonempty bounded supremum domain.
--   - `twoPauliChannel`: PDF pp.3--4: N_p^tp with equal X/Z errors and no Y error.
--   - `twoPauliDilation`: PDF pp.3--4: concrete Stinespring matrix, with environment order X,Z,I. Its two partial traces define the receiver and complement of the SAME dilation.
-- source:
--   Degenerate Quantum Codes for Pauli Channels, arXiv:quant-ph/0604107v2, https://arxiv.org/abs/quant-ph/0604107v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P15
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

/-!
Smith--Smolin, arXiv:quant-ph/0604107v2, PDF pp.2--4.
All new interfaces belong to this paper. A cat has length k+1; k=0 is the
identity cat. Physical and logical Paulis have the ordered convention X^u Z^v.
Syndromes are retained without majority correction. Rates and entropies use bits.
Numerical and underspecified claims are inventoried separately in HARD.md.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

open QAlgorithms
open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: the physical one-qubit Pauli law, with Y carrying both bits. -/
def pauliMass (px py pz : ℝ) (u v : Bool) : ℝ :=
  if u then (if v then py else px) else (if v then pz else 1 - px - py - pz)

/-- PDF p.2: reuse the accepted product law on paired physical amplitude/phase
labels, so all three Pauli parameters are retained. -/
def pauliErrorWordMass {m : ℕ} (px py pz : ℝ) (u v : Qubits m) : ℝ :=
  QAlgorithms.Papers.Independent.Support50.P38.wordMass
    (fun e : Bool × Bool => pauliMass px py pz e.1 e.2) (fun i => (u i, v i))

/-- PDF p.2, Eq.(6) left side: actual pushforward of physical errors to one
logical Pauli and one specific syndrome. No weight multiplicity is inserted. -/
def catLogicalSyndromeMass (k : ℕ) (px py pz : ℝ) (u v : Bool) (s : Qubits k) : ℝ :=
  ∑ x : Qubits (k + 1), ∑ z : Qubits (k + 1),
    if x 0 = u ∧ dotBits z (fun _ => true) = v ∧ QAlgorithms.Papers.Independent.Advance50.P15.repetitionSyndrome x = s
    then pauliErrorWordMass px py pz x z else 0

/-- PDF p.2: marginal probability of one syndrome string. -/
def iidCatSyndromeMass (k : ℕ) (px py pz : ℝ) (s : Qubits k) : ℝ :=
  ∑ u : Bool, ∑ v : Bool, catLogicalSyndromeMass k px py pz u v s

/-- PDF p.2, Eq.(6): number of physical amplitude errors for fixed logical
amplitude and syndrome. The subtraction is only k+1-|s|, always positive. -/
def amplitudeCount (k : ℕ) (u : Bool) (s : Qubits k) : ℕ :=
  if u then k + 1 - hammingWeight s else hammingWeight s

/-- PDF p.2, Eq.(6): number of positions without amplitude errors. -/
def noAmplitudeCount (k : ℕ) (u : Bool) (s : Qubits k) : ℕ :=
  if u then hammingWeight s else k + 1 - hammingWeight s

/-- PDF p.2: matrix of the accepted ordered physical Pauli, on every vector. -/
def orderedPauli {m : ℕ} (u v : Qubits m) : Matrix (Qubits m) (Qubits m) ℂ :=
  fun x y => QAlgorithms.Papers.Independent.Advance50.P15.physicalPauli u v (ket y) x

/-- PDF p.2: the tensor power of the three-parameter Pauli channel. -/
def iidPauliNoise (m : ℕ) (px py pz : ℝ) : Superop (Qubits m) (Qubits m) :=
  fun rho => ∑ u : Qubits m, ∑ v : Qubits m,
    (pauliErrorWordMass px py pz u v : ℂ) • conjSuperop (orderedPauli u v) rho

/-- PDF p.2: accepted cat decoder followed by the indicated syndrome branch;
this is a rectangular Kraus matrix, with the logical qubit remaining. -/
def decoderBranch (k : ℕ) (s : Qubits k) : Matrix Bool (Qubits (k + 1)) ℂ :=
  fun b x => if QAlgorithms.Papers.Independent.Advance50.P15.repetitionCoordinates k x = (b, s) then 1 else 0

/-- PDF p.2: actual encode/noise/measure/decode branch before normalization. -/
def branchChannel (k : ℕ) (px py pz : ℝ) (s : Qubits k) : Superop Bool Bool :=
  conjSuperop (decoderBranch k s) ∘ iidPauliNoise (k + 1) px py pz ∘
    conjSuperop (QAlgorithms.Papers.Independent.Support50.P40.catEncoder k)

/-- PDF p.2: reindex the frozen one-pair Bell vector by Bool, reference first. -/
def catBellInput : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun x => maxEntangled 1 ((fun _ => x.1), (fun _ => x.2))

/-- PDF p.2: Bell output of the ACTUAL branch instrument, not a mixture
postulated from Eq.(6). -/
def branchBell (k : ℕ) (px py pz : ℝ) (s : Qubits k) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  idTensorSuperop (R := Bool) (branchChannel k px py pz s) (pureDensity catBellInput)

/-- PDF p.2: the conditional channel; an impossible branch is assigned the
identity, whose weighted contribution is zero. -/
def conditionalChannel (k : ℕ) (px py pz : ℝ) (s : Qubits k) : Superop Bool Bool :=
  if iidCatSyndromeMass k px py pz s = 0 then id
  else fun rho => ((iidCatSyndromeMass k px py pz s)⁻¹ : ℂ) • branchChannel k px py pz s rho

/-- PDF p.2: actual output with the entire classical syndrome in the receiver. -/
def catInstrumentOutput (k : ℕ) (px py pz : ℝ) :
    Matrix (Bool × (Bool × Qubits k)) (Bool × (Bool × Qubits k)) ℂ :=
  fun x y => if x.2.2 = y.2.2 then
    branchBell k px py pz x.2.2 (x.1, x.2.1) (y.1, y.2.1) else 0

/-- PDF p.2, Eq.(5): signed Bell-input cat rate, without optimizing the input. -/
def catRate (k : ℕ) (px py pz : ℝ) : ℝ :=
  (vnEntropy (traceLeft (catInstrumentOutput k px py pz)) -
    vnEntropy (catInstrumentOutput k px py pz)) / (k + 1 : ℕ)

/-- PDF p.2: tensor product of this fixed inner cat encoder on n blocks. -/
def catBlockEncoder (k n : ℕ) : Matrix (Fin n → Qubits (k + 1)) (Qubits n) ℂ :=
  fun y x => ∏ i, QAlgorithms.Papers.Independent.Support50.P40.catEncoder k (y i) (x i)

/-- PDF p.2, Eq.(5): operational fixed-cat/additive-outer achievability.
The encoder is fixed before the unknown input. All sufficiently large positive
outer blocklengths work, with rate measured per (k+1)n physical qubits. The only
resources are the specified encoder, independent noise and a CPTP decoder. -/
def CatAchievable (k : ℕ) (px py pz R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n ≥ n0, ∃ l : ℕ, (R - delta) * ((k + 1) * n : ℕ) ≤ (l : ℝ) ∧
    ∃ E : Matrix (Qubits n) (Qubits l) ℂ, QAlgorithms.Papers.Independent.Support50.P40.IsAdditiveEncoder E ∧
    ∃ D : Superop (Fin n → Qubits (k + 1)) (Qubits l), IsChannel D ∧
      let transmission := D ∘ piSuperop (fun _ : Fin n => iidPauliNoise (k + 1) px py pz) ∘
        conjSuperop (catBlockEncoder k n) ∘ conjSuperop E
      1 - epsilon ≤ entanglementFidelity transmission ∧
      ∀ psi : EuclideanSpace ℂ (Qubits l), IsState psi →
        1 - epsilon ≤ effectProb (pureDensity psi) (transmission (pureDensity psi))

/-- PDF pp.2--3: distribution of the syndrome Hamming weight, summing strings
only here. -/
def syndromeWeightMass (k : ℕ) (px py pz : ℝ) (r : ℕ) : ℝ :=
  ∑ s : Qubits k, if hammingWeight s = r then iidCatSyndromeMass k px py pz s else 0

/-- PDF pp.2--3: mass away from BOTH limiting syndrome-weight centers.
The k=0 branch is defined separately, avoiding a meaningless empty-word ratio. -/
def concentrationTail (k : ℕ) (qx qz epsilon : ℝ) : ℝ :=
  if k = 0 then 0 else ∑ s : Qubits k,
    if epsilon < min |(hammingWeight s : ℝ) / k - qx|
      |(hammingWeight s : ℝ) / k - (1 - qx)|
    then iidCatSyndromeMass k (qx * (1 - qz)) (qx * qz) (qz * (1 - qx)) s else 0

/-- PDF p.3: X-basis cat, including the logical Hadamard H^tensor(b+1) Enc H. -/
def xCatEncoder (b : ℕ) : Matrix (Qubits (b + 1)) Bool ℂ :=
  fun y c => ∑ d : Bool, (∏ j : Fin (b + 1), hadamard (y j) d) * hadamard d c

/-- PDF p.3: encode the outer X cat, then an inner Z cat on EACH output.
The physical register consists of b+1 blocks of a+1 qubits. -/
def concatenatedEncoder (a b : ℕ) : Matrix (Fin (b + 1) → Qubits (a + 1)) Bool ℂ :=
  fun x c => ∑ y : Qubits (b + 1),
    xCatEncoder b y c * ∏ j : Fin (b + 1), QAlgorithms.Papers.Independent.Support50.P40.catEncoder a (x j) (y j)

/-- PDF pp.2--3: tensor copies of the fixed two-level inner encoder.
Every physical wire is indexed by (copy, outer-cat wire, inner-cat wire). -/
def concatenatedBlockEncoder (a b n : ℕ) :
    Matrix (Fin n → (Fin (b + 1) → Qubits (a + 1))) (Qubits n) ℂ :=
  fun y x => ∏ i, concatenatedEncoder a b (y i) (x i)

/-- PDF pp.2--3, Eq.(5) and Concatenated Repetition Codes: communication
through the fixed two-level inner cat and an additive random-code outer layer.
Rates count (a+1)(b+1)n physical uses; one code handles every unknown input. -/
def ConcatenatedAchievable (a b : ℕ) (p R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n ≥ n0, ∃ l : ℕ, (R - delta) * (((a + 1) * (b + 1)) * n : ℕ) ≤ (l : ℝ) ∧
    ∃ E : Matrix (Qubits n) (Qubits l) ℂ,
      QAlgorithms.Papers.Independent.Support50.P40.IsAdditiveEncoder E ∧
    ∃ D : Superop (Fin n → (Fin (b + 1) → Qubits (a + 1))) (Qubits l), IsChannel D ∧
      let innerNoise := piSuperop (fun _ : Fin (b + 1) =>
        iidPauliNoise (a + 1) (p / 3) (p / 3) (p / 3))
      let transmission := D ∘ piSuperop (fun _ : Fin n => innerNoise) ∘
        conjSuperop (concatenatedBlockEncoder a b n) ∘ conjSuperop E
      1 - epsilon ≤ entanglementFidelity transmission ∧
      ∀ psi : EuclideanSpace ℂ (Qubits l), IsState psi →
        1 - epsilon ≤ effectProb (pureDensity psi) (transmission (pureDensity psi))

/-- PDF p.3: actual encoded Bell output before the two-level syndrome instrument. -/
def concatenatedRawOutput (a b : ℕ) (p : ℝ) :
    Matrix (Bool × (Fin (b + 1) → Qubits (a + 1)))
      (Bool × (Fin (b + 1) → Qubits (a + 1))) ℂ :=
  idTensorSuperop (R := Bool)
    (piSuperop (fun _ : Fin (b + 1) => iidPauliNoise (a + 1) (p / 3) (p / 3) (p / 3)))
    (idTensorSuperop (R := Bool) (conjSuperop (concatenatedEncoder a b))
      (pureDensity catBellInput))

/-- PDF p.3: inner Z-check branches followed by the outer X-check branch.
The logical Hadamard is included in the inverse of the X-basis encoder. -/
def concatenatedDecoderBranch (a b : ℕ) (t : Qubits b)
    (s : Fin (b + 1) → Qubits a) : Matrix Bool (Fin (b + 1) → Qubits (a + 1)) ℂ :=
  hadamard * decoderBranch b t * hadamardN (b + 1) *
    (Matrix.of fun (y : Qubits (b + 1)) (x : Fin (b + 1) → Qubits (a + 1)) =>
      ∏ j : Fin (b + 1), decoderBranch a (s j) (y j) (x j))

/-- PDF p.3: actual two-level instrument output. Both the outer X-check
syndrome and ALL inner Z-check syndromes are retained at the receiver. -/
def concatenatedOutput (a b : ℕ) (p : ℝ) :
    Matrix (Bool × (Bool × (Qubits b × (Fin (b + 1) → Qubits a))))
      (Bool × (Bool × (Qubits b × (Fin (b + 1) → Qubits a)))) ℂ :=
  fun x y => if x.2.2 = y.2.2 then
    idTensorSuperop (R := Bool)
      (conjSuperop (concatenatedDecoderBranch a b x.2.2.1 x.2.2.2))
      (concatenatedRawOutput a b p) (x.1, x.2.1) (y.1, y.2.1)
  else 0

/-- PDF p.3: signed concatenated-cat rate per (a+1)(b+1) channel uses. -/
def concatenatedRate (a b : ℕ) (p : ℝ) : ℝ :=
  (vnEntropy (traceLeft (concatenatedOutput a b p)) -
    vnEntropy (concatenatedOutput a b p)) / ((a + 1) * (b + 1) : ℕ)

/-- PDF p.3, Fig.2: zero-rate noise threshold, restricted to physical noise
p in [0,3/4]. The explicit zero ensures a nonempty bounded supremum domain. -/
def noiseThreshold (R : ℝ → ℝ) : ℝ :=
  sSup ({0} ∪ {p : ℝ | 0 ≤ p ∧ p ≤ 3 / 4 ∧ 0 < R p})

/-- PDF pp.3--4: N_p^tp with equal X/Z errors and no Y error. -/
def twoPauliChannel (p : ℝ) : Superop Bool Bool :=
  fun rho => ((1 - p : ℝ) : ℂ) • rho +
    ((p / 2 : ℝ) : ℂ) • conjSuperop pauliX rho +
    ((p / 2 : ℝ) : ℂ) • conjSuperop pauliZ rho

/-- PDF pp.3--4: concrete Stinespring matrix, with environment order X,Z,I.
Its two partial traces define the receiver and complement of the SAME dilation. -/
def twoPauliDilation (p : ℝ) : Matrix (Bool × Fin 3) Bool ℂ :=
  fun be c => match be.2.val with
    | 0 => (Real.sqrt (p / 2) : ℂ) * pauliX be.1 c
    | 1 => (Real.sqrt (p / 2) : ℂ) * pauliZ be.1 c
    | _ => (Real.sqrt (1 - p) : ℂ) * (1 : Matrix Bool Bool ℂ) be.1 c

/-! Small checks pin the conventions and degenerate branches, without proving
any of the source results. -/

example (px py pz : ℝ) : pauliMass px py pz true true = py := rfl

example (px py pz : ℝ) (u v : Qubits 0) : pauliErrorWordMass px py pz u v = 1 := by
  simp [pauliErrorWordMass, QAlgorithms.Papers.Independent.Support50.P38.wordMass]

example (k : ℕ) (s : Qubits k) : amplitudeCount k false s = hammingWeight s := rfl

example (k : ℕ) (s : Qubits k) : noAmplitudeCount k true s = hammingWeight s := rfl

example (k : ℕ) (s : Qubits k) (b : Bool) :
    decoderBranch k s b ((QAlgorithms.Papers.Independent.Advance50.P15.repetitionCoordinates k).symm (b, s)) = 1 := by
  simp [decoderBranch]

example (b c : Bool) :
    catBellInput (b, c) = maxEntangled 1 ((fun _ => b), (fun _ => c)) := rfl

example (a b : ℕ) (x : Fin 0 → (Fin (b + 1) → Qubits (a + 1))) (y : Qubits 0) :
    concatenatedBlockEncoder a b 0 x y = 1 := by
  simp [concatenatedBlockEncoder]

example (y : Qubits 1) (c : Bool) :
    xCatEncoder 0 y c = ∑ d : Bool, hadamard (y 0) d * hadamard d c := by
  simp [xCatEncoder]

example (a b : ℕ) (p : ℝ)
    (x y : Bool × (Bool × (Qubits b × (Fin (b + 1) → Qubits a))))
    (h : x.2.2 ≠ y.2.2) : concatenatedOutput a b p x y = 0 := by
  simp [concatenatedOutput, h]

example (k : ℕ) (px py pz : ℝ) (x y : Bool × (Bool × Qubits k))
    (h : x.2.2 ≠ y.2.2) : catInstrumentOutput k px py pz x y = 0 := by
  simp [catInstrumentOutput, h]

example (k : ℕ) (px py pz : ℝ) (s : Qubits k)
    (h : iidCatSyndromeMass k px py pz s = 0) : conditionalChannel k px py pz s = id := by
  simp [conditionalChannel, h]

example (k : ℕ) (x : Fin 0 → Qubits (k + 1)) (y : Qubits 0) :
    catBlockEncoder k 0 x y = 1 := by simp [catBlockEncoder]

example (qx qz epsilon : ℝ) : concentrationTail 0 qx qz epsilon = 0 := by
  simp [concentrationTail]

example (p : ℝ) (b c : Bool) :
    twoPauliDilation p (b, (0 : Fin 3)) c = (Real.sqrt (p / 2) : ℂ) * pauliX b c := rfl

end QAlgorithms.Papers.Independent.Intakenext100.P93


