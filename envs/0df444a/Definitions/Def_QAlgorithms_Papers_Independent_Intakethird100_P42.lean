-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P42
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:08:10.654318+00:00
-- url     : https://prove2.me/theorems/ad3a1018-f09e-4f0e-a869-ea328574f1b4
-- title:
--   Definitions for Channel simulation with quantum side information
-- statement:
--   The objects the formalized statements of *Channel simulation with quantum side information* (arXiv:quant-ph/0611008) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SimulationBasis`: PDF p.4: classical blocks X^n,Y_A^n,Y_B^n and the retained quantum B^n.
--   - `CQFeedbackCode`: PDF p.4: one forward classical message, uniform independent shared bits, private stochastic encoding, a coin/message-controlled POVM, and one deterministic output function used by both parties. The POVM is implemented by its canonical square-root instrument, as required by the gentle measurement paragraph on p.12.
--   - `feedbackMeasurementBranch`: PDF pp.4,12, Eq.(6): reuse the accepted square-root instrument on a finite basis. The equivalence only relabels B as Fin (card B) and back; no coordinate or measurement outcome is discarded, and the branch remains unnormalized.
--   - `simulationTarget`: PDF pp.3--4, Eqs.(2),(4),(5): the memoryless feedback target, including X and B.
--   - `simulationOutput`: PDF p.4, Eq.(6): actual joint output, averaged over the independent uniform coin and Alice's stochastic record. Bob's record is measured, not supplied by Alice.
--   - `feedbackTraceError`: PDF p.4, Eq.(6): full trace norm, without the trace-distance factor 1/2.
--   - `SimulationAchievable`: PDF pp.4--5: operational achievability. Integer bit budgets replace nR,nC; rounding is covered by every positive rate slack. Codes precede the sampled input.
--   - `SourceSimulation`: PDF p.14, Eq.(36): source-relative resource simulation, with identities initially distributing X to Alice and B to Bob and a feedback W at the output. This is the same physical Eq.(6) task, not universal arbitrary-input simulation.
--   - `bookProbability`: PDF pp.6--9: probability of an event of a mutually independent q^n codebook. The codebook is fixed before a uniform index is sampled to define its empirical law.
--   - `empiricalLaw`: PDF p.6: the conditional law of G(W) for a fixed codebook, with W uniform on [M].
--   - `dilutionError`: PDF p.6: full classical l1 error; there is no factor 1/2.
--   - `CoverEncoder`: PDF p.7: a fully normalized stochastic encoder, including zero-marginal rows.
--   - `coveringMarginal`: PDF p.7: p(x) is derived from q(y)P(x|y), not a free marginal parameter.
--   - `coveringError`: PDF pp.7,9: full l1 comparison on [M] times X, not merely an output marginal.
--   - `productConditional`: PDF p.9: the conditional product channel P^n(x^n|y^n).
--   - `RDDatum`: PDF pp.15--16: finite-block variational datum, over all finite positive classical auxiliary alphabets and all message-controlled reconstruction POVMs.
--   - `wordDistortion`: PDF p.15: additive per-letter distortion; theorems only use positive n.
--   - `rdExpected`: PDF p.16: expected distortion includes the decoder's actual Born probability.
--   - `blockRD`: PDF p.16: finite-block variational value in extended nonnegative reals. Empty feasible sets have value infinity. Finite attainment is asserted below, not built into a hypothesis or lost by use of real sInf's empty-set default.
--   - `ExactDistortionCode`: PDF pp.15--16: a deterministic encoder and a message-controlled reconstruction POVM. Outcomes have already been coarsened to the reproduced word. No common randomness, entanglement, or additional communication is supplied.
--   - `exactDistortionExpected`: PDF p.16: literal finite-block expected distortion, including the actual Born probabilities of Bob's reconstruction; the source is not replaced by its mean.
--   - `ExactDistortionAchievable`: PDF p.16: the printed operational convention has rate slack but exact expected distortion at each sufficiently large block. It is kept here for the p.17 converse; no equality with Theorem 4.2's variational limit is asserted.
--   - `exactDistortionRate`: PDF p.16: infimum of literal achievable nonnegative rates. The empty set has value infinity, so an impossible distortion target cannot become a zero rate.
--   - `QuantumRDChoice`: PDF p.17: a finite-dimensional CQ channel X to C and a joint C B reconstruction POVM. The positive dimension is part of the datum and has NO upper bound. Every channel output is a density, even at source labels of weight zero.
--   - `quantumRDExpected`: PDF p.17: expected one-letter distortion. Given X=x the quantum systems C and B are in the PRODUCT state W(x) tensor rho_x; the decoder is joint on CB.
--   - `quantumRDCost`: PDF p.17: I(X;C)-I(C;B) in bits. The accepted label information and conditional-product average compute both information terms from the same source.
--   - `quantumRDValue`: PDF p.17: optimize over ALL finite positive auxiliary dimensions and all joint reconstruction POVMs. Nonnegativity follows from the conditional-product source; ofReal does not clip valid costs. Finite attainment is a theorem conclusion.
--   - `redistributionReceiverInformation`: PDF p.18: I(Bhat;B), computed in the same pure four-register source.
--   - `senderMutual`: PDF p.18: I(Bhat;Ahat), computed by actual partial traces.
--   - `fqrsQuantum`: PDF p.18: FQRS communication I(Bhat;RB)/2, without dropping Bob's register.
--   - `printedQuantumCost`: PDF p.18, Proposition 5.1: printed I(Bhat;R|Ahat)/2. For a pure source this equals the accepted quantumCost I(Bhat;R|B)/2 by complementary entropy duality; retaining the printed conditioning avoids silently changing the result.
--   - `diagonalCQSource`: PDF pp.17,19: classical side information as diagonal conditional densities. The channel Z(.|x) is normalized even on zero-probability source labels.
--   - `CQFeedbackCode.IsClassical`: PDF p.19: diagonal POVMs are classical stochastic decoding of the retained Z^n. Their square-root instruments leave each classical basis label intact.
--   - `ClassicalSimulationAchievable`: PDF p.19: fully classical version of the Eq.(6) task. Diagonal instruments preserve the original Z^n; X^n and both Y^n outputs are still in the error test.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, https://arxiv.org/abs/quant-ph/0611008v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

/-!
Luo--Devetak, arXiv:quant-ph/0611008v1. Entropies and resource rates are in bits.
The accepted paper modules imported here are frozen, reviewed library interfaces.
Distinct source-specific definitions are paper-local; the accepted Luders branch
is reused through finite-basis relabelling. The simulation relation is computed from an
encoder, a square-root measurement instrument and two feedback outputs; it is
not defined by its proposed entropy region. The two source-ambiguity deferrals and the
exact Theorem 4.1 reuse are recorded in the unit artifacts. Compilation pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal
open Filter
open QAlgorithms.Papers.Independent.Dependency50.P07
open QAlgorithms.Papers.Independent.Gap48.P20
open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.4: classical blocks X^n,Y_A^n,Y_B^n and the retained quantum B^n. -/
abbrev SimulationBasis (X B : Type) (y n : ℕ) :=
  Copies X n × (Copies (Fin y) n × (Copies (Fin y) n × Copies B n))

/-- PDF p.4: one forward classical message, uniform independent shared bits,
private stochastic encoding, a coin/message-controlled POVM, and one deterministic
output function used by both parties. The POVM is implemented by its canonical
square-root instrument, as required by the gentle measurement paragraph on p.12. -/
structure CQFeedbackCode (X B : Type) [Fintype B] (y n : ℕ) where
  coinBits : ℕ
  messageBits : ℕ
  privateBits : ℕ
  encode : Copies X n → Qubits coinBits → Qubits messageBits → Qubits privateBits → ℝ
  encode_nonnegative : ∀ x l m s, 0 ≤ encode x l m s
  encode_normalized : ∀ x l, (∑ m, ∑ s, encode x l m s) = 1
  measure : Qubits coinBits → Qubits messageBits → Qubits privateBits →
    Matrix (Copies B n) (Copies B n) ℂ
  measure_valid : ∀ l m, IsPOVM (measure l m)
  decode : Qubits coinBits → Qubits messageBits → Qubits privateBits → Copies (Fin y) n

/-- PDF pp.4,12, Eq.(6): reuse the accepted square-root instrument on a finite
basis. The equivalence only relabels B as Fin (card B) and back; no coordinate or
measurement outcome is discarded, and the branch remains unnormalized. -/
def feedbackMeasurementBranch {B : Type} [Fintype B]
    (effect rho : Matrix B B ℂ) : Matrix B B ℂ :=
  let e := Fintype.equivFin B
  (QAlgorithms.Papers.Independent.Claimed50.P40.ludersBranch
    (fun _ : Unit => effect.submatrix e.symm e.symm)
    (rho.submatrix e.symm e.symm) ()).submatrix e e

/-- PDF pp.3--4, Eqs.(2),(4),(5): the memoryless feedback target, including X and B. -/
def simulationTarget {X B : Type} (E : CQData X B) (V : Auxiliary X) (n : ℕ) :
    Matrix (SimulationBasis X B V.size n) (SimulationBasis X B V.size n) ℂ :=
  fun a b =>
    if a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 ∧ a.2.1 = a.2.2.1 then
      ((wordProb E.prob n a.1 * ∏ i, V.channel (a.1 i) (a.2.1 i)) : ℂ) *
        wordState E n a.1 a.2.2.2 b.2.2.2
    else 0

/-- PDF p.4, Eq.(6): actual joint output, averaged over the independent uniform
coin and Alice's stochastic record. Bob's record is measured, not supplied by Alice. -/
def simulationOutput {X B : Type} [Fintype B] (E : CQData X B) {y n : ℕ}
    (P : CQFeedbackCode X B y n) :
    Matrix (SimulationBasis X B y n) (SimulationBasis X B y n) ℂ :=
  fun a b => if a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 then
    ∑ l : Qubits P.coinBits, ∑ m : Qubits P.messageBits,
      ∑ s : Qubits P.privateBits, ∑ t : Qubits P.privateBits,
        if P.decode l m s = a.2.1 ∧ P.decode l m t = a.2.2.1 then
          ((wordProb E.prob n a.1 * ((2 : ℝ) ^ P.coinBits)⁻¹ *
              P.encode a.1 l m s) : ℂ) *
            feedbackMeasurementBranch (P.measure l m t) (wordState E n a.1) a.2.2.2 b.2.2.2
        else 0
    else 0

/-- PDF p.4, Eq.(6): full trace norm, without the trace-distance factor 1/2. -/
def feedbackTraceError {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (V : Auxiliary X) {n : ℕ} (P : CQFeedbackCode X B V.size n) : ℝ :=
  traceNorm (simulationTarget E V n - simulationOutput E P)

/-- PDF pp.4--5: operational achievability. Integer bit budgets replace nR,nC;
rounding is covered by every positive rate slack. Codes precede the sampled input. -/
def SimulationAchievable {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (V : Auxiliary X) (R C : ℝ) : Prop :=
  0 ≤ R ∧ 0 ≤ C ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : CQFeedbackCode X B V.size n,
      feedbackTraceError E V P ≤ eps ∧ (P.messageBits : ℝ) ≤ n * (R + delta) ∧
        (P.coinBits : ℝ) ≤ n * (C + delta)

/-- PDF p.14, Eq.(36): source-relative resource simulation, with identities
initially distributing X to Alice and B to Bob and a feedback W at the output.
This is the same physical Eq.(6) task, not universal arbitrary-input simulation. -/
def SourceSimulation {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (V : Auxiliary X) (R C : ℝ) : Prop :=
  SimulationAchievable E V R C

example {B : Type} [Fintype B] (rho : Matrix B B ℂ) :
    feedbackMeasurementBranch 0 rho = 0 := by
  simp [feedbackMeasurementBranch,
    QAlgorithms.Papers.Independent.Claimed50.P40.ludersBranch, cfc_zero]

example {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (V : Auxiliary X) (R C : ℝ) :
    SourceSimulation E V R C ↔ SimulationAchievable E V R C := Iff.rfl

/-- PDF pp.6--9: probability of an event of a mutually independent q^n codebook.
The codebook is fixed before a uniform index is sampled to define its empirical law. -/
def bookProbability {Y : Type} [Fintype Y] (q : Y → ℝ) (n M : ℕ)
    (event : (Fin M → Copies Y n) → Prop) : ℝ :=
  ∑ book : Fin M → Copies Y n,
    if event book then ∏ i, wordProb q n (book i) else 0

/-- PDF p.6: the conditional law of G(W) for a fixed codebook, with W uniform on [M]. -/
def empiricalLaw {Y : Type} [Fintype Y] {M : ℕ} (book : Fin M → Y) (y : Y) : ℝ :=
  (∑ i, if book i = y then (1 : ℝ) else 0) / M

/-- PDF p.6: full classical l1 error; there is no factor 1/2. -/
def dilutionError {Y : Type} [Fintype Y] (q : Y → ℝ) (n M : ℕ)
    (book : Fin M → Copies Y n) : ℝ :=
  ∑ y, |wordProb q n y - empiricalLaw book y|

/-- PDF p.7: a fully normalized stochastic encoder, including zero-marginal rows. -/
abbrev CoverEncoder (X : Type) [Fintype X] (M : ℕ) :=
  {e : X → Fin M → ℝ // ∀ x, IsProbability (e x)}

/-- PDF p.7: p(x) is derived from q(y)P(x|y), not a free marginal parameter. -/
def coveringMarginal {X Y : Type} [Fintype Y] (q : Y → ℝ) (P : Y → X → ℝ) (x : X) : ℝ :=
  ∑ y, q y * P y x

/-- PDF pp.7,9: full l1 comparison on [M] times X, not merely an output marginal. -/
def coveringError {X Y : Type} [Fintype X] [Fintype Y]
    (q : Y → ℝ) (P : Y → X → ℝ) (M : ℕ) (book : Fin M → Y)
    (e : CoverEncoder X M) : ℝ :=
  ∑ i, ∑ x, |P (book i) x / M - coveringMarginal q P x * e.val x i|

/-- PDF p.9: the conditional product channel P^n(x^n|y^n). -/
def productConditional {X Y : Type} (P : Y → X → ℝ) (n : ℕ)
    (y : Copies Y n) (x : Copies X n) : ℝ := ∏ i, P (y i) (x i)

example {Y : Type} [Fintype Y] (q : Y → ℝ) (n M : ℕ) :
    bookProbability q n M (fun _ => False) = 0 := by
  simp [bookProbability]

example {X Y : Type} (P : Y → X → ℝ) (x : Copies X 0) (y : Copies Y 0) :
    productConditional P 0 y x = 1 := by
  simp [productConditional]

example {Y : Type} [Fintype Y] [Subsingleton Y] [Nonempty Y]
    (M : ℕ) (hM : 0 < M) (book : Fin M → Y) (y : Y) :
    empiricalLaw book y = 1 := by
  have hbook : ∀ i, book i = y := fun _ => Subsingleton.elim _ _
  simp [empiricalLaw, hbook, Nat.ne_of_gt hM]

example {X : Type} [Fintype X] : Nonempty (CoverEncoder X 1) := by
  refine ⟨⟨fun _ _ => 1, ?_⟩⟩
  intro x
  exact ⟨fun _ => by norm_num, by simp⟩

/-- PDF pp.15--16: finite-block variational datum, over all finite positive
classical auxiliary alphabets and all message-controlled reconstruction POVMs. -/
structure RDDatum (X B : Type) [Fintype X] [Fintype B] (n : ℕ) where
  auxiliary : Auxiliary (Copies X n)
  decoder : Fin auxiliary.size → Copies X n → Matrix (Copies B n) (Copies B n) ℂ
  decoder_valid : ∀ y, IsPOVM (decoder y)

/-- PDF p.15: additive per-letter distortion; theorems only use positive n. -/
def wordDistortion {X : Type} (d : X → X → ℝ) (n : ℕ)
    (x z : Copies X n) : ℝ := (∑ i, d (x i) (z i)) / n

/-- PDF p.16: expected distortion includes the decoder's actual Born probability. -/
def rdExpected {X B : Type} [Fintype X] [Fintype B] (E : CQData X B)
    (d : X → X → ℝ) {n : ℕ} (P : RDDatum X B n) : ℝ :=
  ∑ x, ∑ y, ∑ z, wordProb E.prob n x * P.auxiliary.channel x y *
    effectProb (P.decoder y z) (wordState E n x) * wordDistortion d n x z

/-- PDF p.16: finite-block variational value in extended nonnegative reals.
Empty feasible sets have value infinity. Finite attainment is asserted below,
not built into a hypothesis or lost by use of real sInf's empty-set default. -/
def blockRD {X B : Type} [Fintype X] [Fintype B] (E : CQData X B)
    (d : X → X → ℝ) (D : ℝ) (n : ℕ) : ℝ≥0∞ :=
  sInf {r | ∃ P : RDDatum X B n, rdExpected E d P ≤ D ∧
    r = ENNReal.ofReal (auxCost (iidCQ E n) P.auxiliary / n)}

example {X : Type} (d : X → X → ℝ) (x z : Copies X 0) :
    wordDistortion d 0 x z = 0 := by simp [wordDistortion]

/-- PDF pp.15--16: a deterministic encoder and a message-controlled reconstruction
POVM. Outcomes have already been coarsened to the reproduced word. No common
randomness, entanglement, or additional communication is supplied. -/
structure ExactDistortionCode (X B : Type) [Fintype X] [Fintype B] (n : ℕ) where
  messageBits : ℕ
  encode : Copies X n → Qubits messageBits
  decoder : Qubits messageBits → Copies X n → Matrix (Copies B n) (Copies B n) ℂ
  decoder_valid : ∀ m, IsPOVM (decoder m)

/-- PDF p.16: literal finite-block expected distortion, including the actual
Born probabilities of Bob's reconstruction; the source is not replaced by its mean. -/
def exactDistortionExpected {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (d : X → X → ℝ) {n : ℕ} (P : ExactDistortionCode X B n) : ℝ :=
  ∑ x, ∑ z, wordProb E.prob n x *
    effectProb (P.decoder (P.encode x) z) (wordState E n x) * wordDistortion d n x z

/-- PDF p.16: the printed operational convention has rate slack but exact
expected distortion at each sufficiently large block. It is kept here for the
p.17 converse; no equality with Theorem 4.2's variational limit is asserted. -/
def ExactDistortionAchievable {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (d : X → X → ℝ) (D R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
    ∃ P : ExactDistortionCode X B n,
      exactDistortionExpected E d P ≤ D ∧ (P.messageBits : ℝ) ≤ n * (R + delta)

/-- PDF p.16: infimum of literal achievable nonnegative rates. The empty set
has value infinity, so an impossible distortion target cannot become a zero rate. -/
def exactDistortionRate {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (d : X → X → ℝ) (D : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ R : ℝ, ExactDistortionAchievable E d D R ∧ r = ENNReal.ofReal R}

/-- PDF p.17: a finite-dimensional CQ channel X to C and a joint C B
reconstruction POVM. The positive dimension is part of the datum and has NO
upper bound. Every channel output is a density, even at source labels of weight zero. -/
structure QuantumRDChoice (X B : Type) [Fintype X] [Fintype B] where
  dimension : ℕ
  positive : 0 < dimension
  output : X → Matrix (Fin dimension) (Fin dimension) ℂ
  output_valid : ∀ x, IsDensityMatrix (output x)
  decoder : X → Matrix (Fin dimension × B) (Fin dimension × B) ℂ
  decoder_valid : IsPOVM decoder

/-- PDF p.17: expected one-letter distortion. Given X=x the quantum systems
C and B are in the PRODUCT state W(x) tensor rho_x; the decoder is joint on CB. -/
def quantumRDExpected {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (d : X → X → ℝ) (P : QuantumRDChoice X B) : ℝ :=
  ∑ x, ∑ z, E.prob x *
    effectProb (P.decoder z) (Matrix.kronecker (P.output x) (E.state x)) * d x z

/-- PDF p.17: I(X;C)-I(C;B) in bits. The accepted label information and
conditional-product average compute both information terms from the same source. -/
def quantumRDCost {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (P : QuantumRDChoice X B) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P27.labelInformation E.prob P.output -
    (vnEntropy (QAlgorithms.Papers.Independent.Information100.P27.average E.prob P.output) +
      vnEntropy (ensembleMean E) -
      vnEntropy (QAlgorithms.Papers.Independent.Information100.P27.memoryEnvironment
        E.prob E.state P.output))

/-- PDF p.17: optimize over ALL finite positive auxiliary dimensions and all
joint reconstruction POVMs. Nonnegativity follows from the conditional-product
source; ofReal does not clip valid costs. Finite attainment is a theorem conclusion. -/
def quantumRDValue {X B : Type} [Fintype X] [Fintype B]
    (E : CQData X B) (d : X → X → ℝ) (D : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ P : QuantumRDChoice X B, quantumRDExpected E d P ≤ D ∧
    r = ENNReal.ofReal (quantumRDCost E P)}

example {X B : Type} [Fintype X] [Fintype B] (E : CQData X B)
    (P : ExactDistortionCode X B 0) (d : X → X → ℝ) :
    exactDistortionExpected E d P = 0 := by
  simp [exactDistortionExpected, wordDistortion]

example {X B : Type} [Fintype X] [Fintype B] (E : CQData X B)
    (P : QuantumRDChoice X B) : quantumRDExpected E (fun _ _ => 0) P = 0 := by
  simp [quantumRDExpected]

/-- PDF p.18: I(Bhat;B), computed in the same pure four-register source. -/
def redistributionReceiverInformation {A C B R : Type} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => p.2.2.1)
      (fun p => (p.1, p.2.1, p.2.2.2)) +
    subsystemEntropy (pureDensity psi) (fun p => p.2.2.2)
      (fun p => (p.1, p.2.1, p.2.2.1)) -
    subsystemEntropy (pureDensity psi) (fun p => p.2.2) (fun p => (p.1, p.2.1))

/-- PDF p.18: I(Bhat;Ahat), computed by actual partial traces. -/
def senderMutual {A C B R : Type} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => p.2.2.1)
      (fun p => (p.1, p.2.1, p.2.2.2)) +
    subsystemEntropy (pureDensity psi) (fun p => p.2.1) (fun p => (p.1, p.2.2)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.2.1, p.2.2.1))
      (fun p => (p.1, p.2.2.2))

/-- PDF p.18: FQRS communication I(Bhat;RB)/2, without dropping Bob's register. -/
def fqrsQuantum {A C B R : Type} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  (subsystemEntropy (pureDensity psi) (fun p => p.2.2.1)
      (fun p => (p.1, p.2.1, p.2.2.2)) +
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2.2))
      (fun p => (p.2.1, p.2.2.1)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2))
      (fun p => p.2.1)) / 2

/-- PDF p.18, Proposition 5.1: printed I(Bhat;R|Ahat)/2. For a pure source
this equals the accepted quantumCost I(Bhat;R|B)/2 by complementary entropy
duality; retaining the printed conditioning avoids silently changing the result. -/
def printedQuantumCost {A C B R : Type} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  (subsystemEntropy (pureDensity psi) (fun p => (p.2.1, p.2.2.1))
      (fun p => (p.1, p.2.2.2)) +
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.1))
      (fun p => p.2.2) -
    subsystemEntropy (pureDensity psi) (fun p => p.2.1)
      (fun p => (p.1, p.2.2)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.1, p.2.2.1))
      (fun p => p.2.2.2)) / 2

example {A C B R : Type} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) :
    fqrsQuantum psi = (subsystemEntropy (pureDensity psi) (fun p => p.2.2.1)
      (fun p => (p.1, p.2.1, p.2.2.2)) +
      subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2.2))
        (fun p => (p.2.1, p.2.2.1)) -
      subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2))
        (fun p => p.2.1)) / 2 := rfl

/-- PDF pp.17,19: classical side information as diagonal conditional densities.
The channel Z(.|x) is normalized even on zero-probability source labels. -/
def diagonalCQSource {X : Type} (p : X → ℝ) (Z : Auxiliary X) : CQData X (Fin Z.size) where
  prob := p
  state := fun x => Matrix.diagonal (fun z => (Z.channel x z : ℂ))

/-- PDF p.19: diagonal POVMs are classical stochastic decoding of the retained
Z^n. Their square-root instruments leave each classical basis label intact. -/
def CQFeedbackCode.IsClassical {X B : Type} [Fintype B] {y n : ℕ}
    (P : CQFeedbackCode X B y n) : Prop :=
  ∀ l m s u v, u ≠ v → P.measure l m s u v = 0

/-- PDF p.19: fully classical version of the Eq.(6) task. Diagonal instruments
preserve the original Z^n; X^n and both Y^n outputs are still in the error test. -/
def ClassicalSimulationAchievable {X : Type} [Fintype X] (p : X → ℝ)
    (Z V : Auxiliary X) (R C : ℝ) : Prop :=
  0 ≤ R ∧ 0 ≤ C ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : CQFeedbackCode X (Fin Z.size) V.size n,
      P.IsClassical ∧ feedbackTraceError (diagonalCQSource p Z) V P ≤ eps ∧
        (P.messageBits : ℝ) ≤ n * (R + delta) ∧ (P.coinBits : ℝ) ≤ n * (C + delta)

example {X : Type} (p : X → ℝ) (Z : Auxiliary X) (x : X) (z : Fin Z.size) :
    (diagonalCQSource p Z).state x z z = (Z.channel x z : ℂ) := by
  simp [diagonalCQSource]

end QAlgorithms.Papers.Independent.Intakethird100.P42


