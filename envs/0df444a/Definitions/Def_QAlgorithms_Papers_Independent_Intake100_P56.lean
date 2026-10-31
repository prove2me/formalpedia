-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P56
-- name    : QAlgorithms_Papers_Independent_Intake100_P56
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:51:04.003187+00:00
-- url     : https://prove2.me/theorems/a42b7203-54ca-406c-917f-0f2670de6186
-- title:
--   Definitions for Extensive nonadditivity of privacy
-- statement:
--   The objects the formalized statements of *Extensive nonadditivity of privacy* (arXiv:0904.4050) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `conditionalBlockMap`: PDF pp.2–3: tensor power of conditional maps on ALL operators, including entangled inputs, with one independent public label per use.
--   - `conditionalReceiver`: PDF pp.1–3: Bob's conditional marginal of the specified dilation.
--   - `environment`: PDF pp.1–3: the complementary marginal; E is not discarded from Eve.
--   - `PublicLabelClassicalCode`: PDF pp.1–3: an unassisted classical block code. The input is independent of all labels; the receiver's POVM may use the entire public transcript.
--   - `classicalError`: PDF pp.1–3: average decoding error for a uniform message; labels are independent across uses and independent of the chosen input.
--   - `PrivateCodeError`: PDF pp.1–3: strong secrecy, including the public descriptions known to Eve. For each transcript all messages approach ONE common normalized environment state. Trace norm is full trace norm; its harmless constant does not affect capacity.
--   - `PublicLabelClassicalAchievable`: PDF pp.1–3: unassisted memoryless classical/private achievability. Every large positive blocklength is allowed; arbitrary mixed, entangled block encodings are optimized. No preshared resource or feedback is included.
--   - `publicLabelClassicalCapacity`: PDF pp.1–3: the operational classical capacity (bits per channel use). For the positive-dimensional constructed channels, the rate set contains zero and is bounded by log_2 of the input dimension.
--   - `publicLabelPrivateCapacity`: PDF pp.1–3: the operational private capacity, with the full complement and public transcript in the secrecy criterion. No capacity bound is assumed.
--   - `PublicLabelQuantumCode`: PDF pp.1–3: unassisted entanglement-transmission block code. Its fixed CPTP encoder precedes every channel label; the CPTP decoder uses the transcript.
--   - `quantumFidelity`: PDF pp.1–3: average squared entanglement fidelity. The reference in this test is untouched; it is not a free entanglement resource for the code.
--   - `QuantumAchievable`: PDF pp.1–3: rates of unassisted quantum communication per use, with arbitrarily small error and rate slack and arbitrary joint encoders/decoders.
--   - `publicLabelQuantumCapacity`: PDF pp.1–3: operational quantum capacity, in qubits per use. Real supremum is used only on the nonempty bounded rate sets of the constructed channels.
--   - `publicLabelCoherentInformation`: PDF p.3: one-use coherent information, averaging conditional finite entropies; there is no subtraction of infinite classical-label entropies.
--   - `RocketLabel`: PDF pp.1–2: the two independently drawn local unitaries.
--   - `rocketLaw`: PDF pp.1–2, Lemma 1 proof: independent normalized Haar samples U,V.
--   - `controlledPhase`: PDF p.2: P|i,j> = exp(2*pi*i*i*j/d)|i,j>; primitive root with positive phase. Coordinates are the integers 0,...,d-1. Used only for d>0.
--   - `rocketDilation`: PDF p.2 and Fig.1: exact conditional BE dilation P(U tensor V). Sampling is classical; its descriptions are public at both outputs.
--   - `halfErasureDilation`: PDF p.3: the whole d-dimensional register is erased with probability 1/2. `none` is an orthogonal flag. Bob and Eve get opposite erasure branches; the amplitude in EACH branch is 1/sqrt(2).
--   - `jointDilation`: PDF p.3: a single paired use of R_d and the independent half-erasure. Input is ((A1,A2),Bprime), output is ((B,erasureBob),(E,erasureEve)).
--   - `doubleBell`: PDF p.3: the SOURCE'S two-Bell-pair purification, in order A : ((A1,A2),Bprime). Each nonzero amplitude is 1/d, not 1/sqrt(d).
--   - `bellInput`: PDF p.3: actual mixed channel input obtained by tracing out reference A from the source's two-Bell purification. No input is chosen after U,V.
--   - `rocketAssistedOutput`: Fig.2, PDF p.3: Bob's BBprime state for input rho on A1 and the fixed Bell pair on A2,Bprime. E is traced out explicitly.
--   - `recoveryUnitary`: Fig.2, PDF p.3: explicit receiver recovery, reading matrix products right to left: undo V^T on Bprime, undo P on BBprime, then undo U on B.
--   - `rocketRecovery`: Fig.2, PDF p.3: the decoder is constructed from the diagram and then traces out Bprime; it is not an arbitrary hypothesized rocketRecovery map.
--   - `guaranteedViolation`: PDF pp.1,4: rocket input dimension D=d^2, rather than product dimension d^3.
--   - `guaranteedFraction`: PDF pp.1,4: guaranteed violation divided by log_2(D), D=d^2.
-- source:
--   Extensive nonadditivity of privacy, arXiv:0904.4050v2, https://arxiv.org/abs/0904.4050v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intake100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Finite matrix-valued decoders use the Borel measurable space of their usual
entrywise topology. This supplies the measurable codomains in all code fields. -/
local instance (I J : Type) : MeasurableSpace (Matrix I J ℂ) := borel _

/-! The public label is a classical variable, copied to both parties. All maps below
are conditional on this variable; no entropy of a continuous classical register is
taken. Encoders are chosen before labels. The conditional complementary map keeps
the discarded quantum output as well as the public label. -/

variable {A B E S : Type} [Fintype A] [Fintype B] [Fintype E]
variable [DecidableEq A] [DecidableEq B] [DecidableEq E] [MeasurableSpace S]

/-- PDF pp.2–3: tensor power of conditional maps on ALL operators, including
entangled inputs, with one independent public label per use. -/
def conditionalBlockMap (N : S → Superop A B) {n : ℕ} (s : Fin n → S) :
    Superop (Fin n → A) (Fin n → B) := piSuperop (fun i => N (s i))

/-- PDF pp.1–3: Bob's conditional marginal of the specified dilation. -/
def conditionalReceiver (W : S → Matrix (B × E) A ℂ) : S → Superop A B :=
  fun s => QAlgorithms.Papers.Independent.Information100.P67.receiverChannel (W s)

/-- PDF pp.1–3: the complementary marginal; E is not discarded from Eve. -/
def environment (W : S → Matrix (B × E) A ℂ) : S → Superop A E :=
  fun s => QAlgorithms.Papers.Independent.Information100.P67.complementaryChannel (W s)

/-- PDF pp.1–3: an unassisted classical block code. The input is independent of
all labels; the receiver's POVM may use the entire public transcript. -/
structure PublicLabelClassicalCode (A B S : Type) [Fintype A] [Fintype B]
    [DecidableEq B] [MeasurableSpace S] (n : ℕ) where
  M : ℕ
  positive : 0 < M
  input : Fin M → Matrix (Fin n → A) (Fin n → A) ℂ
  density : ∀ m, IsDensityMatrix (input m)
  povm : (Fin n → S) → Fin M → Matrix (Fin n → B) (Fin n → B) ℂ
  valid : ∀ s, IsPOVM (povm s)
  measurable : ∀ m, Measurable (fun s => povm s m)

/-- PDF pp.1–3: average decoding error for a uniform message; labels are
independent across uses and independent of the chosen input. -/
def classicalError (N : S → Superop A B) (mu : Measure S) {n : ℕ}
    (C : PublicLabelClassicalCode A B S n) : ℝ :=
  1 - ∫ s, (C.M : ℝ)⁻¹ * ∑ m,
    effectProb (C.povm s m) (conditionalBlockMap N s (C.input m))
      ∂Measure.pi (fun _ : Fin n => mu)

/-- PDF pp.1–3: strong secrecy, including the public descriptions known to Eve.
For each transcript all messages approach ONE common normalized environment state.
Trace norm is full trace norm; its harmless constant does not affect capacity. -/
def PrivateCodeError (Nenv : S → Superop A E) (mu : Measure S) {n : ℕ}
    (C : PublicLabelClassicalCode A B S n) (eps : ℝ) : Prop :=
  ∃ sigma : (Fin n → S) → Matrix (Fin n → E) (Fin n → E) ℂ,
    Measurable sigma ∧ (∀ s, IsDensityMatrix (sigma s)) ∧
    (∫ s, (C.M : ℝ)⁻¹ * ∑ m,
      traceNorm (conditionalBlockMap Nenv s (C.input m) - sigma s)
        ∂Measure.pi (fun _ : Fin n => mu)) ≤ eps

/-- PDF pp.1–3: unassisted memoryless classical/private achievability. Every
large positive blocklength is allowed; arbitrary mixed, entangled block encodings
are optimized. No preshared resource or feedback is included. -/
def PublicLabelClassicalAchievable (isPrivate : Bool) (N : S → Superop A B)
    (Nenv : S → Superop A E) (mu : Measure S) (rate : ℝ) : Prop :=
  0 ≤ rate ∧ ∀ eps : ℝ, 0 < eps → ∀ slack : ℝ, 0 < slack →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∃ C : PublicLabelClassicalCode A B S n,
      rate - slack ≤ Real.logb 2 C.M / (n : ℝ) ∧
      classicalError N mu C ≤ eps ∧
      (isPrivate = true → PrivateCodeError Nenv mu C eps)

/-- PDF pp.1–3: the operational classical capacity (bits per channel use).
For the positive-dimensional constructed channels, the rate set contains zero
and is bounded by log_2 of the input dimension. -/
def publicLabelClassicalCapacity (W : S → Matrix (B × E) A ℂ) (mu : Measure S) : ℝ :=
  sSup {r | PublicLabelClassicalAchievable false (conditionalReceiver W) (environment W) mu r}

/-- PDF pp.1–3: the operational private capacity, with the full complement
and public transcript in the secrecy criterion. No capacity bound is assumed. -/
def publicLabelPrivateCapacity (W : S → Matrix (B × E) A ℂ) (mu : Measure S) : ℝ :=
  sSup {r | PublicLabelClassicalAchievable true (conditionalReceiver W) (environment W) mu r}

/-- PDF pp.1–3: unassisted entanglement-transmission block code. Its fixed
CPTP encoder precedes every channel label; the CPTP decoder uses the transcript. -/
structure PublicLabelQuantumCode (A B S : Type) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [MeasurableSpace S] (n : ℕ) where
  M : ℕ
  positive : 0 < M
  encoder : Superop (Fin M) (Fin n → A)
  encoder_channel : IsChannel encoder
  decoder : (Fin n → S) → Superop (Fin n → B) (Fin M)
  decoder_channel : ∀ s, IsChannel (decoder s)
  measurable : ∀ X, Measurable (fun s => decoder s X)

/-- PDF pp.1–3: average squared entanglement fidelity. The reference in this
test is untouched; it is not a free entanglement resource for the code. -/
def quantumFidelity (N : S → Superop A B) (mu : Measure S) {n : ℕ}
    (C : PublicLabelQuantumCode A B S n) : ℝ :=
  letI : NeZero C.M := ⟨Nat.ne_of_gt C.positive⟩
  let phi := pureDensity (finiteMaxEntangled (Fin C.M))
  ∫ s, effectProb phi
    (idTensorSuperop (C.decoder s ∘ conditionalBlockMap N s ∘ C.encoder) phi)
      ∂Measure.pi (fun _ : Fin n => mu)

/-- PDF pp.1–3: rates of unassisted quantum communication per use, with
arbitrarily small error and rate slack and arbitrary joint encoders/decoders. -/
def QuantumAchievable (N : S → Superop A B) (mu : Measure S) (rate : ℝ) : Prop :=
  0 ≤ rate ∧ ∀ eps : ℝ, 0 < eps → ∀ slack : ℝ, 0 < slack →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∃ C : PublicLabelQuantumCode A B S n,
      rate - slack ≤ Real.logb 2 C.M / (n : ℝ) ∧
      1 - eps ≤ quantumFidelity N mu C

/-- PDF pp.1–3: operational quantum capacity, in qubits per use. Real supremum
is used only on the nonempty bounded rate sets of the constructed channels. -/
def publicLabelQuantumCapacity (W : S → Matrix (B × E) A ℂ) (mu : Measure S) : ℝ :=
  sSup {r | QuantumAchievable (conditionalReceiver W) mu r}

/-- PDF p.3: one-use coherent information, averaging conditional finite entropies;
there is no subtraction of infinite classical-label entropies. -/
def publicLabelCoherentInformation (W : S → Matrix (B × E) A ℂ) (mu : Measure S)
    (rho : Matrix A A ℂ) : ℝ :=
  ∫ s, vnEntropy (conditionalReceiver W s rho) - vnEntropy (environment W s rho) ∂mu

/-- PDF pp.1–2: the two independently drawn local unitaries. -/
abbrev RocketLabel (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ × Matrix.unitaryGroup (Fin d) ℂ

/-- PDF pp.1–2, Lemma 1 proof: independent normalized Haar samples U,V. -/
def rocketLaw (d : ℕ) : Measure (RocketLabel d) :=
  (Schur.unitaryHaar d).prod (Schur.unitaryHaar d)

/-- PDF p.2: P|i,j> = exp(2*pi*i*i*j/d)|i,j>; primitive root with positive
phase. Coordinates are the integers 0,...,d-1. Used only for d>0. -/
def controlledPhase (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun x y => if x = y then
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x.1.val : ℂ) * (x.2.val : ℂ) / (d : ℂ))
    else 0

/-- PDF p.2 and Fig.1: exact conditional BE dilation P(U tensor V).
Sampling is classical; its descriptions are public at both outputs. -/
def rocketDilation (d : ℕ) (s : RocketLabel d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  controlledPhase d * Matrix.kronecker
    (s.1 : Matrix (Fin d) (Fin d) ℂ) (s.2 : Matrix (Fin d) (Fin d) ℂ)

/-- PDF p.3: the whole d-dimensional register is erased with probability 1/2.
`none` is an orthogonal flag. Bob and Eve get opposite erasure branches;
the amplitude in EACH branch is 1/sqrt(2). -/
def halfErasureDilation (d : ℕ) (_s : Unit) :
    Matrix (Option (Fin d) × Option (Fin d)) (Fin d) ℂ :=
  QAlgorithms.Papers.Independent.Information100.P67.erasureDilation
    (A := Fin d) (1 / 2)

/-- PDF p.3: a single paired use of R_d and the independent half-erasure.
Input is ((A1,A2),Bprime), output is ((B,erasureBob),(E,erasureEve)). -/
def jointDilation (d : ℕ) (s : RocketLabel d) :
    Matrix ((Fin d × Option (Fin d)) × (Fin d × Option (Fin d)))
      ((Fin d × Fin d) × Fin d) ℂ :=
  fun be a => rocketDilation d s (be.1.1, be.2.1) a.1 *
    halfErasureDilation d () (be.1.2, be.2.2) a.2

/-- PDF p.3: the SOURCE'S two-Bell-pair purification, in order
A : ((A1,A2),Bprime). Each nonzero amplitude is 1/d, not 1/sqrt(d). -/
def doubleBell (d : ℕ) :
    EuclideanSpace ℂ (Fin d × ((Fin d × Fin d) × Fin d)) :=
  WithLp.toLp 2 fun x =>
    if x.1 = x.2.1.1 ∧ x.2.1.2 = x.2.2 then (d : ℂ)⁻¹ else 0

/-- PDF p.3: actual mixed channel input obtained by tracing out reference A
from the source's two-Bell purification. No input is chosen after U,V. -/
def bellInput (d : ℕ) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  traceLeft (pureDensity (doubleBell d))

/-- Fig.2, PDF p.3: Bob's BBprime state for input rho on A1 and the fixed
Bell pair on A2,Bprime. E is traced out explicitly. -/
def rocketAssistedOutput (d : ℕ) (hd : 0 < d) (s : RocketLabel d)
    (rho : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let phi := pureDensity (finiteMaxEntangled (Fin d))
  fun b c => ∑ e : Fin d, ∑ a : Fin d × Fin d, ∑ z : Fin d × Fin d,
    rocketDilation d s (b.1,e) a * rho a.1 z.1 * phi (a.2,b.2) (z.2,c.2) *
      conj (rocketDilation d s (c.1,e) z)

/-- Fig.2, PDF p.3: explicit receiver recovery, reading matrix products right
to left: undo V^T on Bprime, undo P on BBprime, then undo U on B. -/
def recoveryUnitary (d : ℕ) (s : RocketLabel d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker ((s.1 : Matrix (Fin d) (Fin d) ℂ)ᴴ)
    (1 : Matrix (Fin d) (Fin d) ℂ) *
    (controlledPhase d)ᴴ *
    Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ)
      (((s.2 : Matrix (Fin d) (Fin d) ℂ).transpose)ᴴ)

/-- Fig.2, PDF p.3: the decoder is constructed from the diagram and then
traces out Bprime; it is not an arbitrary hypothesized rocketRecovery map. -/
def rocketRecovery (d : ℕ) (s : RocketLabel d) :
    Superop (Fin d × Fin d) (Fin d) :=
  fun X => traceRight (recoveryUnitary d s * X * (recoveryUnitary d s)ᴴ)

/-- PDF pp.1,4: rocket input dimension D=d^2, rather than product dimension d^3. -/
def guaranteedViolation (d : ℕ) : ℝ := (1 / 2 : ℝ) * Real.logb 2 d - 2

/-- PDF pp.1,4: guaranteed violation divided by log_2(D), D=d^2. -/
def guaranteedFraction (d : ℕ) : ℝ :=
  guaranteedViolation d / (2 * Real.logb 2 d)

/-! Small structural sanity examples (no theorem proofs in this stage). -/

example (d : ℕ) (x : Fin d × Fin d) :
    controlledPhase d x x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x.1.val : ℂ) * (x.2.val : ℂ) / (d : ℂ)) := by
  simp [controlledPhase]

example : controlledPhase 1 (0,0) (0,0) = 1 := by
  simp [controlledPhase]

example (d : ℕ) (a : Fin d) :
    halfErasureDilation d () (some a,none) a = ((Real.sqrt (1 - (1 / 2 : ℝ))) : ℂ) := by
  simp [halfErasureDilation, QAlgorithms.Papers.Independent.Information100.P67.erasureDilation]

example (d : ℕ) (a : Fin d) : halfErasureDilation d () (none,none) a = 0 := by
  simp [halfErasureDilation, QAlgorithms.Papers.Independent.Information100.P67.erasureDilation]

example : doubleBell 1 (0,((0,0),0)) = 1 := by
  simp [doubleBell]

example {n : ℕ} (N : S → Superop A B) (s : Fin n → S) :
    conditionalBlockMap N s = piSuperop (fun i => N (s i)) := rfl

example : guaranteedFraction 1 = 0 := by
  simp [guaranteedFraction, guaranteedViolation]

end QAlgorithms.Papers.Independent.Intake100.P56


