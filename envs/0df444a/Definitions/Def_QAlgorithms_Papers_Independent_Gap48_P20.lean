-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
-- name    : QAlgorithms_Papers_Independent_Gap48_P20
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T22:02:02.590425+00:00
-- url     : https://prove2.me/theorems/13527900-6c97-4521-8de2-0b264cdbaf22
-- title:
--   Definitions for The operational meaning of quantum conditional information
-- statement:
--   The objects the formalized statements of *The operational meaning of quantum conditional information* (arXiv:quant-ph/0612050) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Copies`: PDF pp.1–2: n independent copies of a register X.
--   - `RedistributionSource`: PDF pp.1–2: canonical four-register source, with inaccessible R first.
--   - `redistributionMarginal`: PDF p.1: partial trace, specified by complementary coordinate projections. All uses below have (keep,forget) a bijection onto the tensor factors; summing over matching forgotten coordinates retains off-diagonal kept coordinates.
--   - `subsystemEntropy`: PDF p.1: entropy in bits of an explicitly computed redistributionMarginal.
--   - `conditionalCost`: PDF p.2: H(C|B)=H(CB)-H(B), from the actual source density.
--   - `quantumCost`: PDF p.2, (1): I(C;R|B)/2, evaluated from four actual marginals.
--   - `redistributionEntanglementRate`: PDF p.2, (2): (I(C;A)-I(C;B))/2. The common H(C) cancels.
--   - `swappedSource`: PDF p.2: swapping sender and receiver side information, leaving C and R fixed.
--   - `sourceAmplitude`: PDF pp.1–2: the actual pure i.i.d. source amplitude, in grouped copy registers.
--   - `TransferCode`: PDF p.2: one forward message of q qubits, k input Bell pairs and l output Bell pairs. Alice's input is AC and her k halves; Bob's is B and his k halves. The maps are fixed independently of the inaccessible reference input.
--   - `forwardApply`: PDF p.2: the all-operator channel of an encoder, transmission, and decoder. The contraction over both message indices transmits a quantum register; it does not measure that register. This formula includes entangled inputs.
--   - `initial`: PDF p.2: the full source and the independently supplied k Bell pairs.
--   - `redistributionTargetDensity`: PDF p.2: desired joint output on A,C,B,R and both final Bell registers.
--   - `redistributionOutputDensity`: PDF p.2: actual output; no operation ever acts on R.
--   - `redistributionError`: PDF pp.1–2: joint full trace-norm reconstruction error, including ebits.
--   - `netEntanglement`: PDF p.2: signed consumption, with subtraction in the reals.
--   - `HasRedistributionClassicalMessage`: PDF p.3: classical-only message: every encoder output is diagonal in the message register. Complete dephasing, followed by the decoder, transmits only q cbits and no quantum channel. No uncharged additional channel is present.
--   - `RedistributionAchievable`: PDF p.2: independently operational asymptotic two-resource achievability. All sufficiently large positive blocklengths work, for every positive error and rate slack. k and l are separate natural counts and E can be negative.
--   - `ClassicalPairAchievable`: PDF p.3: a classical/entanglement rate pair, with no quantum communication.
--   - `ClassicalAchievable`: PDF p.3: unlimited Bell assistance; k and l have no rate restriction at all. The classical cost still counts every message bit.
--   - `mergingClassicalCost`: PDF p.3: the older merging cbit cost I(RA;C), with A placed in the reference.
--   - `catState`: PDF p.3, application (1): the actual four-qubit cat state, in R,A,C,B order.
--   - `catAliceKraus`: PDF p.3: TP extension of Alice's support isometry. It applies CNOT A→C, then traces out C. On |zz> only the false branch occurs, preserving coherence.
--   - `catAlice`: PDF p.3: Alice's complete local operation on every operator.
--   - `catBobIsometry`: PDF p.3: Bob's genuine isometry |z>→|zz>, on the whole input space.
--   - `catBob`: PDF p.3: Bob's local CPTP operation.
--   - `localProduct`: PDF p.3: tensor product of two local operations, on arbitrary correlated inputs.
--   - `catInput`: PDF p.3: input cat state, grouped into Alice's AC and Bob's B.
--   - `jointSource`: PDF p.2: transfer CD jointly, retaining A.
--   - `firstSource`: PDF p.2: D first, with AC retained by the sender.
--   - `secondSource`: PDF p.3: C second, with DB already held by the receiver.
--   - `sequentialInitial`: PDF pp.2–3: actual initial matrix for stage D. The future stage's Bell bank is untouched, so it is placed together with R in this stage's reference.
--   - `sequentialOutput`: PDF pp.2–3: stage D followed by stage C on the actual first-stage output. The D-stage final Bell pairs become part of stage C's untouched reference.
--   - `sequentialTarget`: PDF pp.2–3: joint target with both final Bell banks, including their absence of correlations with the source and with each other.
--   - `SuccessivelyAchievable`: PDF pp.2–3: operational successive achievability with separate stage costs. Initial Bell banks are supplied for both stages; neither stage is required to have nonnegative net entanglement consumption.
--   - `UnitaryRedistributionCode`: PDF p.2, Fig.2: finite local unitaries with explicit input and output work registers. Rectangular matrices are two-sided inverses, so the corresponding finite Hilbert spaces have equal dimensions. Work dimensions are arbitrary positive integers, rather than just powers of two.
--   - `Input`: PDF p.2: full coherent input basis, including both pure local work registers.
--   - `RedistributionOutputBasis`: PDF p.2: full output basis. No work is discarded in this model.
--   - `globalMatrix`: PDF p.2, Fig.2: the actual global unitary, including transmission and id_R. Its adjoint reverses Bob's decoder first, transmits the same message back, then reverses Alice's encoder.
--   - `redistributionInputVector`: PDF p.2: independent pure local ancillas in fixed basis states, and k ebits.
--   - `redistributionTargetVector`: PDF p.2: pure target with l independent ebits and fixed pure output work. These work registers become the initial local ancillas in the reverse process.
--   - `forwardError`: PDF p.2: full pure-state reconstruction error before tracing any work.
--   - `reverseError`: PDF p.2: error of reversing these same matrices with Bell banks exchanged.
--   - `ReversiblyAchievable`: PDF p.2: one coherent family works in both directions. Both signed ebit bounds are imposed so that reversal achieves -E, including E=0.
--   - `ThreeSource`: PDF p.4: six-register source R,A,C_A,B,C_B,C, with C initially at Charlie.
--   - `ThreeCode`: PDF p.4: two encoders, two separately charged forward messages, one receiver. With no feedback, the receiver may postpone all its actions until both messages arrive. The Bell banks belong to the Alice–Charlie and Bob–Charlie links.
--   - `threeForwardApply`: PDF p.4: the actual all-operator joint action of the two local senders and Charlie. Both transmitted message coherences are contracted, never discarded.
--   - `initial`: PDF p.4: source times the two independent initial Bell banks.
--   - `redistributionTargetDensity`: PDF p.4: desired full state including both independent final Bell banks.
--   - `redistributionError`: PDF p.4: full joint error of the actual finite three-party code.
--   - `ThreePartyAchievable`: PDF p.4: four operational rates with independent Bell accounting per link. The definition does not mention an entropic region or an ordering strategy.
--   - `aliceFirst`: PDF p.4: Alice first. Bob's entire B C_B is inaccessible reference here.
--   - `bobSecond`: PDF p.4: Bob second, with C_A C held by Charlie; A is reference.
--   - `bobFirst`: PDF p.4: Bob first; A C_A is in this stage's reference.
--   - `aliceSecond`: PDF p.4: Alice second, with C_B C held by Charlie; B is reference.
--   - `aliceFirstCorner`: PDF p.4: corner obtained by Alice-to-Charlie, then Bob-to-Charlie.
--   - `bobFirstCorner`: PDF p.4: corner obtained in the opposite order, with the same link order.
--   - `InGeneratedRegion`: PDF p.4: convex time sharing of the two corners, plus the wasting and qubit-for-ebit substitution cone on each link. This is an inner region only.
-- source:
--   The operational meaning of quantum conditional information, arXiv:quant-ph/0612050v2, https://arxiv.org/abs/quant-ph/0612050v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

/-!
Devetak–Yard, arXiv:quant-ph/0612050v2, PDF pp.1–4.
Registers are finite nonzero computational-basis types. The canonical source order
is R,A,C,B; changing tuple association never changes ownership or the source.
Entropy is the accepted finite matrix entropy in bits. Local operations are
complete CPTP maps; every reference block, including off-diagonal ones, is kept.
A finite forward protocol is collected into one encoder, one forward message,
and one decoder: with no reverse messages, Bob's intermediate operations commute
past Alice's later operations and can be postponed. Local ancillas and discarded
work are included in the arbitrary rectangular CPTP encoder and decoder.
The asymptotic definitions below contain no entropy inequalities.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1–2: n independent copies of a register X. -/
abbrev Copies (X : Type*) (n : ℕ) := Fin n → X

/-- PDF pp.1–2: canonical four-register source, with inaccessible R first. -/
abbrev RedistributionSource (A C B R : Type*) := R × (A × (C × B))

/-- PDF p.1: partial trace, specified by complementary coordinate projections.
All uses below have (keep,forget) a bijection onto the tensor factors; summing over
matching forgotten coordinates retains off-diagonal kept coordinates. -/
def redistributionMarginal {X K F : Type*} [Fintype X] (rho : Matrix X X ℂ)
    (keep : X → K) (forget : X → F) : Matrix K K ℂ :=
  fun a b => ∑ x, ∑ y,
    if keep x = a ∧ keep y = b ∧ forget x = forget y then rho x y else 0

/-- PDF p.1: entropy in bits of an explicitly computed redistributionMarginal. -/
def subsystemEntropy {X K F : Type*} [Fintype X] [Fintype K]
    (rho : Matrix X X ℂ) (keep : X → K) (forget : X → F) : ℝ :=
  vnEntropy (redistributionMarginal rho keep forget)

section FourRegisters

variable {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]

/-- PDF p.2: H(C|B)=H(CB)-H(B), from the actual source density. -/
def conditionalCost (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => p.2.2) (fun p => (p.1, p.2.1)) -
    subsystemEntropy (pureDensity psi) (fun p => p.2.2.2)
      (fun p => (p.1, p.2.1, p.2.2.1))

/-- PDF p.2, (1): I(C;R|B)/2, evaluated from four actual marginals. -/
def quantumCost (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  (subsystemEntropy (pureDensity psi) (fun p => p.2.2) (fun p => (p.1, p.2.1)) +
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2.2))
      (fun p => (p.2.1, p.2.2.1)) -
    subsystemEntropy (pureDensity psi) (fun p => p.2.2.2)
      (fun p => (p.1, p.2.1, p.2.2.1)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2)) (fun p => p.2.1)) / 2

/-- PDF p.2, (2): (I(C;A)-I(C;B))/2. The common H(C) cancels. -/
def redistributionEntanglementRate (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  (subsystemEntropy (pureDensity psi) (fun p => p.2.1) (fun p => (p.1, p.2.2)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.2.1, p.2.2.1))
      (fun p => (p.1, p.2.2.2)) -
    subsystemEntropy (pureDensity psi) (fun p => p.2.2.2)
      (fun p => (p.1, p.2.1, p.2.2.1)) +
    subsystemEntropy (pureDensity psi) (fun p => p.2.2) (fun p => (p.1, p.2.1))) / 2

/-- PDF p.2: swapping sender and receiver side information, leaving C and R fixed. -/
def swappedSource (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) :
    EuclideanSpace ℂ (RedistributionSource B C A R) :=
  WithLp.toLp 2 fun p => psi (p.1, (p.2.2.2, (p.2.2.1, p.2.1)))

/-- PDF pp.1–2: the actual pure i.i.d. source amplitude, in grouped copy registers. -/
def sourceAmplitude (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (n : ℕ)
    (r : Copies R n) (a : Copies A n) (c : Copies C n) (b : Copies B n) : ℂ :=
  tensorPow n psi (fun i => (r i, (a i, (c i, b i))))

end FourRegisters

/-- PDF p.2: one forward message of q qubits, k input Bell pairs and l output
Bell pairs. Alice's input is AC and her k halves; Bob's is B and his k halves.
The maps are fixed independently of the inaccessible reference input. -/
structure TransferCode (A C B : Type*) [Fintype A] [Fintype C] [Fintype B] (n : ℕ) where
  q : ℕ
  k : ℕ
  l : ℕ
  encoder : Superop ((Copies A n × Copies C n) × Qubits k)
    ((Copies A n × Qubits l) × Qubits q)
  decoder : Superop (Qubits q × (Copies B n × Qubits k))
    ((Copies C n × Copies B n) × Qubits l)
  encoder_channel : IsChannel encoder
  decoder_channel : IsChannel decoder

/-- PDF p.2: the all-operator channel of an encoder, transmission, and decoder.
The contraction over both message indices transmits a quantum register; it does
not measure that register. This formula includes entangled inputs. -/
def forwardApply {X Y U V M : Type*} [Fintype X] [Fintype Y] [Fintype M]
    (encoder : Superop X (U × M)) (decoder : Superop (M × Y) V) :
    Superop (X × Y) (U × V) :=
  fun rho p p' => ∑ x, ∑ x', ∑ y, ∑ y', ∑ m, ∑ m',
    rho (x, y) (x', y') *
      encoder (Matrix.single x x' 1) (p.1, m) (p'.1, m') *
      decoder (Matrix.single (m, y) (m', y') 1) p.2 p'.2

namespace TransferCode

variable {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
variable {n : ℕ} (P : TransferCode A C B n)

/-- PDF p.2: the full source and the independently supplied k Bell pairs. -/
def initial (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) :
    Matrix (Copies R n × (((Copies A n × Copies C n) × Qubits P.k) ×
      (Copies B n × Qubits P.k)))
      (Copies R n × (((Copies A n × Copies C n) × Qubits P.k) ×
      (Copies B n × Qubits P.k))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    sourceAmplitude psi n p.1 p.2.1.1.1 p.2.1.1.2 p.2.2.1 *
      maxEntangled P.k (p.2.1.2, p.2.2.2))

/-- PDF p.2: desired joint output on A,C,B,R and both final Bell registers. -/
def redistributionTargetDensity (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) :
    Matrix (Copies R n × ((Copies A n × Qubits P.l) ×
      ((Copies C n × Copies B n) × Qubits P.l)))
      (Copies R n × ((Copies A n × Qubits P.l) ×
      ((Copies C n × Copies B n) × Qubits P.l))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    sourceAmplitude psi n p.1 p.2.1.1 p.2.2.1.1 p.2.2.1.2 *
      maxEntangled P.l (p.2.1.2, p.2.2.2))

/-- PDF p.2: actual output; no operation ever acts on R. -/
def redistributionOutputDensity (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) :=
  idTensorSuperop (forwardApply P.encoder P.decoder) (P.initial psi)

/-- PDF pp.1–2: joint full trace-norm reconstruction error, including ebits. -/
def redistributionError (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  traceNorm (P.redistributionOutputDensity psi - P.redistributionTargetDensity psi)

/-- PDF p.2: signed consumption, with subtraction in the reals. -/
def netEntanglement : ℝ := (P.k : ℝ) - (P.l : ℝ)

/-- PDF p.3: classical-only message: every encoder output is diagonal in the
message register. Complete dephasing, followed by the decoder, transmits only
q cbits and no quantum channel. No uncharged additional channel is present. -/
def HasRedistributionClassicalMessage : Prop :=
  ∀ X u v m m', m ≠ m' → P.encoder X (u, m) (v, m') = 0

end TransferCode

/-- PDF p.2: independently operational asymptotic two-resource achievability.
All sufficiently large positive blocklengths work, for every positive error and
rate slack. k and l are separate natural counts and E can be negative. -/
def RedistributionAchievable {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (Q E : ℝ) : Prop :=
  0 ≤ Q ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : TransferCode A C B n,
      P.redistributionError psi ≤ eps ∧ (P.q : ℝ) ≤ n * (Q + delta) ∧
        P.netEntanglement ≤ n * (E + delta)

/-- PDF p.3: a classical/entanglement rate pair, with no quantum communication. -/
def ClassicalPairAchievable {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (c E : ℝ) : Prop :=
  0 ≤ c ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : TransferCode A C B n,
      P.HasRedistributionClassicalMessage ∧ P.redistributionError psi ≤ eps ∧ (P.q : ℝ) ≤ n * (c + delta) ∧
        P.netEntanglement ≤ n * (E + delta)

/-- PDF p.3: unlimited Bell assistance; k and l have no rate restriction at all.
The classical cost still counts every message bit. -/
def ClassicalAchievable {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : TransferCode A C B n,
      P.HasRedistributionClassicalMessage ∧ P.redistributionError psi ≤ eps ∧ (P.q : ℝ) ≤ n * (c + delta)

/-- PDF p.3: the older merging cbit cost I(RA;C), with A placed in the reference. -/
def mergingClassicalCost {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.1)) (fun p => p.2.2) +
    subsystemEntropy (pureDensity psi) (fun p => p.2.2.1)
      (fun p => (p.1, p.2.1, p.2.2.2)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.1, p.2.2.1))
      (fun p => p.2.2.2)

/-! Sanity examples pinning the local definitions. -/

example {X : Type*} [Fintype X] (rho : Matrix X X ℂ) :
    redistributionMarginal rho id (fun _ => ()) = rho := by
  ext a b
  unfold redistributionMarginal
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

example {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R))
    (r : Copies R 0) (a : Copies A 0) (c : Copies C 0) (b : Copies B 0) :
    sourceAmplitude psi 0 r a c b = 1 := by
  simp [sourceAmplitude, tensorPow]

example {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) :
    swappedSource (swappedSource psi) = psi := by
  ext p
  rfl

example {A C B : Type*} [Fintype A] [Fintype C] [Fintype B]
    {n : ℕ} (P : TransferCode A C B n) (h : P.k = P.l) :
    P.netEntanglement = 0 := by
  simp [TransferCode.netEntanglement, h]

/-- PDF p.3, application (1): the actual four-qubit cat state, in R,A,C,B order. -/
def catState : EuclideanSpace ℂ (RedistributionSource Bool Bool Bool Bool) :=
  WithLp.toLp 2 fun p =>
    if p.1 = p.2.1 ∧ p.2.1 = p.2.2.1 ∧ p.2.2.1 = p.2.2.2
    then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.3: TP extension of Alice's support isometry. It applies CNOT A→C,
then traces out C. On |zz> only the false branch occurs, preserving coherence. -/
def catAliceKraus (work : Bool) : Matrix Bool (Bool × Bool) ℂ :=
  fun a p => if a = p.1 ∧ work = (p.1 != p.2) then 1 else 0

/-- PDF p.3: Alice's complete local operation on every operator. -/
def catAlice : Superop (Bool × Bool) Bool := krausApply catAliceKraus

/-- PDF p.3: Bob's genuine isometry |z>→|zz>, on the whole input space. -/
def catBobIsometry : Matrix (Bool × Bool) Bool ℂ :=
  fun p b => if p = (b, b) then 1 else 0

/-- PDF p.3: Bob's local CPTP operation. -/
def catBob : Superop Bool (Bool × Bool) := conjSuperop catBobIsometry

/-- PDF p.3: tensor product of two local operations, on arbitrary correlated inputs. -/
def localProduct {X Y U V : Type*} [Fintype X] [Fintype Y]
    (F : Superop X U) (G : Superop Y V) : Superop (X × Y) (U × V) :=
  fun rho p p' => ∑ x, ∑ x', ∑ y, ∑ y',
    rho (x, y) (x', y') * F (Matrix.single x x' 1) p.1 p'.1 *
      G (Matrix.single y y' 1) p.2 p'.2

/-- PDF p.3: input cat state, grouped into Alice's AC and Bob's B. -/
def catInput : Matrix (Bool × ((Bool × Bool) × Bool))
    (Bool × ((Bool × Bool) × Bool)) ℂ :=
  pureDensity (WithLp.toLp 2 fun p => catState (p.1, (p.2.1.1, (p.2.1.2, p.2.2))))

example (z : Bool) : catAliceKraus false z (z, z) = 1 := by
  cases z <;> rfl

example (z : Bool) : catAliceKraus true z (z, z) = 0 := by
  cases z <;> rfl

example (z : Bool) : catBobIsometry (z, z) z = 1 := by
  simp [catBobIsometry]

section Composite

variable {A C D B R : Type*}
variable [Fintype A] [Fintype C] [Fintype D] [Fintype B] [Fintype R]

/-- PDF p.2: transfer CD jointly, retaining A. -/
def jointSource (psi : EuclideanSpace ℂ (R × (A × (C × (D × B))))) :
    EuclideanSpace ℂ (RedistributionSource A (C × D) B R) :=
  WithLp.toLp 2 fun p => psi (p.1, (p.2.1, (p.2.2.1.1, (p.2.2.1.2, p.2.2.2))))

/-- PDF p.2: D first, with AC retained by the sender. -/
def firstSource (psi : EuclideanSpace ℂ (R × (A × (C × (D × B))))) :
    EuclideanSpace ℂ (RedistributionSource (A × C) D B R) :=
  WithLp.toLp 2 fun p => psi (p.1, (p.2.1.1, (p.2.1.2, p.2.2)))

/-- PDF p.3: C second, with DB already held by the receiver. -/
def secondSource (psi : EuclideanSpace ℂ (R × (A × (C × (D × B))))) :
    EuclideanSpace ℂ (RedistributionSource A C (D × B) R) := psi

/-- PDF pp.2–3: actual initial matrix for stage D. The future stage's Bell bank
is untouched, so it is placed together with R in this stage's reference. -/
def sequentialInitial {n : ℕ} (P : TransferCode (A × C) D B n)
    (T : TransferCode A C (D × B) n)
    (psi : EuclideanSpace ℂ (R × (A × (C × (D × B))))) :
    Matrix ((Copies R n × (Qubits T.k × Qubits T.k)) ×
      (((Copies (A × C) n × Copies D n) × Qubits P.k) ×
        (Copies B n × Qubits P.k)))
      ((Copies R n × (Qubits T.k × Qubits T.k)) ×
      (((Copies (A × C) n × Copies D n) × Qubits P.k) ×
        (Copies B n × Qubits P.k))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    tensorPow n psi (fun i => (p.1.1 i, ((p.2.1.1.1 i).1,
      ((p.2.1.1.1 i).2, (p.2.1.1.2 i, p.2.2.1 i))))) *
    maxEntangled P.k (p.2.1.2, p.2.2.2) * maxEntangled T.k p.1.2)

/-- PDF pp.2–3: stage D followed by stage C on the actual first-stage output.
The D-stage final Bell pairs become part of stage C's untouched reference. -/
def sequentialOutput {n : ℕ} (P : TransferCode (A × C) D B n)
    (T : TransferCode A C (D × B) n)
    (psi : EuclideanSpace ℂ (R × (A × (C × (D × B))))) :
    Matrix ((Copies R n × (Qubits P.l × Qubits P.l)) ×
      ((Copies A n × Qubits T.l) ×
        ((Copies C n × Copies (D × B) n) × Qubits T.l)))
      ((Copies R n × (Qubits P.l × Qubits P.l)) ×
      ((Copies A n × Qubits T.l) ×
        ((Copies C n × Copies (D × B) n) × Qubits T.l))) ℂ :=
  let afterD := idTensorSuperop (forwardApply P.encoder P.decoder)
    (sequentialInitial P T psi)
  let regroup : ((Copies R n × (Qubits P.l × Qubits P.l)) ×
      (((Copies A n × Copies C n) × Qubits T.k) ×
        (Copies (D × B) n × Qubits T.k))) →
      ((Copies R n × (Qubits T.k × Qubits T.k)) ×
      ((Copies (A × C) n × Qubits P.l) ×
        ((Copies D n × Copies B n) × Qubits P.l))) :=
    fun p => ((p.1.1, (p.2.1.2, p.2.2.2)),
      (((fun i => (p.2.1.1.1 i, p.2.1.1.2 i)), p.1.2.1),
        (((fun i => (p.2.2.1 i).1), (fun i => (p.2.2.1 i).2)), p.1.2.2)))
  idTensorSuperop (forwardApply T.encoder T.decoder) (fun p q => afterD (regroup p) (regroup q))

/-- PDF pp.2–3: joint target with both final Bell banks, including their absence
of correlations with the source and with each other. -/
def sequentialTarget {n : ℕ} (P : TransferCode (A × C) D B n)
    (T : TransferCode A C (D × B) n)
    (psi : EuclideanSpace ℂ (R × (A × (C × (D × B))))) :
    Matrix ((Copies R n × (Qubits P.l × Qubits P.l)) ×
      ((Copies A n × Qubits T.l) ×
        ((Copies C n × Copies (D × B) n) × Qubits T.l)))
      ((Copies R n × (Qubits P.l × Qubits P.l)) ×
      ((Copies A n × Qubits T.l) ×
        ((Copies C n × Copies (D × B) n) × Qubits T.l))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    tensorPow n psi (fun i => (p.1.1 i, (p.2.1.1 i,
      (p.2.2.1.1 i, p.2.2.1.2 i)))) *
    maxEntangled P.l p.1.2 * maxEntangled T.l (p.2.1.2, p.2.2.2))

/-- PDF pp.2–3: operational successive achievability with separate stage costs.
Initial Bell banks are supplied for both stages; neither stage is required to
have nonnegative net entanglement consumption. -/
def SuccessivelyAchievable
    (psi : EuclideanSpace ℂ (R × (A × (C × (D × B)))))
    (QD ED QC EC : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : TransferCode (A × C) D B n,
      ∃ T : TransferCode A C (D × B) n,
        P.redistributionError (firstSource psi) ≤ eps / 2 ∧
        T.redistributionError (secondSource psi) ≤ eps / 2 ∧
        traceNorm (sequentialOutput P T psi - sequentialTarget P T psi) ≤ eps ∧
        (P.q : ℝ) ≤ n * (QD + delta) ∧ P.netEntanglement ≤ n * (ED + delta) ∧
        (T.q : ℝ) ≤ n * (QC + delta) ∧ T.netEntanglement ≤ n * (EC + delta)

example (psi : EuclideanSpace ℂ (R × (A × (C × (D × B)))))
    (r : R) (a : A) (c : C) (d : D) (b : B) :
    firstSource psi (r, ((a,c), (d,b))) =
      jointSource psi (r, (a, ((c,d), b))) := by rfl

end Composite

/-! Coherent implementations: all work remains in the comparison. -/

/-- PDF p.2, Fig.2: finite local unitaries with explicit input and output work
registers. Rectangular matrices are two-sided inverses, so the corresponding
finite Hilbert spaces have equal dimensions. Work dimensions are arbitrary
positive integers, rather than just powers of two. -/
structure UnitaryRedistributionCode (A C B : Type*) [Fintype A] [Fintype C] [Fintype B] (n : ℕ) where
  q : ℕ
  k : ℕ
  l : ℕ
  waIn : ℕ
  waOut : ℕ
  wbIn : ℕ
  wbOut : ℕ
  encoder : Matrix (((Copies A n × Qubits l) × Fin (waOut + 1)) × Qubits q)
    (((Copies A n × Copies C n) × Qubits k) × Fin (waIn + 1)) ℂ
  decoder : Matrix (((Copies C n × Copies B n) × Qubits l) × Fin (wbOut + 1))
    (Qubits q × ((Copies B n × Qubits k) × Fin (wbIn + 1))) ℂ
  encoder_left : encoderᴴ * encoder = 1
  encoder_right : encoder * encoderᴴ = 1
  decoder_left : decoderᴴ * decoder = 1
  decoder_right : decoder * decoderᴴ = 1

namespace UnitaryRedistributionCode

variable {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
variable {n : ℕ} (P : UnitaryRedistributionCode A C B n)

/-- PDF p.2: full coherent input basis, including both pure local work registers. -/
abbrev Input := Copies R n ×
  ((((Copies A n × Copies C n) × Qubits P.k) × Fin (P.waIn + 1)) ×
    ((Copies B n × Qubits P.k) × Fin (P.wbIn + 1)))

/-- PDF p.2: full output basis. No work is discarded in this model. -/
abbrev RedistributionOutputBasis := Copies R n ×
  (((Copies A n × Qubits P.l) × Fin (P.waOut + 1)) ×
    (((Copies C n × Copies B n) × Qubits P.l) × Fin (P.wbOut + 1)))

/-- PDF p.2, Fig.2: the actual global unitary, including transmission and id_R.
Its adjoint reverses Bob's decoder first, transmits the same message back, then
reverses Alice's encoder. -/
def globalMatrix : Matrix (P.RedistributionOutputBasis (R := R)) (P.Input (R := R)) ℂ :=
  fun o i => if o.1 = i.1 then
    ∑ m, P.encoder (o.2.1, m) i.2.1 * P.decoder o.2.2 (m, i.2.2)
    else 0

/-- PDF p.2: independent pure local ancillas in fixed basis states, and k ebits. -/
def redistributionInputVector (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) :
    EuclideanSpace ℂ (P.Input (R := R)) :=
  WithLp.toLp 2 fun p =>
    if p.2.1.2 = 0 ∧ p.2.2.2 = 0 then
      sourceAmplitude psi n p.1 p.2.1.1.1.1 p.2.1.1.1.2 p.2.2.1.1 *
        maxEntangled P.k (p.2.1.1.2, p.2.2.1.2)
    else 0

/-- PDF p.2: pure target with l independent ebits and fixed pure output work.
These work registers become the initial local ancillas in the reverse process. -/
def redistributionTargetVector (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) :
    EuclideanSpace ℂ (P.RedistributionOutputBasis (R := R)) :=
  WithLp.toLp 2 fun p =>
    if p.2.1.2 = 0 ∧ p.2.2.2 = 0 then
      sourceAmplitude psi n p.1 p.2.1.1.1 p.2.2.1.1.1 p.2.2.1.1.2 *
        maxEntangled P.l (p.2.1.1.2, p.2.2.1.2)
    else 0

/-- PDF p.2: full pure-state reconstruction error before tracing any work. -/
def forwardError (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  traceNorm (pureDensity (rectAct P.globalMatrix (P.redistributionInputVector psi)) -
    pureDensity (P.redistributionTargetVector psi))

/-- PDF p.2: error of reversing these same matrices with Bell banks exchanged. -/
def reverseError (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) : ℝ :=
  traceNorm (pureDensity (rectAct P.globalMatrixᴴ (P.redistributionTargetVector psi)) -
    pureDensity (P.redistributionInputVector psi))

end UnitaryRedistributionCode

/-- PDF p.2: one coherent family works in both directions. Both signed ebit
bounds are imposed so that reversal achieves -E, including E=0. -/
def ReversiblyAchievable {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (Q E : ℝ) : Prop :=
  0 ≤ Q ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n ≥ N, 1 ≤ n → ∃ P : UnitaryRedistributionCode A C B n,
      P.forwardError psi ≤ eps ∧ P.reverseError psi ≤ eps ∧
      (P.q : ℝ) ≤ n * (Q + delta) ∧
      (P.k : ℝ) - P.l ≤ n * (E + delta) ∧
      (P.l : ℝ) - P.k ≤ n * (-E + delta)

example {X : Type*} [Fintype X] (v : EuclideanSpace ℂ X) :
    rectAct (1 : Matrix X X ℂ) v = v := by
  ext x
  simp [rectAct, Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- PDF p.4: six-register source R,A,C_A,B,C_B,C, with C initially at Charlie. -/
abbrev ThreeSource (A CA B CB C R : Type*) := R × (A × (CA × (B × (CB × C))))

/-- PDF p.4: two encoders, two separately charged forward messages, one receiver.
With no feedback, the receiver may postpone all its actions until both messages
arrive. The Bell banks belong to the Alice–Charlie and Bob–Charlie links. -/
structure ThreeCode (A CA B CB C : Type*)
    [Fintype A] [Fintype CA] [Fintype B] [Fintype CB] [Fintype C] (n : ℕ) where
  qa : ℕ
  qb : ℕ
  ka : ℕ
  kb : ℕ
  la : ℕ
  lb : ℕ
  alice : Superop ((Copies A n × Copies CA n) × Qubits ka)
    ((Copies A n × Qubits la) × Qubits qa)
  bob : Superop ((Copies B n × Copies CB n) × Qubits kb)
    ((Copies B n × Qubits lb) × Qubits qb)
  charlie : Superop (Qubits qa × (Qubits qb × (Copies C n × (Qubits ka × Qubits kb))))
    (((Copies CA n × Copies CB n) × Copies C n) × (Qubits la × Qubits lb))
  alice_channel : IsChannel alice
  bob_channel : IsChannel bob
  charlie_channel : IsChannel charlie

/-- PDF p.4: the actual all-operator joint action of the two local senders and
Charlie. Both transmitted message coherences are contracted, never discarded. -/
def threeForwardApply {X Y Z U V W M N : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype M] [Fintype N]
    (F : Superop X (U × M)) (G : Superop Y (V × N))
    (D : Superop (M × (N × Z)) W) : Superop (X × (Y × Z)) (U × (V × W)) :=
  fun rho p p' => ∑ x, ∑ x', ∑ y, ∑ y', ∑ z, ∑ z', ∑ m, ∑ m', ∑ t, ∑ t',
    rho (x, (y, z)) (x', (y', z')) *
    F (Matrix.single x x' 1) (p.1, m) (p'.1, m') *
    G (Matrix.single y y' 1) (p.2.1, t) (p'.2.1, t') *
    D (Matrix.single (m, (t, z)) (m', (t', z')) 1) p.2.2 p'.2.2

namespace ThreeCode

variable {A CA B CB C R : Type*}
variable [Fintype A] [Fintype CA] [Fintype B] [Fintype CB] [Fintype C] [Fintype R]
variable {n : ℕ} (P : ThreeCode A CA B CB C n)

/-- PDF p.4: source times the two independent initial Bell banks. -/
def initial (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) :
    Matrix (Copies R n ×
      (((Copies A n × Copies CA n) × Qubits P.ka) ×
        (((Copies B n × Copies CB n) × Qubits P.kb) ×
          (Copies C n × (Qubits P.ka × Qubits P.kb)))))
      (Copies R n ×
      (((Copies A n × Copies CA n) × Qubits P.ka) ×
        (((Copies B n × Copies CB n) × Qubits P.kb) ×
          (Copies C n × (Qubits P.ka × Qubits P.kb))))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    tensorPow n psi (fun i => (p.1 i, (p.2.1.1.1 i, (p.2.1.1.2 i,
      (p.2.2.1.1.1 i, (p.2.2.1.1.2 i, p.2.2.2.1 i)))))) *
    maxEntangled P.ka (p.2.1.2, p.2.2.2.2.1) *
    maxEntangled P.kb (p.2.2.1.2, p.2.2.2.2.2))

/-- PDF p.4: desired full state including both independent final Bell banks. -/
def redistributionTargetDensity (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) :
    Matrix (Copies R n × ((Copies A n × Qubits P.la) ×
      ((Copies B n × Qubits P.lb) ×
        (((Copies CA n × Copies CB n) × Copies C n) × (Qubits P.la × Qubits P.lb)))))
      (Copies R n × ((Copies A n × Qubits P.la) ×
      ((Copies B n × Qubits P.lb) ×
        (((Copies CA n × Copies CB n) × Copies C n) × (Qubits P.la × Qubits P.lb))))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    tensorPow n psi (fun i => (p.1 i, (p.2.1.1 i, (p.2.2.2.1.1.1 i,
      (p.2.2.1.1 i, (p.2.2.2.1.1.2 i, p.2.2.2.1.2 i)))))) *
    maxEntangled P.la (p.2.1.2, p.2.2.2.2.1) *
    maxEntangled P.lb (p.2.2.1.2, p.2.2.2.2.2))

/-- PDF p.4: full joint error of the actual finite three-party code. -/
def redistributionError (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) : ℝ :=
  traceNorm (idTensorSuperop (threeForwardApply P.alice P.bob P.charlie)
    (P.initial psi) - P.redistributionTargetDensity psi)

end ThreeCode

/-- PDF p.4: four operational rates with independent Bell accounting per link.
The definition does not mention an entropic region or an ordering strategy. -/
def ThreePartyAchievable {A CA B CB C R : Type*}
    [Fintype A] [Fintype CA] [Fintype B] [Fintype CB] [Fintype C] [Fintype R]
    (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) (rates : Fin 4 → ℝ) : Prop :=
  0 ≤ rates 0 ∧ 0 ≤ rates 1 ∧
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
      ∀ n ≥ N, 1 ≤ n → ∃ P : ThreeCode A CA B CB C n,
        P.redistributionError psi ≤ eps ∧
        (P.qa : ℝ) ≤ n * (rates 0 + delta) ∧
        (P.qb : ℝ) ≤ n * (rates 1 + delta) ∧
        (P.ka : ℝ) - P.la ≤ n * (rates 2 + delta) ∧
        (P.kb : ℝ) - P.lb ≤ n * (rates 3 + delta)

section ThreePartyCorners

variable {A CA B CB C R : Type*}
variable [Fintype A] [Fintype CA] [Fintype B] [Fintype CB] [Fintype C] [Fintype R]

/-- PDF p.4: Alice first. Bob's entire B C_B is inaccessible reference here. -/
def aliceFirst (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) :
    EuclideanSpace ℂ (RedistributionSource A CA C (R × (B × CB))) :=
  WithLp.toLp 2 fun p => psi (p.1.1,
    (p.2.1, (p.2.2.1, (p.1.2.1, (p.1.2.2, p.2.2.2)))))

/-- PDF p.4: Bob second, with C_A C held by Charlie; A is reference. -/
def bobSecond (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) :
    EuclideanSpace ℂ (RedistributionSource B CB (CA × C) (R × A)) :=
  WithLp.toLp 2 fun p => psi (p.1.1,
    (p.1.2, (p.2.2.2.1, (p.2.1, (p.2.2.1, p.2.2.2.2)))))

/-- PDF p.4: Bob first; A C_A is in this stage's reference. -/
def bobFirst (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) :
    EuclideanSpace ℂ (RedistributionSource B CB C (R × (A × CA))) :=
  WithLp.toLp 2 fun p => psi (p.1.1,
    (p.1.2.1, (p.1.2.2, (p.2.1, (p.2.2.1, p.2.2.2)))))

/-- PDF p.4: Alice second, with C_B C held by Charlie; B is reference. -/
def aliceSecond (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) :
    EuclideanSpace ℂ (RedistributionSource A CA (CB × C) (R × B)) :=
  WithLp.toLp 2 fun p => psi (p.1.1,
    (p.2.1, (p.2.2.1, (p.1.2, p.2.2.2))))

/-- PDF p.4: corner obtained by Alice-to-Charlie, then Bob-to-Charlie. -/
def aliceFirstCorner (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) : Fin 4 → ℝ :=
  ![quantumCost (aliceFirst psi), quantumCost (bobSecond psi),
    redistributionEntanglementRate (aliceFirst psi), redistributionEntanglementRate (bobSecond psi)]

/-- PDF p.4: corner obtained in the opposite order, with the same link order. -/
def bobFirstCorner (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R)) : Fin 4 → ℝ :=
  ![quantumCost (aliceSecond psi), quantumCost (bobFirst psi),
    redistributionEntanglementRate (aliceSecond psi), redistributionEntanglementRate (bobFirst psi)]

/-- PDF p.4: convex time sharing of the two corners, plus the wasting and
qubit-for-ebit substitution cone on each link. This is an inner region only. -/
def InGeneratedRegion (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R))
    (rates : Fin 4 → ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∃ d : Fin 4 → ℝ,
    0 ≤ d 0 ∧ 0 ≤ d 1 ∧ 0 ≤ d 0 + d 2 ∧ 0 ≤ d 1 + d 3 ∧
    ∀ i, rates i = t * aliceFirstCorner psi i + (1 - t) * bobFirstCorner psi i + d i

example (psi : EuclideanSpace ℂ (ThreeSource A CA B CB C R))
    (r : R) (a : A) (ca : CA) (b : B) (cb : CB) (c : C) :
    aliceFirst psi ((r,(b,cb)),(a,(ca,c))) =
      bobSecond psi ((r,a),(b,(cb,(ca,c)))) := by rfl

end ThreePartyCorners

end QAlgorithms.Papers.Independent.Gap48.P20


