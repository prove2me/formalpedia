-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P74
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T10:03:53.268934+00:00
-- url     : https://prove2.me/theorems/a563367a-7623-418b-97a7-0ace02b74c77
-- title:
--   Definitions for Polar codes for private classical communication
-- statement:
--   The objects the formalized statements of *Polar codes for private classical communication* (arXiv:1203.5794) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `WiretapData`: PDF p.2: fixed isometric extension (output B,E,S2) and input purifications on A'S1.
--   - `WiretapData.Valid`: PDF p.2: isometry and normalized purifications; tracing S2 defines the same wiretap map.
--   - `purifiedWiretapSignal`: PDF p.2, Eq.(2): purified output in order B,E,S1,S2.
--   - `bobMap`: PDF p.2: Bob's marginal of the channel fixed by V, on all operators.
--   - `eveMap`: PDF pp.2,5: Eve's marginal traces B and S2, excluding both shields.
--   - `amplitudeBob`: PDF p.2, Eq.(1): amplitude cq channel to Bob.
--   - `amplitudeEve`: PDF p.2, Eq.(8): amplitude cq channel to Eve.
--   - `bitSign`: The phase (-1)^b.
--   - `phaseVector`: PDF p.2, Eq.(6): normalized phase pure output, C first and Eve last.
--   - `phaseBob`: PDF p.2, Eq.(5): virtual phase output C,B,S1,S2; only E is traced out.
--   - `uniformHolevo`: PDF p.1: Holevo information in bits for equiprobable finite labels. Uses below have nonempty labels and normalized states by the physical construction.
--   - `symmetricPrivateInformation`: PDF p.4: fixed-ensemble symmetric private information; signed, with no optimization.
--   - `polarEntry`: PDF p.3: Arikan G_N=B_N F^(tensor n), F=[[1,0],[1,1]]. Index digits are least significant first; B_N reverses the row's n digits.
--   - `polarEncode`: PDF pp.3–4: row multiplication by G_N (false) or G_N^T (true), over F_2.
--   - `dotParity`: PDF p.3: the binary inner product used in the phase exponent.
--   - `polarSideIndices`: PDF pp.3–4: previous amplitude bits or future phase bits as side information.
--   - `splitOutput`: PDF pp.3–4, Eqs.(10)–(11): the other N-1 bits are uniform, the polarSideIndices bits are revealed classically, and the opposite side is averaged. Phase uses G_N^T.
--   - `goodIndices`: PDF p.3, Eq.(12): strictly less than threshold, applied to ROOT fidelity.
--   - `decodedIndices`: PDF p.4: A union X, exactly the amplitude-good indices.
--   - `phaseGoodIndices`: PDF p.4: phase-good indices of the virtual channel with both shields.
--   - `privateIndices`: PDF p.4: A, good in both amplitude and phase.
--   - `keyIndices`: PDF p.4: Bbad, bad in both variables.
--   - `randomIndices`: PDF p.4: X, independent uniform local random bits.
--   - `frozenIndices`: PDF p.4: Z, uniform frozen bits shared with Bob.
--   - `netRate`: PDF p.4: signed net rate; cast both cardinalities before subtracting.
--   - `keyRate`: PDF pp.5–7: consumed secret-key bits per channel use.
--   - `encodedPhaseVector`: PDF p.3: the displayed coherent output, with exponent x dot z and purifiedWiretapSignal z G_N. Output order is (C,B,S1,S2)^N followed by E^N.
--   - `encodedPhaseOutput`: PDF p.3: trace only Eve from the displayed coherent output.
--   - `referenceEncoder`: PDF p.3: the extra polar encoder U_E on C^N, identity on B^N S1^N S2^N.
--   - `actualPhaseSplit`: PDF p.4: split the actual phase output, revealing future bits, averaging past bits.
--   - `PolarDecoderEffects`: PDF p.4: POVMs depend on the known frozen/key bits; outcomes contain all A union X. No measurement depends on the unknown private or randomized bits.
--   - `IsSuccessiveCancellation`: PDF pp.3–4: a successive cancellation decoder performs a binary projective test for each index in A union X, in increasing order; a test uses the previous decisions and the known frozen/key bits, and frozen indices require no measurement. Outcomes are the sequential effects K^dagger K, not an unconstrained family of message-dependent POVMs.
--   - `decoderError`: PDF pp.3–4: average error over the independent uniform bits in A,X,Z,Bbad.
--   - `reliabilityBound`: PDF p.4: sqrt(2 times the sum of ROOT fidelities), exactly the printed radical.
--   - `decayHalf`: PDF p.4: 2^(-N^beta/2), where N=2^n.
--   - `privateMessageEveState`: PDF p.4: actual conditional Eve state for a uniform private message. Average X,Z,Bbad independently; the real normalization 2^|A|/2^N avoids truncated natural subtraction.
--   - `privateMessageLeakageBits`: PDF p.4, Theorem 2: unconditional uniform-message Holevo leakage I(U_A;E^N), in bits.
--   - `EveDegradable`: PDF p.5: Bob simulates Eve E, not the larger complementary register E S2.
--   - `classicalEmbedding`: PDF p.6, Appendix A, Eq.(14): measure the input basis then prepare the classical joint output; every off-diagonal input entry is discarded.
--   - `classicalKraus`: PDF p.6, Appendix A: Kraus operator sqrt(p(y,z|x)) |y,z><x|.
--   - `classicalDilation`: PDF p.6, Appendix A: the explicit dilation stores (x,y,z) in S2. The physical output is only (y,z); S2 is not appended to Eve.
--   - `bscProbability`: PDF p.7, Appendix C.A: BSC transition probability; inequality of bits is XOR.
--   - `bscOutput`: PDF p.7: computational-basis output states of a BSC.
--   - `independentBsc`: PDF p.7, Eq.(17): independent BSC outputs conditioned on the same input bit.
--   - `erasureData`: PDF pp.9–10: erasure dilation |a> -> sqrt(1-eps)|a,e>+sqrt(eps)|e,a>. Both shields are trivial, and symbol 2 is the orthogonal erasure flag.
--   - `dampingMap`: PDF p.10: the accepted qubit amplitude-damping channel with loss probability 1-eta. Its Kraus labels are reversed relative to the source; the summed channel is the same.
--   - `dampingAmplitude`: PDF p.10: the actual amplitude-channel output for a computational-basis input.
--   - `binaryPhaseBellVector`: PDF p.10: phase-modulated Bell vector with reference C first and Bob's input second.
--   - `dampingPhaseOutput`: PDF pp.10–11: apply the same amplitude-damping channel to half of the Bell state.
--   - `cbIndex`: Computational order |00>, |01>, |10>, |11>, C first.
--   - `dampingPhaseMatrix`: PDF p.11: the exact displayed matrix, including loss at |10><10|.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, https://arxiv.org/abs/1203.5794v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Independent2_P01

/-! Wilde–Renes, arXiv:1203.5794v1. All registers are finite dimensional. The virtual
phase receiver retains both shields. Index i denotes the source's i+1. No theorem is
registered for the three source-ambiguous nodes in HARD.md.
The accepted product channel is used at length 2^n. Accepted damping uses loss
probability 1-eta; its Kraus labels are the reverse of the source labels. -/

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms
open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF p.2: fixed isometric extension (output B,E,S2) and input purifications on A'S1. -/
structure WiretapData (B E S1 S2 : Type) where
  V : Matrix (B × E × S2) Bool ℂ
  psi : Bool → EuclideanSpace ℂ (Bool × S1)

variable {B E S1 S2 : Type}
variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]
variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF p.2: isometry and normalized purifications; tracing S2 defines the same wiretap map. -/
def WiretapData.Valid (d : WiretapData B E S1 S2) : Prop :=
  d.Vᴴ * d.V = 1 ∧ ∀ z, ‖d.psi z‖ = 1

/-- PDF p.2, Eq.(2): purified output in order B,E,S1,S2. -/
def purifiedWiretapSignal (d : WiretapData B E S1 S2) (z : Bool) :
    EuclideanSpace ℂ (B × E × S1 × S2) :=
  WithLp.toLp 2 fun o => ∑ a : Bool, d.V (o.1, o.2.1, o.2.2.2) a * d.psi z (a, o.2.2.1)

/-- PDF p.2: Bob's marginal of the channel fixed by V, on all operators. -/
def bobMap (d : WiretapData B E S1 S2) : Superop Bool B :=
  fun rho => traceRight (d.V * rho * d.Vᴴ)

/-- PDF pp.2,5: Eve's marginal traces B and S2, excluding both shields. -/
def eveMap (d : WiretapData B E S1 S2) : Superop Bool E :=
  fun rho => Matrix.of fun e f => ∑ b : B, ∑ s : S2,
    (d.V * rho * d.Vᴴ) (b, e, s) (b, f, s)

/-- PDF p.2, Eq.(1): amplitude cq channel to Bob. -/
def amplitudeBob (d : WiretapData B E S1 S2) (z : Bool) :=
  bobMap d (traceRight (pureDensity (d.psi z)))

/-- PDF p.2, Eq.(8): amplitude cq channel to Eve. -/
def amplitudeEve (d : WiretapData B E S1 S2) (z : Bool) :=
  eveMap d (traceRight (pureDensity (d.psi z)))

/-- The phase (-1)^b. -/
def bitSign (b : Bool) : ℂ := if b then -1 else 1

/-- PDF p.2, Eq.(6): normalized phase pure output, C first and Eve last. -/
def phaseVector (d : WiretapData B E S1 S2) (x : Bool) :
    EuclideanSpace ℂ ((Bool × B × S1 × S2) × E) :=
  WithLp.toLp 2 fun o => (Real.sqrt 2 : ℂ)⁻¹ * bitSign (x && o.1.1) *
    purifiedWiretapSignal d o.1.1 (o.1.2.1, o.2, o.1.2.2.1, o.1.2.2.2)

/-- PDF p.2, Eq.(5): virtual phase output C,B,S1,S2; only E is traced out. -/
def phaseBob (d : WiretapData B E S1 S2) (x : Bool) :=
  traceRight (pureDensity (phaseVector d x))

/-- PDF p.1: Holevo information in bits for equiprobable finite labels.
Uses below have nonempty labels and normalized states by the physical construction. -/
def uniformHolevo {L O : Type} [Fintype L] [Fintype O] [DecidableEq O]
    (W : L → Matrix O O ℂ) : ℝ :=
  vnEntropy ((Fintype.card L : ℂ)⁻¹ • ∑ l, W l) -
    (Fintype.card L : ℝ)⁻¹ * ∑ l, vnEntropy (W l)

/-- PDF p.4: fixed-ensemble symmetric private information; signed, with no optimization. -/
def symmetricPrivateInformation (d : WiretapData B E S1 S2) : ℝ :=
  uniformHolevo (amplitudeBob d) - uniformHolevo (amplitudeEve d)

/-- PDF p.3: Arikan G_N=B_N F^(tensor n), F=[[1,0],[1,1]].
Index digits are least significant first; B_N reverses the row's n digits. -/
def polarEntry (n : ℕ) (i j : Fin (2 ^ n)) : Bool :=
  decide (∀ k : Fin n, Nat.testBit j.val k.val = true →
    Nat.testBit i.val (n - 1 - k.val) = true)

/-- PDF pp.3–4: row multiplication by G_N (false) or G_N^T (true), over F_2. -/
def polarEncode (n : ℕ) (reverse : Bool) (u : Qubits (2 ^ n)) : Qubits (2 ^ n) :=
  fun j => decide ((∑ i : Fin (2 ^ n), (u i).toNat *
    (if reverse then polarEntry n j i else polarEntry n i j).toNat) % 2 = 1)

/-- PDF p.3: the binary inner product used in the phase exponent. -/
def dotParity {n : ℕ} (x z : Qubits (2 ^ n)) : Bool :=
  decide ((∑ i, (x i).toNat * (z i).toNat) % 2 = 1)

/-- PDF pp.3–4: previous amplitude bits or future phase bits as side information. -/
abbrev polarSideIndices (n : ℕ) (reverse : Bool) (i : Fin (2 ^ n)) :=
  {j : Fin (2 ^ n) // if reverse then i.val < j.val else j.val < i.val}

/-- PDF pp.3–4, Eqs.(10)–(11): the other N-1 bits are uniform, the polarSideIndices bits are
revealed classically, and the opposite side is averaged. Phase uses G_N^T. -/
def splitOutput {O : Type} [Fintype O] [DecidableEq O] (n : ℕ) (reverse : Bool)
    (W : Bool → Matrix O O ℂ) (i : Fin (2 ^ n)) (b : Bool) :
    Matrix ((polarSideIndices n reverse i → Bool) × (Fin (2 ^ n) → O))
      ((polarSideIndices n reverse i → Bool) × (Fin (2 ^ n) → O)) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then
    (((2 : ℝ) ^ (2 ^ n - 1))⁻¹ : ℂ) *
      ∑ u ∈ Finset.univ.filter (fun u : Qubits (2 ^ n) => u i = b ∧
        ∀ j : polarSideIndices n reverse i, u j.val = p.1 j),
        QAlgorithms.Papers.Independent.Information100.P56.productOutput (2 ^ n) W (polarEncode n reverse u) p.2 q.2
    else 0

/-- PDF p.3, Eq.(12): strictly less than threshold, applied to ROOT fidelity. -/
def goodIndices {O : Type} [Fintype O] [DecidableEq O] (n : ℕ) (reverse : Bool)
    (W : Bool → Matrix O O ℂ) (beta : ℝ) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter fun i =>
    rootFidelity (splitOutput n reverse W i false) (splitOutput n reverse W i true) <
      Real.rpow 2 (-Real.rpow ((2 : ℝ) ^ n) beta)

/-- PDF p.4: A union X, exactly the amplitude-good indices. -/
def decodedIndices (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) :=
  goodIndices n false (amplitudeBob d) beta

/-- PDF p.4: phase-good indices of the virtual channel with both shields. -/
def phaseGoodIndices (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) :=
  goodIndices n true (phaseBob d) beta

/-- PDF p.4: A, good in both amplitude and phase. -/
def privateIndices (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) :=
  decodedIndices d beta n ∩ phaseGoodIndices d beta n

/-- PDF p.4: Bbad, bad in both variables. -/
def keyIndices (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) :=
  Finset.univ \ (decodedIndices d beta n ∪ phaseGoodIndices d beta n)

/-- PDF p.4: X, independent uniform local random bits. -/
def randomIndices (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) :=
  decodedIndices d beta n \ phaseGoodIndices d beta n

/-- PDF p.4: Z, uniform frozen bits shared with Bob. -/
def frozenIndices (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) :=
  phaseGoodIndices d beta n \ decodedIndices d beta n

/-- PDF p.4: signed net rate; cast both cardinalities before subtracting. -/
def netRate (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) : ℝ :=
  (((privateIndices d beta n).card : ℝ) - ((keyIndices d beta n).card : ℝ)) / (2 : ℝ) ^ n

/-- PDF pp.5–7: consumed secret-key bits per channel use. -/
def keyRate (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) : ℝ :=
  (keyIndices d beta n).card / (2 : ℝ) ^ n

/-- PDF p.3: the displayed coherent output, with exponent x dot z and purifiedWiretapSignal z G_N.
Output order is (C,B,S1,S2)^N followed by E^N. -/
def encodedPhaseVector (d : WiretapData B E S1 S2) (n : ℕ) (x : Qubits (2 ^ n)) :
    EuclideanSpace ℂ ((Fin (2 ^ n) → Bool × B × S1 × S2) × (Fin (2 ^ n) → E)) :=
  WithLp.toLp 2 fun p =>
    let z : Qubits (2 ^ n) := fun i => (p.1 i).1
    (Real.sqrt ((2 : ℝ) ^ (2 ^ n)) : ℂ)⁻¹ * bitSign (dotParity x z) *
      ∏ i, purifiedWiretapSignal d (polarEncode n false z i)
        ((p.1 i).2.1, p.2 i, (p.1 i).2.2.1, (p.1 i).2.2.2)

/-- PDF p.3: trace only Eve from the displayed coherent output. -/
def encodedPhaseOutput (d : WiretapData B E S1 S2) (n : ℕ) (x : Qubits (2 ^ n)) :=
  traceRight (pureDensity (encodedPhaseVector d n x))

/-- PDF p.3: the extra polar encoder U_E on C^N, identity on B^N S1^N S2^N. -/
def referenceEncoder (d : WiretapData B E S1 S2) (n : ℕ) :
    Matrix (Fin (2 ^ n) → Bool × B × S1 × S2)
      (Fin (2 ^ n) → Bool × B × S1 × S2) ℂ :=
  Matrix.of fun y z => if (∀ i, (y i).2 = (z i).2) ∧
    (fun i => (y i).1) = polarEncode n false (fun i => (z i).1) then 1 else 0

/-- PDF p.4: split the actual phase output, revealing future bits, averaging past bits. -/
def actualPhaseSplit (d : WiretapData B E S1 S2) (n : ℕ) (i : Fin (2 ^ n)) (b : Bool) :=
  Matrix.of fun p q : (polarSideIndices n true i → Bool) ×
      (Fin (2 ^ n) → Bool × B × S1 × S2) =>
    if p.1 = q.1 then (((2 : ℝ) ^ (2 ^ n - 1))⁻¹ : ℂ) *
      ∑ x ∈ Finset.univ.filter (fun x : Qubits (2 ^ n) => x i = b ∧
        ∀ j : polarSideIndices n true i, x j.val = p.1 j), encodedPhaseOutput d n x p.2 q.2
    else 0

/-- PDF p.4: POVMs depend on the known frozen/key bits; outcomes contain all A union X.
No measurement depends on the unknown private or randomized bits. -/
abbrev PolarDecoderEffects (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) :=
  ({i : Fin (2 ^ n) // i ∉ decodedIndices d beta n} → Bool) →
  ({i : Fin (2 ^ n) // i ∈ decodedIndices d beta n} → Bool) →
  Matrix (Fin (2 ^ n) → B) (Fin (2 ^ n) → B) ℂ

/-- PDF pp.3–4: a successive cancellation decoder performs a binary projective test
for each index in A union X, in increasing order; a test uses the previous decisions and
the known frozen/key bits, and frozen indices require no measurement. Outcomes are the
sequential effects K^dagger K, not an unconstrained family of message-dependent POVMs. -/
def IsSuccessiveCancellation (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ)
    (M : PolarDecoderEffects d beta n) : Prop :=
  ∃ T : ({i : Fin (2 ^ n) // i ∉ decodedIndices d beta n} → Bool) →
      (i : Fin (2 ^ n)) → (polarSideIndices n false i → Bool) →
        Matrix (Fin (2 ^ n) → B) (Fin (2 ^ n) → B) ℂ,
    (∀ k i v, IsEffect (T k i v) ∧ T k i v * T k i v = T k i v) ∧
    ∀ k m,
      let u : Qubits (2 ^ n) := fun i => if h : i ∈ decodedIndices d beta n then m ⟨i, h⟩
        else k ⟨i, h⟩
      let steps := List.ofFn (fun i : Fin (2 ^ n) =>
        if i ∈ decodedIndices d beta n then
          let P := T k i (fun j => u j.val)
          if u i then 1 - P else P
        else 1)
      let K := steps.foldl (fun K P => P * K) 1
      M k m = Kᴴ * K

/-- PDF pp.3–4: average error over the independent uniform bits in A,X,Z,Bbad. -/
def decoderError (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ)
    (M : PolarDecoderEffects d beta n) : ℝ :=
  ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ u : Qubits (2 ^ n),
    (1 - effectProb (M (fun i => u i.val) (fun i => u i.val))
      (QAlgorithms.Papers.Independent.Information100.P56.productOutput (2 ^ n) (amplitudeBob d) (polarEncode n false u)))

/-- PDF p.4: sqrt(2 times the sum of ROOT fidelities), exactly the printed radical. -/
def reliabilityBound (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * ∑ i ∈ decodedIndices d beta n,
    rootFidelity (splitOutput n false (amplitudeBob d) i false)
      (splitOutput n false (amplitudeBob d) i true))

/-- PDF p.4: 2^(-N^beta/2), where N=2^n. -/
def decayHalf (beta : ℝ) (n : ℕ) : ℝ :=
  Real.rpow 2 (-Real.rpow ((2 : ℝ) ^ n) beta / 2)

/-- PDF p.4: actual conditional Eve state for a uniform private message. Average X,Z,Bbad
independently; the real normalization 2^|A|/2^N avoids truncated natural subtraction. -/
def privateMessageEveState (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ)
    (m : {i : Fin (2 ^ n) // i ∈ privateIndices d beta n} → Bool) :
    Matrix (Fin (2 ^ n) → E) (Fin (2 ^ n) → E) ℂ :=
  (((2 : ℝ) ^ (privateIndices d beta n).card / (2 : ℝ) ^ (2 ^ n) : ℝ) : ℂ) •
    ∑ u ∈ Finset.univ.filter (fun u : Qubits (2 ^ n) =>
      ∀ i : {i : Fin (2 ^ n) // i ∈ privateIndices d beta n}, u i.val = m i),
      QAlgorithms.Papers.Independent.Information100.P56.productOutput (2 ^ n) (amplitudeEve d) (polarEncode n false u)

/-- PDF p.4, Theorem 2: unconditional uniform-message Holevo leakage I(U_A;E^N), in bits. -/
def privateMessageLeakageBits (d : WiretapData B E S1 S2) (beta : ℝ) (n : ℕ) : ℝ :=
  uniformHolevo (privateMessageEveState d beta n)

/-- PDF p.5: Bob simulates Eve E, not the larger complementary register E S2. -/
def EveDegradable (d : WiretapData B E S1 S2) : Prop :=
  ∃ D : Superop B E, IsChannel D ∧ ∀ rho, D (bobMap d rho) = eveMap d rho

/-- Sanity: phase signs. -/
example : bitSign false = 1 ∧ bitSign true = -1 := by
  simp [bitSign]

/-- Sanity: G_1 is the identity entry. -/
example : polarEntry 0 0 0 = true := by
  simp [polarEntry]

/-- PDF p.6, Appendix A, Eq.(14): measure the input basis then prepare the classical
joint output; every off-diagonal input entry is discarded. -/
def classicalEmbedding {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (p : X → Y → Z → ℝ) : Superop X (Y × Z) :=
  fun rho => Matrix.of fun a b => if a = b then
    ∑ x, rho x x * (p x a.1 a.2 : ℂ) else 0

/-- PDF p.6, Appendix A: Kraus operator sqrt(p(y,z|x)) |y,z><x|. -/
def classicalKraus {X Y Z : Type} (p : X → Y → Z → ℝ)
    (s : X × Y × Z) : Matrix (Y × Z) X ℂ :=
  Matrix.of fun o a => if o = (s.2.1, s.2.2) ∧ a = s.1 then
    (Real.sqrt (p s.1 s.2.1 s.2.2) : ℂ) else 0

/-- PDF p.6, Appendix A: the explicit dilation stores (x,y,z) in S2.
The physical output is only (y,z); S2 is not appended to Eve. -/
def classicalDilation {X Y Z : Type} (p : X → Y → Z → ℝ) :
    Matrix ((Y × Z) × (X × Y × Z)) X ℂ :=
  Matrix.of fun o a => if o.1 = (o.2.2.1, o.2.2.2) ∧ a = o.2.1 then
    (Real.sqrt (p o.2.1 o.2.2.1 o.2.2.2) : ℂ) else 0

/-- PDF p.7, Appendix C.A: BSC transition probability; inequality of bits is XOR. -/
def bscProbability (p : ℝ) (x y : Bool) : ℝ := if x = y then 1 - p else p

/-- PDF p.7: computational-basis output states of a BSC. -/
def bscOutput (p : ℝ) (x : Bool) : Matrix Bool Bool ℂ :=
  Matrix.of fun y z => if y = z then (bscProbability p x y : ℂ) else 0

/-- PDF p.7, Eq.(17): independent BSC outputs conditioned on the same input bit. -/
def independentBsc (pB pE : ℝ) (x y z : Bool) : ℝ :=
  bscProbability pB x y * bscProbability pE x z

/-- PDF pp.9–10: erasure dilation |a> -> sqrt(1-eps)|a,e>+sqrt(eps)|e,a>.
Both shields are trivial, and symbol 2 is the orthogonal erasure flag. -/
def erasureData (eps : ℝ) : WiretapData (Fin 3) (Fin 3) Unit Unit where
  V := Matrix.of fun o a =>
    if o.1.val = a.toNat ∧ o.2.1 = 2 then (Real.sqrt (1 - eps) : ℂ)
    else if o.1 = 2 ∧ o.2.1.val = a.toNat then (Real.sqrt eps : ℂ) else 0
  psi := fun z => ket (z, ())

/-- PDF p.10: the accepted qubit amplitude-damping channel with loss probability 1-eta.
Its Kraus labels are reversed relative to the source; the summed channel is the same. -/
def dampingMap (eta : ℝ) : Superop Bool Bool := QAlgorithms.Papers.Independent.Independent2.P01.damping (1 - eta)

/-- PDF p.10: the actual amplitude-channel output for a computational-basis input. -/
def dampingAmplitude (eta : ℝ) (z : Bool) :=
  dampingMap eta (pureDensity (ket z))

/-- PDF p.10: phase-modulated Bell vector with reference C first and Bob's input second. -/
def binaryPhaseBellVector (x : Bool) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then
    bitSign (x && p.1) / (Real.sqrt 2 : ℂ) else 0

/-- PDF pp.10–11: apply the same amplitude-damping channel to half of the Bell state. -/
def dampingPhaseOutput (eta : ℝ) (x : Bool) :=
  idTensorSuperop (dampingMap eta) (pureDensity (binaryPhaseBellVector x))

/-- Computational order |00>, |01>, |10>, |11>, C first. -/
def cbIndex (p : Bool × Bool) : Fin 4 :=
  if p.1 then (if p.2 then 3 else 2) else (if p.2 then 1 else 0)

/-- PDF p.11: the exact displayed matrix, including loss at |10><10|. -/
def dampingPhaseMatrix (eta : ℝ) (x : Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1 / 2, 0, 0, bitSign x * (Real.sqrt eta : ℂ) / 2;
     0, 0, 0, 0;
     0, 0, (1 - (eta : ℂ)) / 2, 0;
     bitSign x * (Real.sqrt eta : ℂ) / 2, 0, 0, (eta : ℂ) / 2]

/-- Sanity: a classical channel discards every off-diagonal output entry. -/
example {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (p : X → Y → Z → ℝ) (rho : Matrix X X ℂ) (a b : Y × Z) (h : a ≠ b) :
    classicalEmbedding p rho a b = 0 := by
  simp [classicalEmbedding, h]

/-- Sanity: a noiseless BSC has no bit-flip transition. -/
example (x : Bool) : bscProbability 0 x x = 1 := by
  simp [bscProbability]

/-- Sanity: at eta=1 the loss Kraus operator is zero on every entry. -/
example : QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus (1 - (1 : ℝ)) true = 0 := by
  ext b a
  simp [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus]

/-- Sanity: C first puts the loss basis vector |10> at matrix index 2. -/
example : cbIndex (true, false) = 2 := by
  rfl

/-- Sanity: tracing the purification gives the usual matrix contraction over S1. -/
example (d : WiretapData B E S1 S2) (z a b : Bool) :
    (traceRight (pureDensity (d.psi z))) a b = ∑ s : S1, d.psi z (a, s) * conj (d.psi z (b, s)) := by
  rfl

/-- Sanity: zero input bits remain zero under either linear encoder. -/
example (n : ℕ) (reverse : Bool) :
    polarEncode n reverse (fun _ => false) = fun _ => false := by
  funext j
  simp [polarEncode]

/-- Sanity: a singleton input label carries zero Holevo information. -/
example {O : Type} [Fintype O] [DecidableEq O] (rho : Matrix O O ℂ) :
    uniformHolevo (fun _ : Unit => rho) = 0 := by
  simp [uniformHolevo]

/-- Sanity: erasure endpoints transmit to Bob or to Eve with unit amplitude. -/
example : (erasureData 0).V (0, 2, ()) false = 1 ∧
    (erasureData 1).V (2, 0, ()) false = 1 := by
  simp [erasureData]

end

end QAlgorithms.Papers.Independent.Intakethird100.P74


