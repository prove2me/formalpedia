-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P10
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:33:42.780827+00:00
-- url     : https://prove2.me/theorems/34d85457-21c0-46eb-a4dc-3cdae94eec0e
-- title:
--   Definitions for Polar codes for degradable quantum channels
-- statement:
--   The objects the formalized statements of *Polar codes for degradable quantum channels* (arXiv:1109.5346) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BinaryCQ`: PDF p.3: a pair of binary cq letter operators; validity is `IsBinaryCQ`.
--   - `IsBinaryCQ`: PDF p.3: both letter operators are positive semidefinite and trace one.
--   - `symmetricInformation`: PDF p.3: symmetric Holevo information, with the frozen entropy in bits.
--   - `polarCoefficient`: PDF p.3: coefficient (j,k) of B_N F_2^(tensor n), over GF(2). The address map is the frozen most-significant-bit-first map; B_N reverses j's n-bit address before applying the tensor kernel.
--   - `polarWord`: PDF p.3: row-vector multiplication u -> u G_N over GF(2).
--   - `combinedOutput`: PDF p.3: N independent memoryless uses, after the prescribed row polar transform.
--   - `SplitRegister`: PDF p.3, (1)–(3): prefix classical register and all N quantum outputs.
--   - `synthesized`: PDF p.3, (1)–(3): the synthesized letter density, constructed by uniform averaging over every bit other than i and retaining the preceding bits. The denominator 2^(N-1) includes both prefix and suffix averaging.
--   - `synthesizedDegrader`: PDF p.4, proof of Lemma 3: identity on prefix bits, D^(tensor N) on outputs.
--   - `polarThreshold`: PDF pp.3–4: 2^(-N^beta), for N=2^n; beta is a real exponent.
--   - `goodSet`: PDF p.3, (4): the strict ROOT-fidelity good set. Defined for every real beta; operational uses impose 0<beta<1/2, whereas Theorem 2 only assumes beta<1/2.
--   - `badSet`: PDF p.3, (5): the complement of the strict good set; equality is bad.
--   - `poorSet`: PDF p.4: the strict ROOT-fidelity poor set for Eve.
--   - `leafProbability`: PDF pp.3–6: uniform probability of a set of n-step fair synthesis leaves. N=2^n is always positive, including n=0.
--   - `Wiretap`: PDF pp.4–5: actual joint cq wiretap output. One CPTP map degrades both Bob letters to Eve letters; the joint output need not be a channel complement.
--   - `Wiretap.bob`: PDF p.4, (8): Bob's marginal of the actual joint cq output.
--   - `Wiretap.eve`: PDF p.4, (9): Eve's marginal of the same joint cq output.
--   - `informationSet`: PDF p.5: information indices A=P_E intersect G_B; message count is 2^|A|.
--   - `frozenSet`: PDF p.5: frozen indices B=P_E intersect B_B.
--   - `assistanceSet`: PDF p.5: secret-key/ebit indices X=P_E^c intersect B_B.
--   - `randomizationSet`: PDF p.5: independent randomization indices Y=P_E^c intersect G_B.
--   - `dilationLetter`: PDF pp.6–7: receiver and environment of one fixed qubit-input isometry.
--   - `dilationBob`: PDF pp.6–7: Bob's cq channel induced by the specified orthonormal input basis.
--   - `dilationEve`: PDF pp.6–7: complementary cq channel of the SAME isometry and basis.
--   - `bellBobOutput`: PDF pp.6–7: reference–Bob output from the normalized Bell state in this basis, with E traced out. The input to U is the second Bell half.
--   - `symmetricCoherentInformation`: PDF pp.6–7: symmetric coherent information H(B)-H(AB) for the normalized Bell input.
--   - `PolarGate`: PDF pp.3,7: the elementary gate alphabet used for the polar transform alone. Distinct control and target wires ensure that each CNOT is a reversible quantum gate.
--   - `PolarGate.apply`: PDF pp.3,7, (15): the computational-basis action of a CNOT or SWAP gate.
--   - `circuitAction`: PDF pp.3,7: circuit action in list order. Its elementary-gate count is list length.
--   - `circuitOperator`: PDF p.7: coherent linear extension of a reversible classical gate network.
--   - `polarOperator`: PDF p.7: exact coherent u -> u G_N, with no added phases.
--   - `pureCQ`: PDF p.10, Appendix A: the pure-output cq channel, with validity supplied by unit norms.
--   - `minusChannel`: PDF p.10, Appendix A: the worse channel's even and odd parity mixtures, constructed from the input channel, not independent matrices constrained by a target equality.
--   - `amplitudeComplement`: PDF p.11: the printed amplitude-damping COMPLEMENT at original damping gamma. This is linear on all matrices: the upper-left entry is rho_00+(1-gamma)rho_11. It is damping with parameter 1-gamma, not with parameter gamma.
--   - `detectedJumpComplement`: PDF p.11: the photon-detected-jump complement, extended linearly using trace rather than an affine constant 1 on arbitrary operators.
--   - `basisColumn`: PDF p.11: column x of an arbitrary orthonormal basis, represented by a unitary matrix.
--   - `erasureData`: PDF p.11: embedding into the data sector orthogonal to Option.none, the erasure flag.
--   - `dephasingComplement`: PDF p.11: complement obtained by tracing B out of that isometry.
--   - `dephasingDiagonal`: PDF p.11: both environment outputs when the basis is unbiased to the Pauli eigenbasis.
--   - `cloningNormalization`: PDF p.11, (18)–(19): Delta_m=m(m+1)/2, with m a positive clone count in uses.
--   - `cloningEnvironment`: PDF p.11, (18)–(19): the two displayed complementary cloning outputs. The common environmental orthonormal basis can change with the chosen input basis by the cited covariance. No full cloning channel is reconstructed from these two states.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, https://arxiv.org/abs/1109.5346v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

/-!
Wilde–Guha, Polar codes for degradable quantum channels, arXiv:1109.5346v3.
All page references are PDF pages. Local definitions are specific to this paper.
Finite nonempty matrix registers; entropy in bits; F is SQUARED fidelity.
Indices in Lean are zero based: i : Fin (2^n) denotes printed index i+1.
Uniform counting over all synthesized leaves is the n-step marginal of the fair
independent plus/minus birth process. No asymptotic operational capacity is
identified with an entropy formula by definition. Deferred nodes are in HARD.md.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate
open Filter

-- Accepted definitions, without paper-local aliases.
open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)
open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.3: a pair of binary cq letter operators; validity is `IsBinaryCQ`. -/
abbrev BinaryCQ (H : Type*) := Bool → Matrix H H ℂ

/-- PDF p.3: both letter operators are positive semidefinite and trace one. -/
def IsBinaryCQ {H : Type*} [Fintype H] (W : BinaryCQ H) : Prop :=
  ∀ x, IsDensityMatrix (W x)

/-- PDF p.3: symmetric Holevo information, with the frozen entropy in bits. -/
def symmetricInformation {H : Type*} [Fintype H] [DecidableEq H]
    (W : BinaryCQ H) : ℝ :=
  vnEntropy (((2 : ℂ)⁻¹) • (W false + W true)) -
    (vnEntropy (W false) + vnEntropy (W true)) / 2

/-- PDF p.3: coefficient (j,k) of B_N F_2^(tensor n), over GF(2).
The address map is the frozen most-significant-bit-first map; B_N reverses
j's n-bit address before applying the tensor kernel. -/
def polarCoefficient (n : ℕ) (j k : Fin (2 ^ n)) : Bool :=
  decide (∀ t : Fin n,
    natToBits n k.val t = true → natToBits n j.val (Fin.rev t) = true)

/-- PDF p.3: row-vector multiplication u -> u G_N over GF(2). -/
def polarWord (n : ℕ) (u : Fin (2 ^ n) → Bool) : Fin (2 ^ n) → Bool :=
  fun k => decide ((∑ j : Fin (2 ^ n),
    if u j && polarCoefficient n j k then (1 : ZMod 2) else 0) = 1)

/-- PDF p.3: N independent memoryless uses, after the prescribed row polar transform. -/
def combinedOutput {H : Type*} (W : BinaryCQ H) (n : ℕ)
    (u : Fin (2 ^ n) → Bool) : Matrix (Fin (2 ^ n) → H) (Fin (2 ^ n) → H) ℂ :=
  fun a b => ∏ k, W (polarWord n u k) (a k) (b k)

/-- PDF p.3, (1)–(3): prefix classical register and all N quantum outputs. -/
abbrev SplitRegister (H : Type*) (n : ℕ) (i : Fin (2 ^ n)) :=
  (Fin i.val → Bool) × (Fin (2 ^ n) → H)

/-- PDF p.3, (1)–(3): the synthesized letter density, constructed by uniform
averaging over every bit other than i and retaining the preceding bits.
The denominator 2^(N-1) includes both prefix and suffix averaging. -/
def synthesized {H : Type*} [Fintype H] [DecidableEq H]
    (W : BinaryCQ H) (n : ℕ) (i : Fin (2 ^ n)) : BinaryCQ (SplitRegister H n i) := by
  classical
  exact fun x a b => if a.1 = b.1 then
    ((2 : ℂ) ^ (2 ^ n - 1))⁻¹ *
      ∑ u : Fin (2 ^ n) → Bool,
        if u i = x ∧ ∀ j : Fin i.val,
          u ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ = a.1 j
        then combinedOutput W n u a.2 b.2 else 0
    else 0

/-- PDF p.4, proof of Lemma 3: identity on prefix bits, D^(tensor N) on outputs. -/
def synthesizedDegrader {H K : Type*} [Fintype H] [DecidableEq H]
    (D : Superop H K) (n : ℕ) (i : Fin (2 ^ n)) :
    Superop (SplitRegister H n i) (SplitRegister K n i) :=
  idTensorSuperop (R := Fin i.val → Bool) (piSuperop (k := 2 ^ n) (fun _ => D))

/-- PDF pp.3–4: 2^(-N^beta), for N=2^n; beta is a real exponent. -/
def polarThreshold (n : ℕ) (beta : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(((2 : ℝ) ^ n) ^ beta))

/-- PDF p.3, (4): the strict ROOT-fidelity good set. Defined for every real beta;
operational uses impose 0<beta<1/2, whereas Theorem 2 only assumes beta<1/2. -/
def goodSet {H : Type*} [Fintype H] [DecidableEq H]
    (W : BinaryCQ H) (n : ℕ) (beta : ℝ) : Finset (Fin (2 ^ n)) := by
  classical
  exact Finset.univ.filter fun i =>
    rootFidelity (synthesized W n i false) (synthesized W n i true) < polarThreshold n beta

/-- PDF p.3, (5): the complement of the strict good set; equality is bad. -/
def badSet {H : Type*} [Fintype H] [DecidableEq H]
    (W : BinaryCQ H) (n : ℕ) (beta : ℝ) : Finset (Fin (2 ^ n)) := by
  classical
  exact Finset.univ \ goodSet W n beta

/-- PDF p.4: the strict ROOT-fidelity poor set for Eve. -/
def poorSet {H : Type*} [Fintype H] [DecidableEq H]
    (W : BinaryCQ H) (n : ℕ) (beta : ℝ) : Finset (Fin (2 ^ n)) := by
  classical
  exact Finset.univ.filter fun i =>
    1 - polarThreshold n beta <
      rootFidelity (synthesized W n i false) (synthesized W n i true)

/-- PDF pp.3–6: uniform probability of a set of n-step fair synthesis leaves.
N=2^n is always positive, including n=0. -/
def leafProbability {n : ℕ} (S : Finset (Fin (2 ^ n))) : ℝ :=
  (S.card : ℝ) / ((2 : ℝ) ^ n)

/-- PDF pp.4–5: actual joint cq wiretap output. One CPTP map degrades both
Bob letters to Eve letters; the joint output need not be a channel complement. -/
structure Wiretap (B E : Type*) [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] where
  output : BinaryCQ (B × E)
  density : IsBinaryCQ output
  degrading : Superop B E
  cptp : IsChannel degrading
  degrades : ∀ x, traceLeft (output x) = degrading (traceRight (output x))
  classicalEve : Commute (traceLeft (output false)) (traceLeft (output true))

/-- PDF p.4, (8): Bob's marginal of the actual joint cq output. -/
def Wiretap.bob {B E : Type*} [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (V : Wiretap B E) : BinaryCQ B :=
  fun x => traceRight (V.output x)

/-- PDF p.4, (9): Eve's marginal of the same joint cq output. -/
def Wiretap.eve {B E : Type*} [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (V : Wiretap B E) : BinaryCQ E :=
  fun x => traceLeft (V.output x)

/-- PDF p.5: information indices A=P_E intersect G_B; message count is 2^|A|. -/
def informationSet {B E : Type*} [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (V : Wiretap B E) (n : ℕ) (beta : ℝ) :=
  poorSet V.eve n beta ∩ goodSet V.bob n beta

/-- PDF p.5: frozen indices B=P_E intersect B_B. -/
def frozenSet {B E : Type*} [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (V : Wiretap B E) (n : ℕ) (beta : ℝ) :=
  poorSet V.eve n beta ∩ badSet V.bob n beta

/-- PDF p.5: secret-key/ebit indices X=P_E^c intersect B_B. -/
def assistanceSet {B E : Type*} [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (V : Wiretap B E) (n : ℕ) (beta : ℝ) := by
  classical
  exact (Finset.univ \ poorSet V.eve n beta) ∩ badSet V.bob n beta

/-- PDF p.5: independent randomization indices Y=P_E^c intersect G_B. -/
def randomizationSet {B E : Type*} [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (V : Wiretap B E) (n : ℕ) (beta : ℝ) := by
  classical
  exact (Finset.univ \ poorSet V.eve n beta) ∩ goodSet V.bob n beta

/-- PDF pp.6–7: receiver and environment of one fixed qubit-input isometry. -/
def dilationLetter {B E : Type*} [Fintype B] [Fintype E]
    (U : Matrix (B × E) Bool ℂ) (basis : Matrix.unitaryGroup Bool ℂ) (x : Bool) :
    Matrix (B × E) (B × E) ℂ :=
  let v : EuclideanSpace ℂ (B × E) := WithLp.toLp 2 fun z =>
    ∑ a : Bool, U z a * (basis : Matrix Bool Bool ℂ) a x
  pureDensity v

/-- PDF pp.6–7: Bob's cq channel induced by the specified orthonormal input basis. -/
def dilationBob {B E : Type*} [Fintype B] [Fintype E]
    (U : Matrix (B × E) Bool ℂ) (basis : Matrix.unitaryGroup Bool ℂ) : BinaryCQ B :=
  fun x => traceRight (dilationLetter U basis x)

/-- PDF pp.6–7: complementary cq channel of the SAME isometry and basis. -/
def dilationEve {B E : Type*} [Fintype B] [Fintype E]
    (U : Matrix (B × E) Bool ℂ) (basis : Matrix.unitaryGroup Bool ℂ) : BinaryCQ E :=
  fun x => traceLeft (dilationLetter U basis x)

/-- PDF pp.6–7: reference–Bob output from the normalized Bell state in this basis,
with E traced out. The input to U is the second Bell half. -/
def bellBobOutput {B E : Type*} [Fintype B] [Fintype E]
    (U : Matrix (B × E) Bool ℂ) (basis : Matrix.unitaryGroup Bool ℂ) :
    Matrix (Bool × B) (Bool × B) ℂ :=
  fun r s => (2 : ℂ)⁻¹ * ∑ e : E,
    (∑ a : Bool, U (r.2, e) a * (basis : Matrix Bool Bool ℂ) a r.1) *
      conj (∑ a : Bool, U (s.2, e) a * (basis : Matrix Bool Bool ℂ) a s.1)

/-- PDF pp.6–7: symmetric coherent information H(B)-H(AB) for the normalized Bell input. -/
def symmetricCoherentInformation {B E : Type*} [Fintype B] [DecidableEq B]
    [Fintype E] (U : Matrix (B × E) Bool ℂ) (basis : Matrix.unitaryGroup Bool ℂ) : ℝ :=
  vnEntropy (traceLeft (bellBobOutput U basis)) - vnEntropy (bellBobOutput U basis)

/-- n=0 has a single polar coefficient, equal to one. -/
example : polarCoefficient 0 0 0 = true := by simp [polarCoefficient]

/-- The uniform probability of no leaves is zero, including n=0. -/
example (n : ℕ) : leafProbability (n := n) ∅ = 0 := by simp [leafProbability]

/-- Averages and independent-use products retain the letter operators at blocklength one. -/
example {H : Type*} (W : BinaryCQ H) (u : Fin 1 → Bool) (a b : Fin 1 → H) :
    combinedOutput W 0 u a b = W (polarWord 0 u 0) (a 0) (b 0) := by
  simp [combinedOutput]

/-- PDF pp.3,7: the elementary gate alphabet used for the polar transform alone.
Distinct control and target wires ensure that each CNOT is a reversible quantum gate. -/
inductive PolarGate (N : ℕ) where
  | cnot (control target : Fin N) (distinct : control ≠ target)
  | swap (first second : Fin N)

/-- PDF pp.3,7, (15): the computational-basis action of a CNOT or SWAP gate. -/
def PolarGate.apply {N : ℕ} (g : PolarGate N) (u : Fin N → Bool) : Fin N → Bool :=
  match g with
  | .cnot c t _ => Function.update u t (xor (u c) (u t))
  | .swap a b => Function.update (Function.update u a (u b)) b (u a)

/-- PDF pp.3,7: circuit action in list order. Its elementary-gate count is list length. -/
def circuitAction {N : ℕ} (C : List (PolarGate N)) (u : Fin N → Bool) : Fin N → Bool :=
  C.foldl (fun v g => g.apply v) u

/-- PDF p.7: coherent linear extension of a reversible classical gate network. -/
def circuitOperator {N : ℕ} (C : List (PolarGate N)) : Matrix (Qubits N) (Qubits N) ℂ :=
  fun v u => if v = circuitAction C u then 1 else 0

/-- PDF p.7: exact coherent u -> u G_N, with no added phases. -/
def polarOperator (n : ℕ) : Matrix (Qubits (2 ^ n)) (Qubits (2 ^ n)) ℂ :=
  fun v u => if v = polarWord n u then 1 else 0

/-- PDF p.10, Appendix A: the pure-output cq channel, with validity supplied by unit norms. -/
def pureCQ {H : Type*} (psi0 psi1 : EuclideanSpace ℂ H) : BinaryCQ H :=
  fun x => pureDensity (if x then psi1 else psi0)

/-- PDF p.10, Appendix A: the worse channel's even and odd parity mixtures,
constructed from the input channel, not independent matrices constrained by a target equality. -/
def minusChannel {H : Type*} (W : BinaryCQ H) : BinaryCQ (H × H) :=
  fun x => if x then ((2 : ℂ)⁻¹) •
    (Matrix.kronecker (W false) (W true) + Matrix.kronecker (W true) (W false))
  else ((2 : ℂ)⁻¹) •
    (Matrix.kronecker (W false) (W false) + Matrix.kronecker (W true) (W true))

/-- PDF p.11: the printed amplitude-damping COMPLEMENT at original damping gamma.
This is linear on all matrices: the upper-left entry is rho_00+(1-gamma)rho_11.
It is damping with parameter 1-gamma, not with parameter gamma. -/
def amplitudeComplement (gamma : ℝ) : Superop Bool Bool :=
  fun rho a b => if a then
    if b then (gamma : ℂ) * rho true true else (Real.sqrt gamma : ℂ) * rho true false
  else if b then (Real.sqrt gamma : ℂ) * rho false true
  else rho false false + ((1 - gamma : ℝ) : ℂ) * rho true true

/-- PDF p.11: the photon-detected-jump complement, extended linearly using trace
rather than an affine constant 1 on arbitrary operators. -/
def detectedJumpComplement (gamma : ℝ) : Superop Bool Bool :=
  fun rho => Matrix.diagonal fun x => if x then (gamma : ℂ) * rho true true
    else rho.trace - (gamma : ℂ) * rho true true

/-- PDF p.11: column x of an arbitrary orthonormal basis, represented by a unitary matrix. -/
def basisColumn {H : Type*} [Fintype H] [DecidableEq H]
    (basis : Matrix.unitaryGroup H ℂ) (x : H) : EuclideanSpace ℂ H :=
  WithLp.toLp 2 fun a => (basis : Matrix H H ℂ) a x

/-- PDF p.11: embedding into the data sector orthogonal to Option.none, the erasure flag. -/
def erasureData (d : ℕ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Option (Fin d)) (Option (Fin d)) ℂ :=
  fun i j => match i, j with
    | some a, some b => rho a b
    | _, _ => 0

/-- PDF p.11: complement obtained by tracing B out of that isometry. -/
def dephasingComplement (p : ℝ) (sigma : Matrix Bool Bool ℂ) : Superop Bool Bool :=
  let V := indexedKrausDilation (fun x : Bool =>
    if x then (Real.sqrt p : ℂ) • sigma
    else (Real.sqrt (1 - p) : ℂ) • (1 : Matrix Bool Bool ℂ))
  fun rho => traceLeft (V * rho * Vᴴ)

/-- PDF p.11: both environment outputs when the basis is unbiased to the Pauli eigenbasis. -/
def dephasingDiagonal (p : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun x => if x then (p : ℂ) else ((1 - p : ℝ) : ℂ)

/-- PDF p.11, (18)–(19): Delta_m=m(m+1)/2, with m a positive clone count in uses. -/
def cloningNormalization (m : ℕ) : ℝ := (m : ℝ) * (m + 1) / 2

/-- PDF p.11, (18)–(19): the two displayed complementary cloning outputs.
The common environmental orthonormal basis can change with the chosen input basis
by the cited covariance. No full cloning channel is reconstructed from these two states. -/
def cloningEnvironment (m : ℕ) (basis : Matrix.unitaryGroup (Fin m) ℂ) (x : Bool) :
    Matrix (Fin m) (Fin m) ℂ :=
  ∑ i : Fin m, (((i.val + 1 : ℝ) / cloningNormalization m : ℝ) : ℂ) •
    pureDensity (basisColumn basis (if x then Fin.rev i else i))

/-- An empty circuit acts as the identity, including the n=0 transform case. -/
example {N : ℕ} (u : Fin N → Bool) : circuitAction [] u = u := rfl

/-- The worse branch is the even-parity mixture, with weight 1/2 on each term. -/
example {H : Type*} (W : BinaryCQ H) : minusChannel W false = ((2 : ℂ)⁻¹) •
    (Matrix.kronecker (W false) (W false) + Matrix.kronecker (W true) (W true)) := rfl

/-- The complementary damping off-diagonal coefficient is sqrt(gamma). -/
example (gamma : ℝ) (rho : Matrix Bool Bool ℂ) :
    amplitudeComplement gamma rho true false = (Real.sqrt gamma : ℂ) * rho true false := rfl

/-- The detected-jump complement is linear at zero, with no affine constant one. -/
example (gamma : ℝ) : detectedJumpComplement gamma 0 = 0 := by
  ext a b
  cases a <;> cases b <;> simp [detectedJumpComplement]

/-- The erasure data embedding has no component in the orthogonal flag sector. -/
example (d : ℕ) (rho : Matrix (Fin d) (Fin d) ℂ) : erasureData d rho none none = 0 := rfl

/-- The no-error branch of the Pauli isometry is sqrt(1-p) times the identity. -/
example (p : ℝ) (sigma : Matrix Bool Bool ℂ) :
    indexedKrausDilation (fun x : Bool =>
      if x then (Real.sqrt p : ℂ) • sigma
      else (Real.sqrt (1 - p) : ℂ) • (1 : Matrix Bool Bool ℂ))
        (false, false) true = 0 := by simp [indexedKrausDilation]

/-- At one clone the normalizing constant is one, not zero. -/
example : cloningNormalization 1 = 1 := by norm_num [cloningNormalization]

end QAlgorithms.Papers.Independent.Intakethird100.P10


