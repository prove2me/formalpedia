-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36
-- name    : QAlgorithms_Papers_Independent_Gap48_P36
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T04:50:19.85741+00:00
-- url     : https://prove2.me/theorems/775bc559-1596-4006-b7f2-356993070f90
-- title:
--   Definitions for Properties of Conjugate Channels with Applications to Additivity and Multiplicativity
-- statement:
--   The objects the formalized statements of *Properties of Conjugate Channels with Applications to Additivity and Multiplicativity* (arXiv:quant-ph/0509126) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `krausNumber`: PDF pp.5,30: minimum size of a normalized Kraus representation. On a nonchannel the natural infimum may be zero; results require IsChannel.
--   - `choiEigenvalue`: PDF pp.29–30: eigenvalues of the computed normalized Choi matrix. The non-Hermitian default is never used for channels.
--   - `choiEigenvector`: PDF pp.29–30: an orthonormal spectral basis, with its source tensor order.
--   - `ChoiSupport`: PDF pp.29–30: retain only nonzero Choi eigenvalues, including multiplicity.
--   - `spectralKraus`: PDF p.29, (89): spectral Kraus family with the essential sqrt(d lambda). Neither Kraus normalization nor minimality is built into this definition.
--   - `constrainedHolevo`: PDF p.9: constrained Holevo quantity, with the input state fixed.
--   - `entanglementFormation`: PDF p.9, (18): the finite pure-state convex roof of marginal entropy.
--   - `UnitaryBasis`: PDF p.13, (30): a complete orthogonal unitary basis, including its identity label. No orthogonality assumption is imposed on vectors in the Hadamard constructions.
--   - `PhaseClosed`: PDF p.15, (35): closure up to a scalar phase; no raw matrix group is assumed.
--   - `weightedKraus`: PDF p.14, (32): canonical weighted unitary Kraus family.
--   - `ProbabilityWeights`: PDF p.14: nonnegative probabilities, allowing zero weights.
--   - `randomUnitary`: PDF p.14, (32): the channel is computed from weights and basis matrices.
--   - `randomComplement`: PDF p.14, (33): canonical complement, retaining every Kraus label.
--   - `noisyComplement`: PDF pp.14,19: canonical noisy complement, with Kraus matrices T_m/d.
--   - `pureNoisyImage`: PDF p.14: the image of normalized pure inputs, excluding the zero vector.
--   - `weightMatrix`: PDF p.14: A=diag(a_m), distinct from its positive square root.
--   - `weightRoot`: PDF p.14: positive square root of the diagonal probability matrix.
--   - `DoublyStochastic`: PDF p.20, Theorem 12(d): a real nonnegative matrix with row and column sums one.
--   - `ImageConditions`: PDF pp.19–20: the four necessary conditions, with (c) read as modulus. The source's Hadamard conjugation is entrywise conjugation, hence squared modulus.
--   - `WeylLabel`: PDF p.15: projective qudit labels; raw matrices need not form a group. The accepted Information100.P39.PauliLabel instead encodes N binary qubits.
--   - `finWeyl`: PDF p.15, (36): accepted positive-phase X^j Z^k, reindexed to Fin d. The accepted Information100.P34.weyl has exactly this shift/clock order. This wrapper changes only the coordinate type from ZMod d to Fin d.
--   - `printedMultiplier`: PDF p.15, (39), with the duplicate i in its Fourier exponent removed. Printed: (mk-jn)i2pi i/d. Changed: (mk-jn)2pi i/d, forced by the unitary conjugation (36)-(37) and the Fourier calculation used in (43). The remaining printed phase and Fourier sign do not change the modulus for real a. This expression is used ONLY through its modulus.
--   - `maxPauliMultiplierSq`: PDF p.16: finite supremum of squared Weyl multiplier magnitudes. The accepted Next46.P14.largestMultiplier is an unrelated message-length maximum. The d=1 set is empty, with real supremum zero; the bound still reads 1.
--   - `pauliTwoBound`: PDF p.16: the square-root upper bound (42).
--   - `basisCoefficient`: PDF p.17, (44): complex basis coefficient Tr(T_m^dagger rho), with no extra factor. The accepted Claimed50.P03.coefficient is a normalized real qubit-word coefficient.
--   - `FlatSupport`: PDF p.20: the invariant definition of D-decomposability used in Theorem 13: exactly D nonzero coefficients, all of unit modulus. General block reducibility is not substituted for this predicate.
--   - `SortedRows`: PDF p.22: a genuine permutation of labeled coefficients, ordered row by row.
--   - `blockWeight`: PDF p.22: beta_i is a sum of d weights, not an average.
--   - `blockBound`: PDF p.22, (60): the finite-p bound for the sorted block weights.
--   - `CosetRows`: PDF pp.25–26: rows of the labeled rearrangement are cosets of one subgroup. Tied numerical weights never merge Kraus labels.
--   - `cyclicNext`: PDF p.26: cyclic successor, only used for positive tensor counts.
--   - `krausLinearizer`: PDF p.26, (76): the Kraus linearizer; all tensor indices are retained. This differs from the accepted Support21.P18.theta qubit spin-flip map.
--   - `leftCycle`: PDF p.26: left cyclic shift on tensor basis kets.
--   - `channelLinearizer`: PDF p.26, (77): tensor power of the computed trace dual applied to L_p. The accepted definitions named omega are state vectors or angular matrix sets, not the channel linearization operator (77).
--   - `qubitLambda`: PDF p.31: Bloch multiplier for the axis with nonzero binary Pauli label k.
--   - `qubitAxis`: PDF p.31: Hermitian Pauli axis. The label (1,1) has XZ=-iY, so its Hermitian representative is iXZ. This phase does not change its channel.
--   - `qubitAxisState`: PDF p.31: the two normalized spectral projectors of a nonidentity qubit axis.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, https://arxiv.org/abs/quant-ph/0509126v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

/-! King–Matsumoto–Nathanson–Ruskai, arXiv:quant-ph/0509126v3.
All page numbers refer to PDF pages. Finite matrices, normalized states and natural
logarithms are used for entropy. The imported Holevo capacity is in bits;
its additivity identity is invariant under this fixed positive unit conversion. Source discrepancies and deferred clauses are in HARD.md.
Compilation is pending the mechanical batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P48
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)
open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]
variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]
variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- PDF pp.5,30: minimum size of a normalized Kraus representation.
On a nonchannel the natural infimum may be zero; results require IsChannel. -/
def krausNumber (Phi : Superop A B) : ℕ :=
  sInf {r | ∃ F : Fin r → Matrix B A ℂ, IsKrausFamily F ∧ Phi = krausApply F}

/-- PDF pp.29–30: eigenvalues of the computed normalized Choi matrix.
The non-Hermitian default is never used for channels. -/
def choiEigenvalue (Phi : Superop A B) (k : A × B) : ℝ :=
  if h : (normalizedChoi Phi).IsHermitian then h.eigenvalues k else 0

/-- PDF pp.29–30: an orthonormal spectral basis, with its source tensor order. -/
def choiEigenvector (Phi : Superop A B) (k : A × B) : EuclideanSpace ℂ (A × B) :=
  if h : (normalizedChoi Phi).IsHermitian then h.eigenvectorBasis k else 0

/-- PDF pp.29–30: retain only nonzero Choi eigenvalues, including multiplicity. -/
abbrev ChoiSupport (Phi : Superop A B) := {k : A × B // choiEigenvalue Phi k ≠ 0}

/-- PDF p.29, (89): spectral Kraus family with the essential sqrt(d lambda).
Neither Kraus normalization nor minimality is built into this definition. -/
def spectralKraus (Phi : Superop A B) : ChoiSupport Phi → Matrix B A ℂ :=
  fun k b a => (Real.sqrt ((Fintype.card A : ℝ) * choiEigenvalue Phi k.val) : ℂ) *
    choiEigenvector Phi k.val (a,b)

/-- PDF p.9: constrained Holevo quantity, with the input state fixed. -/
def constrainedHolevo (Phi : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  entropy (Phi rho) - hhat Phi rho

/-- PDF p.9, (18): the finite pure-state convex roof of marginal entropy. -/
def entanglementFormation (gamma : Matrix (B × C) (B × C) ℂ) : ℝ :=
  convexRoof (fun psi => entropy (traceRight (pureDensity psi))) gamma

/-- PDF p.13, (30): a complete orthogonal unitary basis, including its identity label.
No orthogonality assumption is imposed on vectors in the Hadamard constructions. -/
structure UnitaryBasis (A K : Type*) [Fintype A] [DecidableEq A] [Fintype K] where
  matrix : K → Matrix A A ℂ
  identityLabel : K
  cardinality : Fintype.card K = Fintype.card A ^ 2
  identity : matrix identityLabel = 1
  unitary : ∀ k, (matrix k)ᴴ * matrix k = 1
  orthogonal : ∀ j k, ((matrix j)ᴴ * matrix k).trace =
    if j = k then (Fintype.card A : ℂ) else 0

/-- PDF p.15, (35): closure up to a scalar phase; no raw matrix group is assumed. -/
def PhaseClosed (T : UnitaryBasis A K) : Prop :=
  ∀ m n, ∃ k : K, ∃ z : ℂ, ‖z‖ = 1 ∧ (T.matrix m)ᴴ * T.matrix n = z • T.matrix k

/-- PDF p.14, (32): canonical weighted unitary Kraus family. -/
def weightedKraus (T : K → Matrix A A ℂ) (a : K → ℝ) : K → Matrix A A ℂ :=
  fun k => (Real.sqrt (a k) : ℂ) • T k

/-- PDF p.14: nonnegative probabilities, allowing zero weights. -/
def ProbabilityWeights (a : K → ℝ) : Prop := (∀ k, 0 ≤ a k) ∧ ∑ k, a k = 1

/-- PDF p.14, (32): the channel is computed from weights and basis matrices. -/
def randomUnitary (T : K → Matrix A A ℂ) (a : K → ℝ) : Superop A A :=
  krausApply (weightedKraus T a)

/-- PDF p.14, (33): canonical complement, retaining every Kraus label. -/
def randomComplement (T : K → Matrix A A ℂ) (a : K → ℝ) : Superop A K :=
  complementaryChannel (indexedKrausDilation (weightedKraus T a))

/-- PDF pp.14,19: canonical noisy complement, with Kraus matrices T_m/d. -/
def noisyComplement (T : K → Matrix A A ℂ) : Superop A K :=
  complementaryChannel (indexedKrausDilation
    (fun k => ((Fintype.card A : ℂ)⁻¹) • T k))

/-- PDF p.14: the image of normalized pure inputs, excluding the zero vector. -/
def pureNoisyImage (T : K → Matrix A A ℂ) : Set (Matrix K K ℂ) :=
  {gamma | ∃ psi : EuclideanSpace ℂ A, IsState psi ∧ gamma = noisyComplement T (pureDensity psi)}

/-- PDF p.14: A=diag(a_m), distinct from its positive square root. -/
def weightMatrix (a : K → ℝ) : Matrix K K ℂ := Matrix.diagonal (fun k => (a k : ℂ))

/-- PDF p.14: positive square root of the diagonal probability matrix. -/
def weightRoot (a : K → ℝ) : Matrix K K ℂ :=
  Matrix.diagonal (fun k => (Real.sqrt (a k) : ℂ))

/-- PDF p.20, Theorem 12(d): a real nonnegative matrix with row and column sums one. -/
def DoublyStochastic (M : Matrix K K ℝ) : Prop :=
  (∀ j k, 0 ≤ M j k) ∧ (∀ j, ∑ k, M j k = 1) ∧ (∀ k, ∑ j, M j k = 1)

/-- PDF pp.19–20: the four necessary conditions, with (c) read as modulus.
The source's Hadamard conjugation is entrywise conjugation, hence squared modulus. -/
def ImageConditions (d : ℕ) (gamma : Matrix K K ℂ) : Prop :=
  IsDensityMatrix gamma ∧
  ((d : ℂ) • gamma) * ((d : ℂ) • gamma) = (d : ℂ) • gamma ∧
  Matrix.rank ((d : ℂ) • gamma) = d ∧
  (∀ k, gamma k k = ((d : ℂ)^2)⁻¹) ∧
  (∀ j k, ‖gamma j k‖ ≤ ((d : ℝ)^2)⁻¹) ∧
  DoublyStochastic (fun j k => (d : ℝ)^3 * Complex.normSq (gamma j k))

/-- PDF p.15: projective qudit labels; raw matrices need not form a group.
The accepted Information100.P39.PauliLabel instead encodes N binary qubits. -/
abbrev WeylLabel (d : ℕ) := ZMod d × ZMod d

/-- PDF p.15, (36): accepted positive-phase X^j Z^k, reindexed to Fin d.
The accepted Information100.P34.weyl has exactly this shift/clock order.
This wrapper changes only the coordinate type from ZMod d to Fin d. -/
def finWeyl (d : ℕ) [NeZero d] (jk : WeylLabel d) : Matrix (Fin d) (Fin d) ℂ :=
  (QAlgorithms.Papers.Independent.Information100.P34.weyl jk.1 jk.2).submatrix
    (ZMod.finEquiv d) (ZMod.finEquiv d)

/-- PDF p.15, (39), with the duplicate i in its Fourier exponent removed.
Printed: (mk-jn)i2pi i/d. Changed: (mk-jn)2pi i/d, forced by the
unitary conjugation (36)-(37) and the Fourier calculation used in (43).
The remaining printed phase and Fourier sign do not change the modulus
for real a. This expression is used ONLY through its modulus. -/
def printedMultiplier (d : ℕ) [NeZero d] (a : WeylLabel d → ℝ) (jk : WeylLabel d) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((jk.1.val * jk.2.val : ℕ) : ℂ) / (d : ℂ)) *
    ∑ mn, (a mn : ℂ) * Complex.exp
      (2 * Real.pi * Complex.I * (((mn.1.val * jk.2.val : ℕ) : ℂ) -
        ((jk.1.val * mn.2.val : ℕ) : ℂ)) / (d : ℂ))

/-- PDF p.16: finite supremum of squared Weyl multiplier magnitudes.
The accepted Next46.P14.largestMultiplier is an unrelated message-length maximum.
The d=1 set is empty, with real supremum zero; the bound still reads 1. -/
def maxPauliMultiplierSq (d : ℕ) [NeZero d] (a : WeylLabel d → ℝ) : ℝ :=
  sSup {x | ∃ jk : WeylLabel d, jk ≠ 0 ∧ x = ‖printedMultiplier d a jk‖^2}

/-- PDF p.16: the square-root upper bound (42). -/
def pauliTwoBound (d : ℕ) [NeZero d] (a : WeylLabel d → ℝ) : ℝ :=
  Real.sqrt ((1 + ((d : ℝ) - 1) * maxPauliMultiplierSq d a) / (d : ℝ))

/-- PDF p.17, (44): complex basis coefficient Tr(T_m^dagger rho), with no extra factor.
The accepted Claimed50.P03.coefficient is a normalized real qubit-word coefficient. -/
def basisCoefficient (T : K → Matrix A A ℂ) (rho : Matrix A A ℂ) (k : K) : ℂ :=
  ((T k)ᴴ * rho).trace

/-- PDF p.20: the invariant definition of D-decomposability used in Theorem 13:
exactly D nonzero coefficients, all of unit modulus. General block reducibility
is not substituted for this predicate. -/
def FlatSupport (T : K → Matrix A A ℂ) (rho : Matrix A A ℂ) (D : ℕ) : Prop :=
  (Finset.univ.filter (fun k => basisCoefficient T rho k ≠ 0)).card = D ∧
    ∀ k, basisCoefficient T rho k = 0 ∨ ‖basisCoefficient T rho k‖ = 1

/-- PDF p.22: a genuine permutation of labeled coefficients, ordered row by row. -/
def SortedRows {d : ℕ} (a : K → ℝ) (e : (Fin d × Fin d) ≃ K) : Prop :=
  ∀ u v, u.1.val * d + u.2.val ≤ v.1.val * d + v.2.val → a (e v) ≤ a (e u)

/-- PDF p.22: beta_i is a sum of d weights, not an average. -/
def blockWeight {d : ℕ} (a : K → ℝ) (e : (Fin d × Fin d) ≃ K) (i : Fin d) : ℝ :=
  ∑ j, a (e (i,j))

/-- PDF p.22, (60): the finite-p bound for the sorted block weights. -/
def blockBound {d : ℕ} (p : ℝ) (a : K → ℝ) (e : (Fin d × Fin d) ≃ K) : ℝ :=
  Real.rpow (∑ i, Real.rpow (blockWeight a e i) p) (1 / p)

/-- PDF pp.25–26: rows of the labeled rearrangement are cosets of one subgroup.
Tied numerical weights never merge Kraus labels. -/
def CosetRows {d : ℕ} [NeZero d]
    (e : (Fin d × Fin d) ≃ WeylLabel d) : Prop :=
  ∃ S : AddSubgroup (WeylLabel d), ∀ i, ∃ g : WeylLabel d,
    Set.range (fun j => e (i,j)) = {q | q - g ∈ S}

/-- PDF p.26: cyclic successor, only used for positive tensor counts. -/
def cyclicNext {p : ℕ} (i : Fin p) : Fin p :=
  ⟨(i.val + 1) % p, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- PDF p.26, (76): the Kraus linearizer; all tensor indices are retained.
This differs from the accepted Support21.P18.theta qubit spin-flip map. -/
def krausLinearizer (F : K → Matrix B A ℂ) (p : ℕ) :
    Matrix (Fin p → A) (Fin p → A) ℂ :=
  fun a b => ∑ ks : Fin p → K, ∏ i, ((F (ks i))ᴴ * F (ks (cyclicNext i))) (a i) (b i)

/-- PDF p.26: left cyclic shift on tensor basis kets. -/
def leftCycle (A : Type*) [DecidableEq A] (p : ℕ) :
    Matrix (Fin p → A) (Fin p → A) ℂ :=
  fun a b => if a = (fun i => b (cyclicNext i)) then 1 else 0

/-- PDF p.26, (77): tensor power of the computed trace dual applied to L_p.
The accepted definitions named omega are state vectors or angular matrix sets,
not the channel linearization operator (77). -/
def channelLinearizer (Phi : Superop A B) (p : ℕ) :
    Matrix (Fin p → A) (Fin p → A) ℂ :=
  piSuperop (fun _ : Fin p => operatorTraceDual Phi) (leftCycle B p)

/-- PDF p.31: Bloch multiplier for the axis with nonzero binary Pauli label k. -/
def qubitLambda (a : WeylLabel 2 → ℝ) (k : WeylLabel 2) : ℝ :=
  2 * (a 0 + a k) - 1

/-- PDF p.31: Hermitian Pauli axis. The label (1,1) has XZ=-iY,
so its Hermitian representative is iXZ. This phase does not change its channel. -/
def qubitAxis (k : WeylLabel 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if k = (1,1) then Complex.I • finWeyl 2 k else finWeyl 2 k

/-- PDF p.31: the two normalized spectral projectors of a nonidentity qubit axis. -/
def qubitAxisState (k : WeylLabel 2) (positive : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (1 + (if positive then (1 : ℂ) else -1) • qubitAxis k)

/-! Small definition sanity checks, without proofs of the source theorems. -/

example (d : ℕ) [NeZero d] (i : Fin d) : finWeyl d (0,0) i i = 1 := by
  simp [finWeyl, QAlgorithms.Papers.Independent.Information100.P34.weyl]

example (a : Fin 1 → ℝ) : weightMatrix a 0 0 = (a 0 : ℂ) := rfl

example : leftCycle (Fin 1) 1 (fun _ => 0) (fun _ => 0) = 1 := by
  simp [leftCycle]

example (a : WeylLabel 2 → ℝ) (k : WeylLabel 2) :
    qubitLambda a k = 2 * (a 0 + a k) - 1 := rfl

end QAlgorithms.Papers.Independent.Gap48.P36


