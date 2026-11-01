-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P03
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T03:47:23.167733+00:00
-- url     : https://prove2.me/theorems/59a7a766-90b6-4e8b-af69-a9e037bb376a
-- title:
--   Definitions for Quantum measurements and the Abelian Stabilizer Problem
-- statement:
--   The objects the formalized statements of *Quantum measurements and the Abelian Stabilizer Problem* (arXiv:quant-ph/9511026) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ASPAction`: PDF p.3: an action on a uniquely encoded subset, with no membership algorithm. The total black box has unrestricted behavior outside M.
--   - `stabilizer`: PDF pp.3–4: the stabilizer is constructed from the action and the given point.
--   - `integerBits`: PDF p.3, reasonable coding: one sign bit and a self-delimited binary magnitude. This explicit length differs by a constant factor from ordinary signed integer coding.
--   - `latticeBasisBits`: PDF p.4: total bit length of the columns of an additive lattice basis.
--   - `orderAction`: PDF p.4, example 1: the integer-power action on the residue ring.
--   - `andTau`: PDF p.11: Toffoli, with controls on the first two wires.
--   - `notTau`: PDF p.8: the XOR lift of NOT, distinct from the single-wire NOT.
--   - `cTauBasis`: PDF p.8: C_tau includes copy/XOR in addition to the XOR lifts of NOT and AND.
--   - `rBasis`: PDF p.8: the classical reversible basis R.
--   - `kitaevGateBasis`: PDF p.11: all one-qubit unitaries, CNOT and Toffoli; not a finite gate set.
--   - `OrthogonalProjectorFamily`: PDF pp.10,15: finite orthogonal families, encoded by their orthogonal projectors. No completeness assumption is imposed. Zero projectors are harmless.
--   - `OrthogonalProjectorFamily.support`: PDF pp.10,15: projection onto the measured support N.
--   - `subspaceProbability`: PDF p.9, equation (8): Born probability for a subspace projector.
--   - `Computes`: PDF p.11, Definition 3: the output register, rather than the whole memory, is measured. Inputs outside the promise are unconstrained.
--   - `PartialUnitary`: PDF p.12: a genuine partial unitary is an isometry equivalence between subspaces.
--   - `PartialUnitary.inverse`: PDF p.12: partial inverse, with domain and range swapped.
--   - `PartialApprox`: PDF p.12: precision on the intended domain, including BOTH subspace inclusions. The printed undefined A is read as U_tilde, as forced by the preceding definition.
--   - `PartialUnitary.apply`: A total evaluation helper for a partial unitary, using projection onto its domain. It is NOT asserted to be a full unitary. Only valid-domain evaluations are used below.
--   - `partialRun`: PDF p.12: a compatible sequence is evaluated in chronological order.
--   - `PartialSequenceApprox`: PDF p.12: the full precision relation for two valid partial-operation sequences on specified initial domains. Besides the vector bound, both the initial-domain and composite-range inclusions are required. Validity of both chains is supplied by uses.
--   - `binaryAngle`: PDF p.14: the exactly represented finite binary angle, first bit of weight 1/2.
--   - `rotatedZero`: PDF p.14: |x> tensored with the real rotation of |0>.
--   - `randomBitBell`: PDF p.14: the Bell state produced by copying a Hadamard bit with CNOT.
--   - `garbageState`: PDF pp.14–15: the physical output when basis input x produces (G(x),g(x)).
--   - `coherentImage`: PDF pp.14–15: the ideal coherent image before discarding work.
--   - `phaseAncilla`: PDF p.16: the eigenphase ancilla block H diag(1,lambda) H.
--   - `eigenphaseTest`: PDF p.16, equation (16): H, controlled U, H; target is the second factor.
--   - `measurementMatrix`: PDF p.15, Definition 5: measurement operator on N tensor D, extended by identity on the unmeasured orthogonal complement. This extension is also used in Theorem 2.
--   - `eigenspaceOutcomeProbability`: PDF p.15: conditional probability, with ordered output wires C and zero work D.
--   - `firstMeasurement`: PDF pp.16–17: first measurement lifted to distinct ancillary factor D'.
--   - `secondMeasurement`: PDF pp.16–17: second measurement lifted to distinct ancillary factor D''.
--   - `inputXorMatrix`: PDF p.16: XOR a retained input word into the first n wires of fresh computer memory; the remaining w wires are untouched. This is a product of n CNOTs.
--   - `copyInputMatrix`: PDF p.16: the actual input-copy operator, with retained input first and fresh computation memory second. It does not clone an unknown quantum state.
--   - `majorityCode`: PDF p.11: strict majority, with an explicit failure flag when no majority exists. The final bit is true exactly when a majority was found.
--   - `majorityTail`: PDF p.11: binomial upper tail includes ties (2j >= r).
--   - `amplificationRate`: PDF p.11: the exponential rate for fixed base error epsilon.
--   - `repeatedMajorityLaw`: PDF p.11: the exact law of majority of independent computations on fresh memories. Only a classical input x is copied; no unknown quantum state is cloned.
--   - `cyclicFourierVector`: PDF p.21, equation (22): the source's positive-sign, normalized cyclic Fourier vector embedded in n residue qubits. q>=1 and q<=2^n are imposed by its uses.
--   - `outerMap`: Rank-one map |v><u|, used to construct the ideal partial maps (23) and (24).
--   - `cyclicFourierMatrix`: PDF p.21, equation (22): the cyclic QFT, with zero action outside its valid subspace. This is a partial-isometry matrix, not a claimed full-space unitary.
--   - `idealQ`: PDF p.21, equation (23): constructed linear extension |psi_a,0> -> |psi_a,a>. Its conjugate transpose is its inverse on the indicated range.
--   - `idealTswapped`: PDF p.21, equation (24), registers [Y,X]: |0,a> -> |psi_a,a>.
--   - `xorIntoSecond`: PDF p.21, equation (25): tau_n[X,Y] adds X into Y.
--   - `xorIntoFirst`: PDF p.21, equation (25): tau_n[Y,X] adds Y into X.
--   - `encodeNatural`: PDF p.4: explicit self-delimiting binary natural coding, with a unary length prefix. Its length is logarithmic in t+1, rather than unary in t.
--   - `encodeInteger`: PDF p.4: signed integer coding, preserving every integer entry exactly.
--   - `encodeBasis`: PDF p.4: a dimension-prefixed, column-major encoding of an integer basis matrix.
--   - `columnLattice`: PDF p.4: the subgroup generated by the columns, as a set of integer vectors.
--   - `IsLatticeBasis`: PDF p.4: independence of the k columns, hence a basis of its full-rank lattice.
--   - `IsCanonicalBasis`: PDF p.4, equation (1): canonical upper triangular COLUMN basis for the same subgroup. The above-diagonal entry is reduced modulo m_ii, not m_jj.
--   - `canonicalBasis`: PDF p.4: the uniquely specified canonical matrix, with an explicit zero fallback on invalid inputs. The following theorem proves existence and uniqueness on every valid input.
--   - `discreteLogInput`: PDF p.4, example 2: a primitive root and unit are encoded by their unique residues, followed by the supplied rank-two lattice basis.
--   - `phaseDistance`: PDF pp.16,18: distance of real phases modulo one, in [0,1/2].
--   - `encodeRational`: PDF p.18: normalized rational-phase output coding.
--   - `rationalRecoveryInput`: PDF p.18: a dyadic measurement word has exactly 2n+1 bits, even when its numerator has leading zeros. Unary n and this fixed width make the input length O(n+1).
--   - `PartialUnitary.matrix`: PDF pp.12–13: matrix of the partial isometry, zero on the orthogonal complement. It remains a partial gate: ValidPartialExecution checks every call's intended domain.
--   - `PartialOracleStep`: PDF p.13: a Q operation or one plain call of a named n-wire partial oracle. There is no free controlled call and no free inverse oracle.
--   - `PartialOracleStep.matrix`: PDF p.13: lift the known operation or the partial oracle to its ordered distinct wires.
--   - `partialOracleMatrix`: PDF p.13: chronological operation list, with the oracle supplied only to the evaluator.
--   - `partialOracleCount`: PDF p.13: syntactic plain-oracle count, including calls whose matrix happens to be Q.
--   - `ValidPartialExecution`: PDF pp.12–13: each partial call is defined on the entire incoming vector, including entanglement with other wires. For the zero-extended isometry this is equivalent to norm preservation at that call, hence to membership in its lifted domain.
--   - `ControlledDomain`: PDF p.13, equation (13): the two control slices must both belong to N. The controlled range is |0>N direct-sum |1>M, not B^1 tensor M when N differs from M.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, https://arxiv.org/abs/quant-ph/9511026v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01

/-!
Statements from Kitaev, quant-ph/9511026v1. All page references are PDF pages.
Paper-local interfaces have complete bodies; target proofs are deliberately omitted.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.3: an action on a uniquely encoded subset, with no membership algorithm.
The total black box has unrestricted behavior outside M. -/
structure ASPAction (k n : ℕ) (M : Set (Qubits n)) where
  run : (Fin k → ℤ) → Qubits n → Qubits n
  preserves : ∀ g x, x ∈ M → run g x ∈ M
  zero : ∀ x, x ∈ M → run 0 x = x
  add : ∀ g h x, x ∈ M → run (g + h) x = run g (run h x)

/-- PDF pp.3–4: the stabilizer is constructed from the action and the given point. -/
def stabilizer {k n : ℕ} {M : Set (Qubits n)} (A : ASPAction k n M)
    (a : Qubits n) (ha : a ∈ M) : AddSubgroup (Fin k → ℤ) where
  carrier := {g | A.run g a = a}
  zero_mem' := A.zero a ha
  add_mem' := by
    intro g h hg hh
    change A.run (g + h) a = a
    rw [A.add g h a ha, hh, hg]
  neg_mem' := by
    intro g hg
    change A.run (-g) a = a
    have h := A.add (-g) g a ha
    rw [neg_add_cancel, A.zero a ha, hg] at h
    exact h.symm

/-- PDF p.3, reasonable coding: one sign bit and a self-delimited binary magnitude.
This explicit length differs by a constant factor from ordinary signed integer coding. -/
def integerBits (z : ℤ) : ℕ := 2 * (Nat.log2 (z.natAbs + 1) + 1) + 1

/-- PDF p.4: total bit length of the columns of an additive lattice basis. -/
def latticeBasisBits {k : ℕ} {S : AddSubgroup (Fin k → ℤ)}
    (b : (Fin k → ℤ) ≃+ S) : ℕ :=
  ∑ i, ∑ j, integerBits ((b (Pi.single i (1 : ℤ))).val j)

example : integerBits 0 = 3 := by decide

example {k n : ℕ} {M : Set (Qubits n)} (A : ASPAction k n M)
    (a : Qubits n) (ha : a ∈ M) : (0 : Fin k → ℤ) ∈ stabilizer A a ha :=
  (stabilizer A a ha).zero_mem

/-- PDF p.4, example 1: the integer-power action on the residue ring. -/
def orderAction {q : ℕ} (g : (ZMod q)ˣ) (m : ℤ) (x : ZMod q) : ZMod q :=
  ((g ^ m : (ZMod q)ˣ) : ZMod q) * x

example {q : ℕ} (g : (ZMod q)ˣ) (x : ZMod q) : orderAction g 0 x = x := by
  simp [orderAction]

/-- PDF p.11: Toffoli, with controls on the first two wires. -/
def andTau : Gate :=
  ⟨3, fun y x => if y = ![x 0, x 1, xor (x 2) (x 0 && x 1)] then 1 else 0⟩

/-- PDF p.8: the XOR lift of NOT, distinct from the single-wire NOT. -/
def notTau : Gate := Gate.ofMatrix2
  (fun y x => if y = (x.1, xor x.2 (!x.1)) then 1 else 0)

/-- PDF p.8: C_tau includes copy/XOR in addition to the XOR lifts of NOT and AND. -/
def cTauBasis : Set Gate := {notTau, andTau, Gate.ofMatrix2 cnot}

/-- PDF p.8: the classical reversible basis R. -/
def rBasis : Set Gate := {Gate.ofMatrix1 pauliX, Gate.ofMatrix2 cnot, andTau}

/-- PDF p.11: all one-qubit unitaries, CNOT and Toffoli; not a finite gate set. -/
def kitaevGateBasis : Set Gate :=
  {g | g.arity = 1 ∧ g.IsUnitary} ∪ {Gate.ofMatrix2 cnot, andTau}

/-- PDF p.13, Definition 4: frozen clean padding leaves a zero-width register unchanged. -/
example (v : EuclideanSpace ℂ (Qubits 0)) (z : Qubits 0) : cleanVector 0 v z = v z := by
  simp [QAlgorithms.Papers.Independent.Renew46.P01.cleanVector]

example (x : Qubits 3) : andTau.mat ![x 0, x 1, xor (x 2) (x 0 && x 1)] x = 1 := by
  simp [andTau]

/-- PDF pp.10,15: finite orthogonal families, encoded by their orthogonal projectors.
No completeness assumption is imposed. Zero projectors are harmless. -/
structure OrthogonalProjectorFamily (I : Type*) [Fintype I] [DecidableEq I] (r : ℕ) where
  proj : Fin r → Matrix I I ℂ
  hermitian : ∀ v, (proj v).IsHermitian
  idempotent : ∀ v, proj v * proj v = proj v
  orthogonal : ∀ v u, v ≠ u → proj v * proj u = 0

/-- PDF pp.10,15: projection onto the measured support N. -/
def OrthogonalProjectorFamily.support {I : Type*} [Fintype I] [DecidableEq I] {r : ℕ}
    (O : OrthogonalProjectorFamily I r) : Matrix I I ℂ := ∑ v, O.proj v

/-- PDF p.9, equation (8): Born probability for a subspace projector. -/
def subspaceProbability {I : Type*} [Fintype I] (rho P : Matrix I I ℂ) : ℝ :=
  (rho * P).trace.re

example {I : Type*} [Fintype I] (rho : Matrix I I ℂ) :
    subspaceProbability rho 0 = 0 := by simp [subspaceProbability]

/-- PDF p.11, Definition 3: the output register, rather than the whole memory,
is measured. Inputs outside the promise are unconstrained. -/
def Computes {n m w : ℕ} (U : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
    (out : Fin m ↪ Fin (n + w)) (N : Set (Qubits n)) (F : Qubits n → Qubits m)
    (epsilon : ℝ) : Prop :=
  ∀ x ∈ N, 1 - epsilon ≤ probEvent (act U (inputState x w)) (fun z => z ∘ out = F x)

example {n m w : ℕ} (U : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
    (out : Fin m ↪ Fin (n + w)) (F : Qubits n → Qubits m) (e : ℝ) :
    Computes U out ∅ F e := by simp [Computes]

/-- PDF p.12: a genuine partial unitary is an isometry equivalence between subspaces. -/
structure PartialUnitary (I : Type*) [Fintype I] where
  domain : Submodule ℂ (EuclideanSpace ℂ I)
  range : Submodule ℂ (EuclideanSpace ℂ I)
  iso : domain ≃ₗᵢ[ℂ] range

/-- PDF p.12: partial inverse, with domain and range swapped. -/
def PartialUnitary.inverse {I : Type*} [Fintype I] (U : PartialUnitary I) : PartialUnitary I :=
  ⟨U.range, U.domain, U.iso.symm⟩

/-- PDF p.12: precision on the intended domain, including BOTH subspace inclusions.
The printed undefined A is read as U_tilde, as forced by the preceding definition. -/
def PartialApprox {I : Type*} [Fintype I] (V U : PartialUnitary I) (delta : ℝ) : Prop :=
  ∃ hdom : U.domain ≤ V.domain, U.range ≤ V.range ∧
    ∀ (x : EuclideanSpace ℂ I) (hx : x ∈ U.domain),
      ‖(V.iso ⟨x, hdom hx⟩ : EuclideanSpace ℂ I) -
        (U.iso ⟨x, hx⟩ : EuclideanSpace ℂ I)‖ ≤ delta * ‖x‖

/-- A total evaluation helper for a partial unitary, using projection onto its domain.
It is NOT asserted to be a full unitary. Only valid-domain evaluations are used below. -/
def PartialUnitary.apply {I : Type*} [Fintype I] (U : PartialUnitary I)
    (x : EuclideanSpace ℂ I) : EuclideanSpace ℂ I :=
  (U.iso (U.domain.orthogonalProjectionOnto x) : EuclideanSpace ℂ I)

/-- PDF p.12: a compatible sequence is evaluated in chronological order. -/
def partialRun {I : Type*} [Fintype I] (us : List (PartialUnitary I))
    (x : EuclideanSpace ℂ I) : EuclideanSpace ℂ I :=
  us.foldl (fun v U => U.apply v) x

example {I : Type*} [Fintype I] (x : EuclideanSpace ℂ I) : partialRun [] x = x := rfl

/-- PDF p.12: the full precision relation for two valid partial-operation sequences
on specified initial domains. Besides the vector bound, both the initial-domain and
composite-range inclusions are required. Validity of both chains is supplied by uses. -/
def PartialSequenceApprox {I : Type*} [Fintype I]
    (V U : List (PartialUnitary I))
    (N Ntilde : Submodule ℂ (EuclideanSpace ℂ I)) (delta : ℝ) : Prop :=
  N ≤ Ntilde ∧
    (∀ x ∈ N, ∃ y ∈ Ntilde, partialRun U x = partialRun V y) ∧
    ∀ x ∈ N, ‖partialRun V x - partialRun U x‖ ≤ delta * ‖x‖

example {I : Type*} [Fintype I] (N : Submodule ℂ (EuclideanSpace ℂ I)) :
    PartialSequenceApprox [] [] N N 0 := by
  refine ⟨le_rfl, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · intro x hx
    simp [partialRun]

/-- PDF p.14: the exactly represented finite binary angle, first bit of weight 1/2. -/
def binaryAngle {b : ℕ} (x : Qubits b) : ℝ :=
  2 * Real.pi * ∑ i : Fin b, if x i then 1 / (2 : ℝ) ^ (i.val + 1) else 0

/-- PDF p.14: |x> tensored with the real rotation of |0>. -/
def rotatedZero {b : ℕ} (x : Qubits b) : EuclideanSpace ℂ (Qubits (b + 1)) :=
  WithLp.toLp 2 fun z => if Fin.init z = x then
    (if z (Fin.last b) then (Real.sin (binaryAngle x) : ℂ)
      else (Real.cos (binaryAngle x) : ℂ)) else 0

example : binaryAngle (fun _ : Fin 0 => false) = 0 := by simp [binaryAngle]

/-- PDF p.14: the Bell state produced by copying a Hadamard bit with CNOT. -/
def randomBitBell : EuclideanSpace ℂ (Bool × Bool) :=
  act cnot (tensorVec (act hadamard (ket false)) (ket false))

/-- PDF pp.14–15: the physical output when basis input x produces (G(x),g(x)). -/
def garbageState {I J K : Type*} [Fintype I] [DecidableEq J] [DecidableEq K]
    (G : I → J) (g : I → K) (c : EuclideanSpace ℂ I) : EuclideanSpace ℂ (J × K) :=
  ∑ x, c x • ket (G x, g x)

/-- PDF pp.14–15: the ideal coherent image before discarding work. -/
def coherentImage {I J : Type*} [Fintype I] [DecidableEq J]
    (G : I → J) (c : EuclideanSpace ℂ I) : EuclideanSpace ℂ J := ∑ x, c x • ket (G x)

/-- PDF p.16: the eigenphase ancilla block H diag(1,lambda) H. -/
def phaseAncilla (phi : ℝ) : Matrix Bool Bool ℂ :=
  hadamard * Matrix.diagonal (fun b : Bool => if b then Complex.exp (2 * Real.pi * phi * Complex.I)
    else 1) * hadamard

/-- PDF p.16, equation (16): H, controlled U, H; target is the second factor. -/
def eigenphaseTest {I : Type*} [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) :
    Matrix (Bool × I) (Bool × I) ℂ :=
  (hadamard ⊗ₖ (1 : Matrix I I ℂ)) * controlled U * (hadamard ⊗ₖ (1 : Matrix I I ℂ))

/-- PDF p.15, Definition 5: measurement operator on N tensor D, extended by identity
on the unmeasured orthogonal complement. This extension is also used in Theorem 2. -/
def measurementMatrix {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {r : ℕ} (O : OrthogonalProjectorFamily I r) (V : Fin r → Matrix J J ℂ) : Matrix (I × J) (I × J) ℂ :=
  (∑ v, O.proj v ⊗ₖ V v) + ((1 - O.support) ⊗ₖ (1 : Matrix J J ℂ))

/-- PDF p.15: conditional probability, with ordered output wires C and zero work D. -/
def eigenspaceOutcomeProbability {r d m : ℕ} (V : Fin r → Matrix (Qubits d) (Qubits d) ℂ)
    (C : Fin m ↪ Fin d) (v : Fin r) (y : Qubits m) : ℝ :=
  probEvent (act (V v) (zeroKet d)) (fun z => z ∘ C = y)

/-- PDF pp.16–17: first measurement lifted to distinct ancillary factor D'. -/
def firstMeasurement {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] {r : ℕ}
    (O : OrthogonalProjectorFamily I r) (V : Fin r → Matrix J J ℂ) : Matrix (I × (J × K)) (I × (J × K)) ℂ :=
  measurementMatrix O (fun v => V v ⊗ₖ (1 : Matrix K K ℂ))

/-- PDF pp.16–17: second measurement lifted to distinct ancillary factor D''. -/
def secondMeasurement {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] {r : ℕ}
    (O : OrthogonalProjectorFamily I r) (V : Fin r → Matrix K K ℂ) : Matrix (I × (J × K)) (I × (J × K)) ℂ :=
  measurementMatrix O (fun v => (1 : Matrix J J ℂ) ⊗ₖ V v)

example {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    measurementMatrix (I := I) (J := J)
      (⟨Fin.elim0, by intro v; exact Fin.elim0 v, by intro v; exact Fin.elim0 v,
        by intro v; exact Fin.elim0 v⟩ : OrthogonalProjectorFamily I 0) Fin.elim0 = 1 := by
  simp [measurementMatrix, OrthogonalProjectorFamily.support, Matrix.one_kronecker_one]

/-- PDF p.16: XOR a retained input word into the first n wires of fresh
computer memory; the remaining w wires are untouched. This is a product of n CNOTs. -/
def inputXorMatrix {n : ℕ} (w : ℕ) (x : Qubits n) :
    Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ :=
  fun y z => if y = (fun i => xor (z i) (Fin.append x (fun _ : Fin w => false) i))
    then 1 else 0

/-- PDF p.16: the actual input-copy operator, with retained input first and
fresh computation memory second. It does not clone an unknown quantum state. -/
def copyInputMatrix (n w : ℕ) :
    Matrix (Qubits n × Qubits (n + w)) (Qubits n × Qubits (n + w)) ℂ :=
  fun y z => if y.1 = z.1 then inputXorMatrix w z.1 y.2 z.2 else 0

example {n : ℕ} (w : ℕ) (x : Qubits n) (z : Qubits (n + w)) :
    inputXorMatrix w x
      (fun i => xor (z i) (Fin.append x (fun _ : Fin w => false) i)) z = 1 := by
  simp [inputXorMatrix]

/-- PDF p.11: strict majority, with an explicit failure flag when no majority exists.
The final bit is true exactly when a majority was found. -/
def majorityCode {r m : ℕ} (ys : Fin r → Qubits m) : Qubits (m + 1) :=
  if h : ∃ y : Qubits m, r < 2 * (Finset.univ.filter (fun i => ys i = y)).card then
    Fin.snoc h.choose true else Fin.snoc (fun _ => false) false

/-- PDF p.11: binomial upper tail includes ties (2j >= r). -/
def majorityTail (r : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (r + 1)).filter (fun j => r ≤ 2 * j),
    (Nat.choose r j : ℝ) * epsilon ^ j * (1 - epsilon) ^ (r - j)

/-- PDF p.11: the exponential rate for fixed base error epsilon. -/
def amplificationRate (epsilon : ℝ) : ℝ := 2 * Real.sqrt (epsilon * (1 - epsilon))

/-- PDF p.11: the exact law of majority of independent computations on fresh memories.
Only a classical input x is copied; no unknown quantum state is cloned. -/
def repeatedMajorityLaw {n m w : ℕ}
    (U : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
    (out : Fin m ↪ Fin (n + w)) (r : ℕ) (x : Qubits n) (y : Qubits (m + 1)) : ℝ :=
  ∑ ys : Fin r → Qubits m, if majorityCode ys = y then
    ∏ i, probEvent (act U (inputState x w)) (fun z => z ∘ out = ys i) else 0

example (ys : Fin 0 → Qubits 1) : majorityCode ys (Fin.last 1) = false := by
  unfold majorityCode
  split
  next h => simp at h
  next => rw [Fin.snoc_last]

/-- PDF p.21, equation (22): the source's positive-sign, normalized cyclic Fourier vector
embedded in n residue qubits. q>=1 and q<=2^n are imposed by its uses. -/
def cyclicFourierVector (n q : ℕ) (a : Fin q) : EuclideanSpace ℂ (Qubits n) :=
  ∑ b : Fin q, qftMatrix q b a • ket (natToBits n b.val)

/-- Rank-one map |v><u|, used to construct the ideal partial maps (23) and (24). -/
def outerMap {I : Type*} (v u : EuclideanSpace ℂ I) : Matrix I I ℂ :=
  fun i j => v i * conj (u j)

/-- PDF p.21, equation (22): the cyclic QFT, with zero action outside its valid subspace.
This is a partial-isometry matrix, not a claimed full-space unitary. -/
def cyclicFourierMatrix (n q : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ a : Fin q, outerMap (cyclicFourierVector n q a) (ket (natToBits n a.val))

/-- PDF p.21, equation (23): constructed linear extension |psi_a,0> -> |psi_a,a>.
Its conjugate transpose is its inverse on the indicated range. -/
def idealQ (n q : ℕ) : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  ∑ a : Fin q, outerMap
    (tensorVec (cyclicFourierVector n q a) (ket (natToBits n a.val)))
    (tensorVec (cyclicFourierVector n q a) (zeroKet n))

/-- PDF p.21, equation (24), registers [Y,X]: |0,a> -> |psi_a,a>. -/
def idealTswapped (n q : ℕ) : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  ∑ a : Fin q, outerMap
    (tensorVec (cyclicFourierVector n q a) (ket (natToBits n a.val)))
    (tensorVec (zeroKet n) (ket (natToBits n a.val)))

/-- PDF p.21, equation (25): tau_n[X,Y] adds X into Y. -/
def xorIntoSecond (n : ℕ) : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  fun y x => if y = (x.1, fun i => xor (x.2 i) (x.1 i)) then 1 else 0

/-- PDF p.21, equation (25): tau_n[Y,X] adds Y into X. -/
def xorIntoFirst (n : ℕ) : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  fun y x => if y = ((fun i => xor (x.1 i) (x.2 i)), x.2) then 1 else 0

example (n : ℕ) : cyclicFourierVector n 1 0 = ket (natToBits n 0) := by
  simp [cyclicFourierVector, qftMatrix, Fin.sum_univ_one]

/-- PDF p.4: explicit self-delimiting binary natural coding, with a unary length prefix.
Its length is logarithmic in t+1, rather than unary in t. -/
def encodeNatural (t : ℕ) : List Bool :=
  let bs := Nat.bits (t + 1)
  List.replicate bs.length true ++ [false] ++ bs

/-- PDF p.4: signed integer coding, preserving every integer entry exactly. -/
def encodeInteger (z : ℤ) : List Bool := decide (z < 0) :: encodeNatural z.natAbs

/-- PDF p.4: a dimension-prefixed, column-major encoding of an integer basis matrix. -/
def encodeBasis {k : ℕ} (B : Matrix (Fin k) (Fin k) ℤ) : List Bool :=
  encodeNatural k ++ ((List.ofFn fun j =>
    (List.ofFn fun i => encodeInteger (B i j)).flatten).flatten)

/-- PDF p.4: the subgroup generated by the columns, as a set of integer vectors. -/
def columnLattice {k : ℕ} (B : Matrix (Fin k) (Fin k) ℤ) : Set (Fin k → ℤ) :=
  Set.range (fun c => B.mulVec c)

/-- PDF p.4: independence of the k columns, hence a basis of its full-rank lattice. -/
def IsLatticeBasis {k : ℕ} (B : Matrix (Fin k) (Fin k) ℤ) : Prop :=
  Function.Injective (fun c => B.mulVec c)

/-- PDF p.4, equation (1): canonical upper triangular COLUMN basis for the same subgroup.
The above-diagonal entry is reduced modulo m_ii, not m_jj. -/
def IsCanonicalBasis {k : ℕ} (B C : Matrix (Fin k) (Fin k) ℤ) : Prop :=
  IsLatticeBasis C ∧ columnLattice C = columnLattice B ∧
  (∀ i j, j < i → C i j = 0) ∧ (∀ i, 0 < C i i) ∧
  (∀ i j, i < j → 0 ≤ C i j ∧ C i j < C i i)

/-- PDF p.4: the uniquely specified canonical matrix, with an explicit zero fallback
on invalid inputs. The following theorem proves existence and uniqueness on every valid input. -/
def canonicalBasis {k : ℕ} (B : Matrix (Fin k) (Fin k) ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  if h : ∃ C, IsCanonicalBasis B C then h.choose else 0

example : encodeNatural 0 = [true, false, true] := rfl

example : encodeInteger 0 = [false, true, false, true] := rfl

/-- PDF p.4, example 2: a primitive root and unit are encoded by their unique residues,
followed by the supplied rank-two lattice basis. -/
def discreteLogInput (q : ℕ) (zeta g : (ZMod q)ˣ) (B : Matrix (Fin 2) (Fin 2) ℤ) : List Bool :=
  encodeNatural q ++ encodeNatural (zeta : ZMod q).val ++
    encodeNatural (g : ZMod q).val ++ encodeBasis B

/-- PDF pp.16,18: distance of real phases modulo one, in [0,1/2]. -/
def phaseDistance (x y : ℝ) : ℝ := min (Int.fract (x - y)) (1 - Int.fract (x - y))

/-- PDF p.18: normalized rational-phase output coding. -/
def encodeRational (r : ℚ) : List Bool := encodeInteger r.num ++ encodeNatural r.den

/-- PDF p.18: a dyadic measurement word has exactly 2n+1 bits, even when its numerator
has leading zeros. Unary n and this fixed width make the input length O(n+1). -/
def rationalRecoveryInput (n numerator : ℕ) : List Bool :=
  List.replicate n true ++ [false] ++ List.ofFn (natToBits (2 * n + 1) numerator)

example (x : ℝ) : phaseDistance x x = 0 := by simp [phaseDistance]

/-- PDF pp.12–13: matrix of the partial isometry, zero on the orthogonal complement.
It remains a partial gate: ValidPartialExecution checks every call's intended domain. -/
def PartialUnitary.matrix {I : Type*} [Fintype I] [DecidableEq I] (U : PartialUnitary I) :
    Matrix I I ℂ := fun i j => U.apply (ket j) i

/-- PDF p.13: a Q operation or one plain call of a named n-wire partial oracle.
There is no free controlled call and no free inverse oracle. -/
inductive PartialOracleStep (n total : ℕ) where
  | known (g : GateApp kitaevGateBasis total)
  | call (wires : Fin n ↪ Fin total)

/-- PDF p.13: lift the known operation or the partial oracle to its ordered distinct wires. -/
def PartialOracleStep.matrix {n total : ℕ} (U : PartialUnitary (Qubits n)) :
    PartialOracleStep n total → Matrix (Qubits total) (Qubits total) ℂ
  | .known g => embedOp g.gate.mat g.wires
  | .call wires => embedOp U.matrix wires

/-- PDF p.13: chronological operation list, with the oracle supplied only to the evaluator. -/
def partialOracleMatrix {n total : ℕ} (c : List (PartialOracleStep n total))
    (U : PartialUnitary (Qubits n)) : Matrix (Qubits total) (Qubits total) ℂ :=
  (c.map (PartialOracleStep.matrix U)).reverse.prod

/-- PDF p.13: syntactic plain-oracle count, including calls whose matrix happens to be Q. -/
def partialOracleCount {n total : ℕ} (c : List (PartialOracleStep n total)) : ℕ :=
  c.countP (fun s => match s with | .known _ => false | .call _ => true)

/-- PDF pp.12–13: each partial call is defined on the entire incoming vector, including
entanglement with other wires. For the zero-extended isometry this is equivalent to norm
preservation at that call, hence to membership in its lifted domain. -/
def ValidPartialExecution {n total : ℕ} (c : List (PartialOracleStep n total))
    (U : PartialUnitary (Qubits n)) (v : EuclideanSpace ℂ (Qubits total)) : Prop :=
  ∀ j : Fin c.length, match c.get j with
    | .known _ => True
    | .call wires =>
      let incoming := act (partialOracleMatrix (c.take j.val) U) v
      ‖act (embedOp U.matrix wires) incoming‖ = ‖incoming‖

/-- PDF p.13, equation (13): the two control slices must both belong to N.
The controlled range is |0>N direct-sum |1>M, not B^1 tensor M when N differs from M. -/
def ControlledDomain {n : ℕ} (U : PartialUnitary (Qubits n))
    (v : EuclideanSpace ℂ (Qubits (n + 1))) : Prop :=
  ∀ b : Bool, (WithLp.toLp 2 (fun x : Qubits n => v (Fin.cons b x))) ∈ U.domain

example {n total : ℕ} (U : PartialUnitary (Qubits n)) :
    partialOracleMatrix ([] : List (PartialOracleStep n total)) U = 1 := rfl

example {n total : ℕ} : partialOracleCount ([] : List (PartialOracleStep n total)) = 0 := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P03


