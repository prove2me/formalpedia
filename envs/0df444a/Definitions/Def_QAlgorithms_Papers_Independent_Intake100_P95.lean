-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95
-- name    : QAlgorithms_Papers_Independent_Intake100_P95
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T15:45:55.404018+00:00
-- url     : https://prove2.me/theorems/adc60ced-16a1-440c-b419-2a6d78224615
-- title:
--   Definitions for Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks
-- statement:
--   The objects the formalized statements of *Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks* (arXiv:quant-ph/0610061) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `LocalSU`
--   - `localMatrix`: The actual local special-unitary matrix, PDF p.3.
--   - `adjointConjugation`: Conjugation, specialized to unitaries whenever inverse means dagger.
--   - `localAd`: Local adjoint action, PDF pp.3–4.
--   - `IsHamiltonian`: Hermitian traceless Hamiltonian, iH in su(2^n); PDF p.3.
--   - `TypeI`: One local K precedes the universal time quantifier; PDF pp.2,4.
--   - `embeddedPauli`: A single embedded Pauli matrix, identities at all other positions; (27).
--   - `IsLocalHamiltonian`: Hermitian local generators, identified with the skew algebra by -i; p.3.
--   - `CentralizerPerp`: Intrinsic real orthocomplement of the traceless Hermitian centralizer; PDF p.3, (6)–(8), interpreted through the Hermitian/skew identification.
--   - `productEigenoperator`: Tensor outer products of one-qubit eigenvectors; PDF p.4.
--   - `productEigenvalue`: Exact product eigenvalue, including all branch choices in (23).
--   - `SelectedPairs`: The genuinely selected -1 branch, not the erroneous subtype unions.
--   - `collectiveZ`: Collective F_z=sum Z_l/2, (27), (34), (86).
--   - `individualZRotation`: Independent local z angles, (38).
--   - `jointZ`: Joint z-rotation, (35).
--   - `OddPi`: Odd-pi congruence uses integer lifts, with no real-modulo convention.
--   - `HasOrder`: Quantum order through the commutator in (32).
--   - `tensorFactor`: 1, J_z, J_+, J_- from (32),(37); raising is (X+iY)/2.
--   - `factorOrder`: Orders of 1,J_z,J_+,J_- are 0,0,+1,-1.
--   - `tensorMonomial`: Tensor monomial (37), not necessarily Hermitian.
--   - `tensorOperatorSum`: Linear combinations in (40) may have repeated terms or zero coefficients.
--   - `orderMatrix`: Real order matrix in (40).
--   - `supportComponent`: Canonical full Pauli expansion grouped by exact support; (28).
--   - `xyz`: Two-qubit diagonal interaction a XX+b YY+c ZZ, (24).
--   - `axisPulse`: Axis pulse exp(-i theta sigma_axis/2), Table II.
--   - `pairPauli`: Pair Pauli embedding, identities on all remaining qubits; (25),(26).
--   - `couplingGraph`: Real couplings are specified only for k<l; adjacency ignores unused entries.
--   - `BipartiteCouplings`: Bipartiteness by a two-coloring; weights may be positive or negative.
--   - `isingZZ`: Ising coupling Hamiltonian, including the source's pi/2 factor, (25).
--   - `networkXY`: Uniform anisotropy kappa, endpoints included; (26).
--   - `entryOrder`: Row Z/2 weight minus column Z/2 weight, fixing the sign in (45),(50).
--   - `matrixUnitSum`: Linear combination of matrix units (51).
--   - `torus`: Weyl-torus representative; the angles sum to zero at use, (47).
--   - `concurrenceInvolution`: The concurrence Cartan involution (57), including conjugation.
--   - `distanceSq`: Squared distance objective; no default matrix norm, (63).
--   - `reversalOverlap`: Negative real trace overlap to maximize, (64).
--   - `toLocalIndex`: Basis relabelling Bool to Fin 2 for the accepted local Lie algebra, PDF p.11. No wire order is changed.
--   - `fromLocalIndex`: Inverse basis relabelling, PDF p.11.
--   - `localSkewProjection`: The accepted real Hilbert--Schmidt local projection with only a basis relabelling; PDF p.11, (65). The accepted Y-generator has opposite sign, which cancels between its real coefficient and generator.
--   - `localNumericalRange`: Formula (69), for arbitrary complex A,C.
--   - `realVec`: Column-stacked real and imaginary coordinates, (71).
--   - `realRepresentation`: Real representation of a complex-linear superoperator, (75).
--   - `adjoiningReal`: Real matrix of adjoining, diag(transpose,-transpose), (72)–(74).
--   - `twoSidedDistanceSq`: Two-sided distance, testing all local pairs, (4),(80).
--   - `twoSidedObjective`: The minimization objective in (81), with its printed minus sign.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, https://arxiv.org/abs/quant-ph/0610061v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

/-! Statements from quant-ph/0610061v1. Qubit 0 is the most significant bit.
All norms explicitly called `frobNorm` are Frobenius norms. Local operations
are products of independent SU(2) factors, with no wire permutations.
Theorems are statements only; compilation is delegated to the batch worker. -/

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)
open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)
open QAlgorithms.Papers.Independent.Information100.P10 (pauli)
open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

abbrev LocalSU (n : ℕ) := Fin n → Matrix.specialUnitaryGroup Bool ℂ

/-- The actual local special-unitary matrix, PDF p.3. -/
def localMatrix {n : ℕ} (K : LocalSU n) : Op (QAlgorithms.Qubits n) :=
  QAlgorithms.kronAll (fun l => (K l : Matrix Bool Bool ℂ))

/-- Conjugation, specialized to unitaries whenever inverse means dagger. -/
def adjointConjugation {ι : Type*} [Fintype ι] (K A : Matrix ι ι ℂ) :=
  K * A * K.conjTranspose

/-- Local adjoint action, PDF pp.3–4. -/
def localAd {n : ℕ} (K : LocalSU n) (A : Op (QAlgorithms.Qubits n)) : Op (QAlgorithms.Qubits n) :=
  adjointConjugation (localMatrix K) A

/-- Hermitian traceless Hamiltonian, iH in su(2^n); PDF p.3. -/
def IsHamiltonian {n : ℕ} (H : Op (QAlgorithms.Qubits n)) : Prop :=
  H.IsHermitian ∧ Matrix.trace H = 0

/-- One local K precedes the universal time quantifier; PDF pp.2,4. -/
def TypeI {n : ℕ} (H : Op (QAlgorithms.Qubits n)) : Prop :=
  ∃ K : LocalSU n, ∀ t : ℝ, localAd K (evolution H t) = evolution H (-t)

/-- A single embedded Pauli matrix, identities at all other positions; (27). -/
def embeddedPauli {n : ℕ} (k : Fin n) (a : Fin 3) : Op (QAlgorithms.Qubits n) :=
  QAlgorithms.kronAll (fun l => if l = k then pauli a else 1)

/-- Hermitian local generators, identified with the skew algebra by -i; p.3. -/
def IsLocalHamiltonian {n : ℕ} (k : Op (QAlgorithms.Qubits n)) : Prop :=
  ∃ c : Fin n → Fin 3 → ℝ, k = ∑ l, ∑ a, (c l a : ℂ) • embeddedPauli l a

/-- Intrinsic real orthocomplement of the traceless Hermitian centralizer;
PDF p.3, (6)–(8), interpreted through the Hermitian/skew identification. -/
def CentralizerPerp {n : ℕ} (H k : Op (QAlgorithms.Qubits n)) : Prop :=
  ∀ A : Op (QAlgorithms.Qubits n), IsHamiltonian A → comm A H = 0 → realHSPairing k A = 0

/-- Tensor outer products of one-qubit eigenvectors; PDF p.4. -/
def productEigenoperator {n : ℕ} (V : Fin n → Matrix.unitaryGroup Bool ℂ)
    (a b : QAlgorithms.Qubits n) : Op (QAlgorithms.Qubits n) :=
  fun i j =>
    QAlgorithms.kronAll (fun l => (V l : Matrix Bool Bool ℂ)) i a *
      star (QAlgorithms.kronAll (fun l => (V l : Matrix Bool Bool ℂ)) j b)

/-- Exact product eigenvalue, including all branch choices in (23). -/
def productEigenvalue {n : ℕ} (lam : Fin n → Bool → ℂ)
    (a b : QAlgorithms.Qubits n) : ℂ :=
  ∏ l, lam l (a l) * star (lam l (b l))

/-- The genuinely selected -1 branch, not the erroneous subtype unions. -/
def SelectedPairs {n : ℕ} (lam : Fin n → Bool → ℂ) :=
  {q : QAlgorithms.Qubits n × QAlgorithms.Qubits n //
    productEigenvalue lam q.1 q.2 = -1}

/-- Collective F_z=sum Z_l/2, (27), (34), (86). -/
def collectiveZ (n : ℕ) : Op (QAlgorithms.Qubits n) :=
  (1 / 2 : ℂ) • ∑ k : Fin n, embeddedPauli k 2

/-- Independent local z angles, (38). -/
def individualZRotation {n : ℕ} (phi : Fin n → ℝ) : Op (QAlgorithms.Qubits n) :=
  QAlgorithms.kronAll (fun l => QAlgorithms.Papers.Independent.Next46.P21.zRotation (phi l))

/-- Joint z-rotation, (35). -/
def jointZ (n : ℕ) (phi : ℝ) : Op (QAlgorithms.Qubits n) := individualZRotation (fun _ => phi)

/-- Odd-pi congruence uses integer lifts, with no real-modulo convention. -/
def OddPi (x : ℝ) : Prop := ∃ z : ℤ, x = (2 * (z : ℝ) + 1) * Real.pi

/-- Quantum order through the commutator in (32). -/
def HasOrder {n : ℕ} (T : Op (QAlgorithms.Qubits n)) (p : ℤ) : Prop :=
  comm (collectiveZ n) T = (p : ℂ) • T

/-- 1, J_z, J_+, J_- from (32),(37); raising is (X+iY)/2. -/
def tensorFactor (nu : Fin 4) : Matrix Bool Bool ℂ :=
  if nu = 0 then 1
  else if nu = 1 then (1 / 2 : ℂ) • QAlgorithms.pauliZ
  else if nu = 2 then (1 / 2 : ℂ) • (QAlgorithms.pauliX + Complex.I • QAlgorithms.pauliY)
  else (1 / 2 : ℂ) • (QAlgorithms.pauliX - Complex.I • QAlgorithms.pauliY)

/-- Orders of 1,J_z,J_+,J_- are 0,0,+1,-1. -/
def factorOrder (nu : Fin 4) : ℤ := if nu = 2 then 1 else if nu = 3 then -1 else 0

/-- Tensor monomial (37), not necessarily Hermitian. -/
def tensorMonomial {n : ℕ} (nu : Fin n → Fin 4) : Op (QAlgorithms.Qubits n) := QAlgorithms.kronAll (fun l => tensorFactor (nu l))

/-- Linear combinations in (40) may have repeated terms or zero coefficients. -/
def tensorOperatorSum {n m : ℕ} (nu : Fin m → Fin n → Fin 4) (c : Fin m → ℂ) : Op (QAlgorithms.Qubits n) :=
  ∑ a, c a • tensorMonomial (nu a)

/-- Real order matrix in (40). -/
def orderMatrix {n m : ℕ} (nu : Fin m → Fin n → Fin 4) : Matrix (Fin m) (Fin n) ℝ :=
  fun a l => (factorOrder (nu a l) : ℝ)

/-- Canonical full Pauli expansion grouped by exact support; (28). -/
def supportComponent {n : ℕ} (H : Op (QAlgorithms.Qubits n)) (S : Finset (Fin n)) : Op (QAlgorithms.Qubits n) :=
  ∑ s : Fin n → Fin 4, if wordSupport s = S then
    (((2 : ℂ) ^ n)⁻¹ * Matrix.trace ((wordMatrix s).conjTranspose * H)) • wordMatrix s
  else 0

/-- Two-qubit diagonal interaction a XX+b YY+c ZZ, (24). -/
def xyz (a b c : ℝ) : Op (QAlgorithms.Qubits 2) :=
  (a : ℂ) • QAlgorithms.kronAll (fun _ => QAlgorithms.pauliX) +
  (b : ℂ) • QAlgorithms.kronAll (fun _ => QAlgorithms.pauliY) +
  (c : ℂ) • QAlgorithms.kronAll (fun _ => QAlgorithms.pauliZ)

/-- Axis pulse exp(-i theta sigma_axis/2), Table II. -/
def axisPulse {n : ℕ} (a : Fin 3) (phi : Fin n → ℝ) : Op (QAlgorithms.Qubits n) :=
  QAlgorithms.kronAll (fun l => NormedSpace.exp ((-Complex.I * (phi l : ℂ) / 2) • pauli a))

/-- Pair Pauli embedding, identities on all remaining qubits; (25),(26). -/
def pairPauli {n : ℕ} (i j : Fin n) (a : Fin 3) : Op (QAlgorithms.Qubits n) :=
  QAlgorithms.kronAll (fun l => if l = i ∨ l = j then pauli a else 1)

/-- Real couplings are specified only for k<l; adjacency ignores unused entries. -/
def couplingGraph {n : ℕ} (J : Fin n → Fin n → ℝ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ J (min i j) (max i j) ≠ 0
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by simpa [min_comm, max_comm] using h.2⟩⟩
  loopless := ⟨by
    intro i h
    exact h.1 rfl⟩

/-- Bipartiteness by a two-coloring; weights may be positive or negative. -/
def BipartiteCouplings {n : ℕ} (J : Fin n → Fin n → ℝ) : Prop :=
  ∃ color : Fin n → Bool, ∀ i j, (couplingGraph J).Adj i j → color i ≠ color j

/-- Ising coupling Hamiltonian, including the source's pi/2 factor, (25). -/
def isingZZ {n : ℕ} (J : Fin n → Fin n → ℝ) : Op (QAlgorithms.Qubits n) :=
  (Real.pi / 2 : ℂ) • ∑ i, ∑ j, if i < j then (J i j : ℂ) • pairPauli i j 2 else 0

/-- Uniform anisotropy kappa, endpoints included; (26). -/
def networkXY {n : ℕ} (J : Fin n → Fin n → ℝ) (kappa : ℝ) : Op (QAlgorithms.Qubits n) :=
  (Real.pi / 2 : ℂ) • ∑ i, ∑ j, if i < j then
    (J i j : ℂ) • (pairPauli i j 0 + (kappa : ℂ) • pairPauli i j 1) else 0

/-- Row Z/2 weight minus column Z/2 weight, fixing the sign in (45),(50). -/
def entryOrder {n : ℕ} (i j : QAlgorithms.Qubits n) (l : Fin n) : ℝ :=
  (if i l then (-1 / 2 : ℝ) else 1 / 2) - (if j l then (-1 / 2 : ℝ) else 1 / 2)

/-- Linear combination of matrix units (51). -/
def matrixUnitSum {n m : ℕ} (i j : Fin m → QAlgorithms.Qubits n) (c : Fin m → ℂ) : Op (QAlgorithms.Qubits n) :=
  ∑ a, c a • Matrix.single (i a) (j a) (1 : ℂ)

/-- Weyl-torus representative; the angles sum to zero at use, (47). -/
def torus {n : ℕ} (theta : QAlgorithms.Qubits n → ℝ) : Op (QAlgorithms.Qubits n) :=
  Matrix.diagonal (fun i => Complex.exp (-Complex.I * (theta i : ℂ)))

/-- The concurrence Cartan involution (57), including conjugation. -/
def concurrenceInvolution {n : ℕ} (A : Op (QAlgorithms.Qubits n)) : Op (QAlgorithms.Qubits n) :=
  adjointConjugation (QAlgorithms.kronAll (fun _ => (-Complex.I) • QAlgorithms.pauliY)) (fun i j => star (A i j))

/-- Squared distance objective; no default matrix norm, (63). -/
def distanceSq {n : ℕ} (H : Op (QAlgorithms.Qubits n)) (K : LocalSU n) : ℝ :=
  QAlgorithms.frobNorm (localAd K H + H) ^ 2

/-- Negative real trace overlap to maximize, (64). -/
def reversalOverlap {n : ℕ} (H : Op (QAlgorithms.Qubits n)) (K : Op (QAlgorithms.Qubits n)) : ℝ :=
  QAlgorithms.Papers.Independent.Advance50.P38.realTraceOverlap H (-H) K

/-- Basis relabelling Bool to Fin 2 for the accepted local Lie algebra, PDF p.11.
No wire order is changed. -/
def toLocalIndex {n : ℕ} (A : Op (QAlgorithms.Qubits n)) :
    Matrix (QAlgorithms.Papers.Independent.Advance50.P38.LocalQubitIndex n)
      (QAlgorithms.Papers.Independent.Advance50.P38.LocalQubitIndex n) ℂ :=
  fun i j => A (fun l => finTwoEquiv (i l)) (fun l => finTwoEquiv (j l))

/-- Inverse basis relabelling, PDF p.11. -/
def fromLocalIndex {n : ℕ}
    (A : Matrix (QAlgorithms.Papers.Independent.Advance50.P38.LocalQubitIndex n)
      (QAlgorithms.Papers.Independent.Advance50.P38.LocalQubitIndex n) ℂ) :
    Op (QAlgorithms.Qubits n) :=
  fun i j => A (fun l => finTwoEquiv.symm (i l)) (fun l => finTwoEquiv.symm (j l))

/-- The accepted real Hilbert--Schmidt local projection with only a basis relabelling;
PDF p.11, (65). The accepted Y-generator has opposite sign, which cancels
between its real coefficient and generator. -/
def localSkewProjection {n : ℕ} (A : Op (QAlgorithms.Qubits n)) :
    Op (QAlgorithms.Qubits n) :=
  fromLocalIndex (QAlgorithms.Papers.Independent.Advance50.P38.localProjection (toLocalIndex A))

example {n : ℕ} (A : Op (QAlgorithms.Qubits n)) :
    fromLocalIndex (toLocalIndex A) = A := by
  ext i j
  simp [fromLocalIndex, toLocalIndex]

example {n : ℕ} : localSkewProjection (0 : Op (QAlgorithms.Qubits n)) = 0 := by
  have hzero : toLocalIndex (0 : Op (QAlgorithms.Qubits n)) = 0 := rfl
  unfold localSkewProjection
  rw [hzero]
  simp only [QAlgorithms.Papers.Independent.Advance50.P38.localProjection,
    QAlgorithms.Papers.Independent.Advance50.P38.realHSPairing,
    Matrix.conjTranspose_zero, zero_mul, Matrix.trace_zero, Complex.zero_re,
    zero_smul, Finset.sum_const_zero, smul_zero]
  rfl

/-- Formula (69), for arbitrary complex A,C. -/
def localNumericalRange {n : ℕ} (C A : Op (QAlgorithms.Qubits n)) : Set ℂ :=
  Set.range (fun K : LocalSU n => Matrix.trace (C.conjTranspose * localAd K A))

/-- Column-stacked real and imaginary coordinates, (71). -/
def realVec {ι : Type*} (A : Matrix ι ι ℂ) : Bool × (ι × ι) → ℝ :=
  fun q => if q.1 then (Matrix.vec A q.2).im else (Matrix.vec A q.2).re

/-- Real representation of a complex-linear superoperator, (75). -/
def realRepresentation {ι : Type*} (B : Matrix ι ι ℂ) :
    Matrix (Bool × ι) (Bool × ι) ℝ :=
  fun i j => if i.1 then (if j.1 then (B i.2 j.2).re else (B i.2 j.2).im)
    else (if j.1 then -(B i.2 j.2).im else (B i.2 j.2).re)

/-- Real matrix of adjoining, diag(transpose,-transpose), (72)–(74). -/
def adjoiningReal {ι : Type*} [DecidableEq ι] :
    Matrix (Bool × (ι × ι)) (Bool × (ι × ι)) ℝ :=
  fun i j => if i.1 = j.1 ∧ i.2.1 = j.2.2 ∧ i.2.2 = j.2.1
    then (if i.1 then -1 else 1) else 0

/-- Two-sided distance, testing all local pairs, (4),(80). -/
def twoSidedDistanceSq {n : ℕ} (U : Op (QAlgorithms.Qubits n)) (K L : LocalSU n) : ℝ :=
  QAlgorithms.frobNorm (localMatrix K * U * localMatrix L - U.conjTranspose) ^ 2

/-- The minimization objective in (81), with its printed minus sign. -/
def twoSidedObjective {n : ℕ} (U : Op (QAlgorithms.Qubits n)) (K L : LocalSU n) : ℝ :=
  -(Matrix.trace (localMatrix K * U * localMatrix L * U)).re

example : tensorFactor 2 false true = 1 := by
  change (1 / 2 : ℂ) * (1 + Complex.I * (-Complex.I)) = 1
  norm_num [mul_neg, Complex.I_mul_I]

example : factorOrder 2 = 1 ∧ factorOrder 3 = -1 := by
  constructor <;> rfl

example {n : ℕ} : tensorOperatorSum (fun _ : Fin 0 => fun _ : Fin n => (0 : Fin 4))
    (fun a : Fin 0 => Fin.elim0 a) = 0 := by
  simp [tensorOperatorSum]

example (x : ℂ) : realRepresentation (fun _ _ : Unit => x)
    (false, ()) (true, ()) = -x.im := rfl

example (J : Fin 1 → Fin 1 → ℝ) : isingZZ J = 0 := by
  simp [isingZZ]

example {n : ℕ} (H : Op (QAlgorithms.Qubits n)) : evolution H 0 = 1 := by
  simp [evolution]

example (i j : QAlgorithms.Qubits 0) : QAlgorithms.kronAll (fun l : Fin 0 => Fin.elim0 l) i j = 1 := by
  simp [QAlgorithms.kronAll]

example : OddPi Real.pi := by
  exact ⟨0, by simp⟩

example {n : ℕ} (i j : QAlgorithms.Qubits n) : Matrix.single i j (1 : ℂ) i j = 1 := by
  simp

example {n : ℕ} : wordSupport (fun _ : Fin n => (0 : Fin 4)) = ∅ := by
  simp [wordSupport]

example {n : ℕ} (l : Fin n) :
    entryOrder (fun _ => false) (fun _ => true) l = 1 := by
  norm_num [entryOrder]

example {n : ℕ} (i : QAlgorithms.Qubits n × QAlgorithms.Qubits n) :
    (adjoiningReal : Matrix (Bool × (QAlgorithms.Qubits n × QAlgorithms.Qubits n))
      (Bool × (QAlgorithms.Qubits n × QAlgorithms.Qubits n)) ℝ)
      (true, i) (true, (i.2, i.1)) = -1 := by
  simp [adjoiningReal]

example {n : ℕ} (K L : LocalSU n) : twoSidedObjective (0 : Op (QAlgorithms.Qubits n)) K L = 0 := by
  simp [twoSidedObjective]

end

end QAlgorithms.Papers.Independent.Intake100.P95


