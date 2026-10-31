-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P90
-- name    : QAlgorithms_Papers_Independent_Intake100_P90
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:08:18.457321+00:00
-- url     : https://prove2.me/theorems/5ed48589-0278-4c64-89d0-fef4e3f06921
-- title:
--   Definitions for Lower and upper bounds on the secret key rate for QKD protocols using one--way classical communication
-- statement:
--   The objects the formalized statements of *Lower and upper bounds on the secret key rate for QKD protocols using one--way classical communication* (arXiv:quant-ph/0410215) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PairOp`
--   - `sourceBell`: PDF p.2: the normalized Bell vectors, in the printed order Phi+, Phi-, Psi+, Psi-. The last vector is (|10>-|01>)/sqrt(2).
--   - `sourceBellDiagonal`: PDF pp.2--3: Bell-diagonal matrix with the specified four real weights. Physical uses carry nonnegativity and normalization.
--   - `sourceZDisagreement`: PDF p.3: actual computational-basis disagreement probability.
--   - `sourcePauliChoice`: PDF p.2: one of the four local operations Z^a X^b. The fourth differs from Y only by a phase, which cancels in conjugation.
--   - `bilateralPauli`: PDF p.2: independent two-qubit bilateral Pauli, on a single AB pair.
--   - `pairTwirl`: PDF p.2: the physical, trace-preserving D2. The printed bare sum is corrected to the uniform average, with factor 1/4.
--   - `bb84BasisAverage`: PDF p.4: BB84's equal-basis D1, with A=B=I or H.
--   - `signalWord`: PDF pp.1--2: the product signal chosen by Alice's bit word.
--   - `localEncoding`: PDF p.1: single-position encoding filter, before physical success scaling.
--   - `encodingFilter`: PDF p.1: the actual encoding filter. Its row is <(phi^a)*|, so its matrix entry is phi^a(b), with no remaining conjugation.
--   - `sourceDecoder`: PDF p.1: B_j=|0><hat(phi^1)|+|1><hat(phi^0)|, with an explicit positive physical scaling. For nonorthogonal signals the printed unscaled operator need not be a contraction, whereas every implemented success Kraus operator must be. Scaling is the same in both realizations.
--   - `sourceTensorProduct`: PDF pp.1--2: product decoding filter, allowing nonunitary contractions.
--   - `pmBranch`: PDF p.1: Eve's prepare-and-measure branch, after the same decoder and arbitrary coherent unitary on all signals and her pure ancillary register.
--   - `eprResource`: PDF p.2: normalized Phi+ tensor resource, ordered by Alice/Bob registers.
--   - `ebVector`: PDF p.2: explicitly evaluated (A tensor B) (I tensor U) (|Phi+>^tensor n tensor |eta>), with A and B measured as in the source.
--   - `ebBranch`: PDF p.2: Alice and Bob's computational-basis projection, retaining Eve.
--   - `physicalEbVector`: PDF pp.1--2: the actual successful EB filter branch, including the positive scaling of Alice's nonunitary encoding operation.
--   - `encodingSuccessMass`: PDF pp.1--2: Alice's encoding-success probability, before Bob's filter/measurement, evaluated from the physical EB branch.
--   - `physicalEbBranch`: PDF pp.1--2: physical EB Eve vector after both local filters and Alice/Bob's two measurement outcomes.
--   - `sourceConditionalEve`: PDF pp.1--2: conditional Eve density, only used at strictly positive mass. At the zero vector the total expression is zero, not a normalized state.
--   - `mixOnFirst`: PDF p.2: random local diagonal conjugations on Alice.
--   - `mixOnSecond`: PDF p.2: the analogous random diagonal conjugations on Bob.
--   - `pairSymmetrize`: PDF p.2: the uniform common pair permutation map P_S, not a sum.
--   - `independentPairTwirl`: PDF p.2: the independent bilateral Pauli average on n pairs.
--   - `BellType`: PDF p.2: all four nonnegative occupation numbers, summing to n. Using bounded naturals supplies the finite type without truncated subtraction.
--   - `sortedBellWord`: PDF p.2: sorted word Phi1^n1 Phi2^n2 Phi3^n3 Phi4^n4.
--   - `bellWord`: PDF p.2: normalized Bell product vector for a label word.
--   - `bellCounts`: PDF p.2: Bell occupations of a word; values are natural counts.
--   - `bellTypeWeight`: PDF p.2, Eq.(1): construct lambda by grouping actual Bell probabilities of the input according to occupation numbers; it is not supplied as a premise.
--   - `IsPairBlockSeparable`: PDF p.2: separability across AB pair blocks; an individual AB factor may be entangled. This definition makes no restriction on subsequent CPP.
-- source:
--   Lower and upper bounds on the secret key rate for QKD protocols using one--way classical communication, arXiv:quant-ph/0410215v2, https://arxiv.org/abs/quant-ph/0410215v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Gates

/-!
Statements from Kraus--Gisin--Renner, quant-ph/0410215v2.
The operational rate statements are explicitly deferred in the accompanying HARD.md.
New objects below are local to this paper. All measurement blocks are unnormalized;
only conditional states divide by their positive branch mass.
Computational-basis projectors reuse pureDensity (ket x). The paper-specific
source* objects have different domains and meanings from the accepted library
declarations with the short names flagged by the previous mechanical check;
see MODERATION_NOTES.md for the exact comparison.
-/

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P90

abbrev PairOp := Matrix (Bool × Bool) (Bool × Bool) ℂ

/-- PDF p.2: the normalized Bell vectors, in the printed order
Phi+, Phi-, Psi+, Psi-. The last vector is (|10>-|01>)/sqrt(2). -/
def sourceBell (l : Fin 4) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun p =>
    let c : ℂ := (Real.sqrt 2)⁻¹
    if l = 0 then (if p.1 = p.2 then c else 0)
    else if l = 1 then (if p.1 = p.2 then (if p.1 then -c else c) else 0)
    else if l = 2 then (if p.1 ≠ p.2 then c else 0)
    else (if p.1 ≠ p.2 then (if p.1 then c else -c) else 0)

/-- PDF pp.2--3: Bell-diagonal matrix with the specified four real weights.
Physical uses carry nonnegativity and normalization. -/
def sourceBellDiagonal (w : Fin 4 → ℝ) : PairOp :=
  ∑ l, (w l : ℂ) • pureDensity (sourceBell l)

/-- PDF p.3: actual computational-basis disagreement probability. -/
def sourceZDisagreement (rho : PairOp) : ℝ :=
  (rho (false, true) (false, true)).re + (rho (true, false) (true, false)).re

/-- PDF p.2: one of the four local operations Z^a X^b. The fourth differs
from Y only by a phase, which cancels in conjugation. -/
def sourcePauliChoice (l : Fin 4) : Matrix Bool Bool ℂ :=
  if l = 0 then 1 else if l = 1 then pauliZ
  else if l = 2 then pauliX else pauliZ * pauliX

/-- PDF p.2: independent two-qubit bilateral Pauli, on a single AB pair. -/
def bilateralPauli (l : Fin 4) : PairOp :=
  Matrix.kronecker (sourcePauliChoice l) (sourcePauliChoice l)

/-- PDF p.2: the physical, trace-preserving D2. The printed bare sum is
corrected to the uniform average, with factor 1/4. -/
def pairTwirl (rho : PairOp) : PairOp :=
  (4⁻¹ : ℂ) • ∑ l : Fin 4, bilateralPauli l * rho * (bilateralPauli l).conjTranspose

/-- PDF p.4: BB84's equal-basis D1, with A=B=I or H. -/
def bb84BasisAverage (rho : PairOp) : PairOp :=
  (2⁻¹ : ℂ) • (rho +
    Matrix.kronecker hadamard hadamard * rho *
      (Matrix.kronecker hadamard hadamard).conjTranspose)

/-- PDF pp.1--2: the product signal chosen by Alice's bit word. -/
def signalWord {n : ℕ} (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (a : Qubits n) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun b => ∏ i, phi i (a i) (b i)

/-- PDF p.1: single-position encoding filter, before physical success scaling. -/
def localEncoding (phi : Bool → EuclideanSpace ℂ Bool) : Matrix Bool Bool ℂ :=
  fun a b => phi a b

/-- PDF p.1: the actual encoding filter. Its row is <(phi^a)*|,
so its matrix entry is phi^a(b), with no remaining conjugation. -/
def encodingFilter {n : ℕ} (phi : Fin n → Bool → EuclideanSpace ℂ Bool) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  fun a b => signalWord phi a b

/-- PDF p.1: B_j=|0><hat(phi^1)|+|1><hat(phi^0)|, with an explicit
positive physical scaling. For nonorthogonal signals the printed unscaled
operator need not be a contraction, whereas every implemented success
Kraus operator must be. Scaling is the same in both realizations. -/
def sourceDecoder (hat : Bool → EuclideanSpace ℂ Bool) (s : ℝ) :
    Matrix Bool Bool ℂ :=
  fun a b => (s : ℂ) * conj (hat (!a) b)

/-- PDF pp.1--2: product decoding filter, allowing nonunitary contractions. -/
def sourceTensorProduct {I : Type*} {n : ℕ} (M : Fin n → Matrix I I ℂ) :
    Matrix (Fin n → I) (Fin n → I) ℂ :=
  fun x y => ∏ i, M i (x i) (y i)

/-- PDF p.1: Eve's prepare-and-measure branch, after the same decoder
and arbitrary coherent unitary on all signals and her pure ancillary register. -/
def pmBranch {n : ℕ} {E : Type*} [Fintype E]
    (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (B : Fin n → Matrix Bool Bool ℂ)
    (U : Matrix.unitaryGroup (Qubits n × E) ℂ) (eta : EuclideanSpace ℂ E)
    (a k : Qubits n) : EuclideanSpace ℂ E :=
  WithLp.toLp 2 fun e =>
    ∑ b : Qubits n, ∑ c : Qubits n, ∑ f : E,
      sourceTensorProduct B k b * (U : Matrix _ _ ℂ) (b, e) (c, f) *
        signalWord phi a c * eta f

/-- PDF p.2: normalized Phi+ tensor resource, ordered by Alice/Bob registers. -/
def eprResource (n : ℕ) : EuclideanSpace ℂ (Qubits n × Qubits n) :=
  WithLp.toLp 2 fun p =>
    if p.1 = p.2 then (((Real.sqrt 2)⁻¹ : ℂ) ^ n) else 0

/-- PDF p.2: explicitly evaluated (A tensor B) (I tensor U)
(|Phi+>^tensor n tensor |eta>), with A and B measured as in the source. -/
def ebVector {n : ℕ} {E : Type*} [Fintype E]
    (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (B : Fin n → Matrix Bool Bool ℂ)
    (U : Matrix.unitaryGroup (Qubits n × E) ℂ) (eta : EuclideanSpace ℂ E) :
    EuclideanSpace ℂ (Qubits n × (Qubits n × E)) :=
  WithLp.toLp 2 fun p =>
    ∑ d : Qubits n, ∑ b : Qubits n, ∑ c : Qubits n, ∑ f : E,
      encodingFilter phi p.1 d * sourceTensorProduct B p.2.1 b *
        (U : Matrix _ _ ℂ) (b, p.2.2) (c, f) * eprResource n (d, c) * eta f

/-- PDF p.2: Alice and Bob's computational-basis projection, retaining Eve. -/
def ebBranch {n : ℕ} {E : Type*} [Fintype E]
    (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (B : Fin n → Matrix Bool Bool ℂ)
    (U : Matrix.unitaryGroup (Qubits n × E) ℂ) (eta : EuclideanSpace ℂ E)
    (a k : Qubits n) : EuclideanSpace ℂ E :=
  WithLp.toLp 2 fun e => ebVector phi B U eta (a, k, e)

/-- PDF pp.1--2: the actual successful EB filter branch, including the
positive scaling of Alice's nonunitary encoding operation. -/
def physicalEbVector {n : ℕ} {E : Type*} [Fintype E]
    (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (B : Fin n → Matrix Bool Bool ℂ)
    (U : Matrix.unitaryGroup (Qubits n × E) ℂ) (eta : EuclideanSpace ℂ E)
    (aScale : Fin n → ℝ) : EuclideanSpace ℂ (Qubits n × (Qubits n × E)) :=
  ((∏ i, aScale i : ℝ) : ℂ) • ebVector phi B U eta

/-- PDF pp.1--2: Alice's encoding-success probability, before Bob's
filter/measurement, evaluated from the physical EB branch. -/
def encodingSuccessMass {n : ℕ} {E : Type*} [Fintype E]
    (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (U : Matrix.unitaryGroup (Qubits n × E) ℂ) (eta : EuclideanSpace ℂ E)
    (aScale : Fin n → ℝ) : ℝ :=
  (pureDensity (physicalEbVector phi (fun _ => 1) U eta aScale)).trace.re

/-- PDF pp.1--2: physical EB Eve vector after both local filters and
Alice/Bob's two measurement outcomes. -/
def physicalEbBranch {n : ℕ} {E : Type*} [Fintype E]
    (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (B : Fin n → Matrix Bool Bool ℂ)
    (U : Matrix.unitaryGroup (Qubits n × E) ℂ) (eta : EuclideanSpace ℂ E)
    (aScale : Fin n → ℝ) (a k : Qubits n) : EuclideanSpace ℂ E :=
  WithLp.toLp 2 fun e => physicalEbVector phi B U eta aScale (a, k, e)

/-- PDF pp.1--2: conditional Eve density, only used at strictly positive mass.
At the zero vector the total expression is zero, not a normalized state. -/
def sourceConditionalEve {I : Type*} [Fintype I]
    (v : EuclideanSpace ℂ I) : Matrix I I ℂ :=
  ((pureDensity v).trace.re⁻¹ : ℂ) • pureDensity v

/-- PDF p.2: random local diagonal conjugations on Alice. -/
def mixOnFirst {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq J] (p : K → ℝ) (O : K → Matrix I I ℂ)
    (rho : Matrix (I × J) (I × J) ℂ) : Matrix (I × J) (I × J) ℂ :=
  ∑ k, (p k : ℂ) • (Matrix.kronecker (O k) (1 : Matrix J J ℂ) * rho *
    (Matrix.kronecker (O k) (1 : Matrix J J ℂ)).conjTranspose)

/-- PDF p.2: the analogous random diagonal conjugations on Bob. -/
def mixOnSecond {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] (p : K → ℝ) (O : K → Matrix J J ℂ)
    (rho : Matrix (I × J) (I × J) ℂ) : Matrix (I × J) (I × J) ℂ :=
  ∑ k, (p k : ℂ) • (Matrix.kronecker (1 : Matrix I I ℂ) (O k) * rho *
    (Matrix.kronecker (1 : Matrix I I ℂ) (O k)).conjTranspose)

/-- PDF p.2: the uniform common pair permutation map P_S, not a sum. -/
def pairSymmetrize {n : ℕ}
    (rho : Matrix (Fin n → (Bool × Bool)) (Fin n → (Bool × Bool)) ℂ) :
    Matrix (Fin n → (Bool × Bool)) (Fin n → (Bool × Bool)) ℂ :=
  ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
    ∑ pi : Equiv.Perm (Fin n), (fun x y => rho (x ∘ pi) (y ∘ pi))

/-- PDF p.2: the independent bilateral Pauli average on n pairs. -/
def independentPairTwirl {n : ℕ}
    (rho : Matrix (Fin n → (Bool × Bool)) (Fin n → (Bool × Bool)) ℂ) :
    Matrix (Fin n → (Bool × Bool)) (Fin n → (Bool × Bool)) ℂ :=
  ((Fintype.card (Fin n → Fin 4) : ℂ)⁻¹) •
    ∑ w : Fin n → Fin 4,
      sourceTensorProduct (fun i => bilateralPauli (w i)) * rho *
        (sourceTensorProduct (fun i => bilateralPauli (w i))).conjTranspose

/-- PDF p.2: all four nonnegative occupation numbers, summing to n.
Using bounded naturals supplies the finite type without truncated subtraction. -/
abbrev BellType (n : ℕ) := {t : Fin 4 → Fin (n + 1) // ∑ l, (t l).val = n}

/-- PDF p.2: sorted word Phi1^n1 Phi2^n2 Phi3^n3 Phi4^n4. -/
def sortedBellWord {n : ℕ} (t : BellType n) (i : Fin n) : Fin 4 :=
  if i.val < (t.val 0).val then 0
  else if i.val < (t.val 0).val + (t.val 1).val then 1
  else if i.val < (t.val 0).val + (t.val 1).val + (t.val 2).val then 2 else 3

/-- PDF p.2: normalized Bell product vector for a label word. -/
def bellWord {n : ℕ} (w : Fin n → Fin 4) : EuclideanSpace ℂ (Fin n → (Bool × Bool)) :=
  WithLp.toLp 2 fun x => ∏ i, sourceBell (w i) (x i)

/-- PDF p.2: Bell occupations of a word; values are natural counts. -/
def bellCounts {n : ℕ} (w : Fin n → Fin 4) (l : Fin 4) : ℕ :=
  (Finset.univ.filter fun i => w i = l).card

/-- PDF p.2, Eq.(1): construct lambda by grouping actual Bell probabilities
of the input according to occupation numbers; it is not supplied as a premise. -/
def bellTypeWeight {n : ℕ}
    (rho : Matrix (Fin n → (Bool × Bool)) (Fin n → (Bool × Bool)) ℂ) (t : BellType n) : ℝ :=
  ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin 4 =>
    ∀ l, bellCounts w l = (t.val l).val), effectProb (pureDensity (bellWord w)) rho

/-- PDF p.2: separability across AB pair blocks; an individual AB factor
may be entangled. This definition makes no restriction on subsequent CPP. -/
def IsPairBlockSeparable {n : ℕ}
    (rho : Matrix (Fin n → (Bool × Bool)) (Fin n → (Bool × Bool)) ℂ) : Prop :=
  ∃ q : ℕ, ∃ p : Fin q → ℝ, ∃ M : Fin q → Fin n → PairOp,
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
    (∀ j i, IsDensityMatrix (M j i)) ∧
    rho = ∑ j, (p j : ℂ) • sourceTensorProduct (M j)

/-- Sanity: the encoding row is the original signal, not its conjugate. -/
example {n : ℕ} (phi : Fin n → Bool → EuclideanSpace ℂ Bool) (a b : Qubits n) :
    encodingFilter phi a b = ∏ i, phi i (a i) (b i) := rfl

/-- Sanity: the decoder assigns the orthogonal-to-one vector to outcome zero. -/
example (hat : Bool → EuclideanSpace ℂ Bool) (s : ℝ) (b : Bool) :
    sourceDecoder hat s false b = (s : ℂ) * conj (hat true b) := rfl

/-- Sanity: Alice's physical encoding vector includes the product scaling. -/
example {n : ℕ} {E : Type*} [Fintype E]
    (phi : Fin n → Bool → EuclideanSpace ℂ Bool)
    (B : Fin n → Matrix Bool Bool ℂ)
    (U : Matrix.unitaryGroup (Qubits n × E) ℂ) (eta : EuclideanSpace ℂ E)
    (aScale : Fin n → ℝ) :
    physicalEbVector phi B U eta aScale =
      ((∏ i, aScale i : ℝ) : ℂ) • ebVector phi B U eta := rfl

/-- Sanity: zero pairs gives the scalar unit EPR resource. -/
example (a b : Qubits 0) : eprResource 0 (a, b) = 1 := by
  have h : a = b := Subsingleton.elim _ _
  simp [eprResource, h]

/-- Sanity: the last printed Bell vector has opposite |10> and |01> signs. -/
example : sourceBell 3 (true, false) = ((Real.sqrt 2)⁻¹ : ℂ) ∧
    sourceBell 3 (false, true) = -((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [sourceBell]

/-- Sanity: zero pairs gives the unit product matrix. -/
example (M : Fin 0 → PairOp) (x y : Fin 0 → (Bool × Bool)) :
    sourceTensorProduct M x y = 1 := by simp [sourceTensorProduct]

/-- Sanity: the QBER is zero on the zero matrix. Physical uses exclude it. -/
example : sourceZDisagreement (0 : PairOp) = 0 := by simp [sourceZDisagreement]

/-- Sanity: a singleton, identity diagonal mixture is the original state. -/
example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) :
    mixOnFirst (fun _ : Unit => 1) (fun _ => (1 : Matrix I I ℂ)) rho = rho := by
  simp [mixOnFirst, Matrix.one_kronecker_one]

end QAlgorithms.Papers.Independent.Intake100.P90


