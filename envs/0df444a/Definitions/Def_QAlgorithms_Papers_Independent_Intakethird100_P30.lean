-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P30
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:35:05.025214+00:00
-- url     : https://prove2.me/theorems/8242e7f8-726d-4cb2-894d-a78522c79b5e
-- title:
--   Definitions for Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution
-- statement:
--   The objects the formalized statements of *Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution* (arXiv:1612.07734) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sixStateBellPair`: PDF p.1: the normalized Bell vector, reusing the frozen one-EPR-pair vector. The bijection sends a Bool to its constant one-bit word; no new Bell state is defined.
--   - `sixState`: PDF pp.1,3: the six-state input, with QBER in [0,1/2] in the statements.
--   - `sixStateCopies`: PDF p.3, (1): independent sixStateCopies, explicitly regrouped as A^I B^I.
--   - `codeKraus`: PDF p.3, (2): the codeword-to-label Kraus operator, not a channel.
--   - `bobState`: PDF p.3, (1): Bob-only filtered operator, constructed by actual conjugation.
--   - `bothState`: PDF p.7, (20): Alice and Bob both apply the same code filter.
--   - `otherMarginal`: PDF pp.1,9: trace out the original B, retaining A and the B-prime copy.
--   - `IsBobCopyExtension`: PDF pp.1,9 and reference [21], p.10: actual positive-operator extension.
--   - `BobExtendible`: PDF pp.1,9: extendability to a copy of Bob; zero operators are allowed.
--   - `threshold`: PDF p.3: upper transition boundary. The inserted zero and the bounded QBER domain make this supremum nonempty and bounded for every input family. This formulation records 'beyond which', without assuming a transition theorem.
--   - `bobThreshold`: PDF p.3: Bob-only threshold of the constructed family (1).
--   - `bothThreshold`: PDF p.7: threshold in the same-code Alice/Bob regime (20).
--   - `codeWordXor`: PDF pp.3–4: coordinatewise XOR.
--   - `CodeEquivalent`: PDF p.4: equivalence forgets word order as well as coordinate order and translation. The coordinate bijection also handles differently named finite register sets.
--   - `NoConstantColumns`: PDF p.4: every coordinate assumes both values among codewords.
--   - `codeProduct`: PDF p.4: Cartesian concatenation; the coordinate registers are explicitly a sum.
--   - `FixedCoordinates`: PDF p.4: the constant-coordinate register of a code.
--   - `VaryingCoordinates`: PDF p.4: the surviving register after deleting all constant columns.
--   - `deleteConstants`: PDF p.4: deletion is a restriction of the actual words, including the empty tail.
--   - `repetition`: PDF pp.2,4: the two repetition words; injective only on a nonempty register.
--   - `repetitionPolynomial`: PDF p.5, (9), and p.10, (A3): the exact repetition polynomial.
--   - `chau`: PDF p.5: Chau's limiting QBER.
--   - `repetitionApprox`: PDF p.5, (10): the displayed approximation, used only at positive block length.
--   - `diagonalLaw`: PDF p.3: the normalized diagonal law; never used without positive trace.
--   - `acceptanceMass`: PDF p.3: acceptance mass in the original computational-basis distribution.
--   - `xorSectorBlock`: PDF p.3: XOR-sector block, with all word labels retained.
--   - `xorSectorPermutation`: PDF p.3, (4): fixed computational-basis permutation (alpha,k) -> (alpha XOR Ck,k).
--   - `MatrixEntryCompatible`: PDF p.3: full compatible-case condition from both Kronecker deltas in (3).
--   - `multiCode`: PDF p.4: a finite iterated Cartesian concatenation, with named coordinate blocks.
--   - `publicAnnouncement`: PDF p.3: the retained announcement is a classical, duplicated public label. All off-diagonal label blocks vanish; membership is checked on both Bob indices.
--   - `forgottenAnnouncement`: PDF p.3: forgetting the classical label sums branch operators, not amplitudes.
--   - `transformCodeSet`: PDF p.4: action on unordered code sets, coordinate permutation then fixed XOR.
--   - `codeOrbit`: PDF p.4: the finite orbit of an unordered code, used as its canonical class key.
--   - `SetNoConstantColumns`: PDF p.4: absence of constant columns for an unordered code set.
--   - `codeClassCount`: PDF p.4, Table I: number of distinct orbits of size-m code sets. Taking the image of full orbits forgets both codeword order and coordinate symmetries.
--   - `tableEntries`: PDF p.4, Table I: all and only the numeric cells, visually checked in the PDF. Each triple is (block length, number of words, number of inequivalent codes).
--   - `SDPFeasible`: PDF p.5, (11): free Hermitian R with PSD shifted R, not necessarily PSD R.
--   - `slackValues`: PDF p.5, (11): the feasible objective values, with actual marginal constraints.
--   - `sdpMinimum`: PDF p.5: exact SDP value. Feasibility, a lower bound, and attainment are conclusions of sdpCharacterization, never extra hypotheses deciding extendability.
--   - `codeSlack`: PDF p.5, (12): exact function T_C; no spline or grid is used here.
--   - `CodeLinear`: PDF p.3: linearity means XOR closure, without imposing it on general codes.
--   - `fourWordCode`: PDF p.6, (14): the four explicit words on a first bit and an n-bit tail.
--   - `prependCodeColumn`: PDF p.7: add the new column first; moving it to the last position is a coordinate permutation.
--   - `columnOrbitCandidates`: PDF p.7: orbits represented by nonconstant new columns, allowing further identifications.
--   - `complementExtension`: PDF p.7, (19): lower block is the complement, not another unchanged copy of C.
--   - `twistedExtension`: PDF p.7: the more general extension uses the equivalent code in its lower block.
--   - `ComplementClosed`: PDF p.7: complement closure as a pointwise property of the entire code set.
--   - `zeroTail`: PDF p.7: the converse constructs the first-bit-zero tail code, not a free witness.
--   - `Equidistant`: PDF p.8: equidistance is imposed on every pair of distinct code labels.
--   - `simplexS`: PDF p.8, (21): the common diagonal coefficient s.
--   - `simplexU`: PDF pp.3,8, (3),(21): the off-equal-label population u.
--   - `simplexV`: PDF pp.3,8, (3),(21): the coherence coefficient v.
--   - `simplexZ`: PDF p.8, (21)–(22): the positive trace used to normalize the filtered operator.
--   - `simplexA`: PDF p.8, (22): eigenvalue of the distinguished Bell vector.
--   - `simplexB`: PDF p.8, (22): the other zero-shift eigenvalue.
--   - `simplexWeights`: PDF p.8, (22): the third eigenvalue, computed from the actual code coefficients.
--   - `cyclicBellVector`: PDF p.8: generalized Bell vectors for the source's X(k)Z(l) order. The clock phase acts on the original second label i, before its cyclic shift by k. This defines Bell vectors directly, without introducing a duplicate Weyl operator.
--   - `vectorPurification`: PDF p.8, IV B step 1: vec(sqrt(P)), physical AB first and E1E2 second. This is an unnormalized purification for general PSD P, not an arbitrary state witness.
--   - `candidateDegrader`: PDF p.8, IV B step 2: candidate E = N after trace E2.
--   - `complementaryOperator`: PDF p.8: complementary Choi operator, obtained by tracing the actual B from the constructed purification. It is not assumed trace preserving.
--   - `candidateExtension`: PDF pp.8–9: the proposed extension is constructed by acting on the purification.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, https://arxiv.org/abs/1612.07734v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement

/-!
Khatri–Lütkenhaus, arXiv:1612.07734v2. All citations use PDF page numbers.
Filtered operators are unnormalized. Code labels are arbitrary finite types;
requiring injectivity and nonempty labels gives precisely distinct nonempty codes.
Finite coordinate types allow explicit splitting and regrouping of registers.
For `Fin n` the word space is the frozen `QAlgorithms.Qubits n`.
Compilation is pending the authorized batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}
variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]
variable [Fintype A] [Fintype B]

/-- PDF p.1: the normalized Bell vector, reusing the frozen one-EPR-pair vector.
The bijection sends a Bool to its constant one-bit word; no new Bell state is defined. -/
def sixStateBellPair : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun p => maxEntangled 1 ((fun _ => p.1), (fun _ => p.2))

/-- PDF pp.1,3: the six-state input, with QBER in [0,1/2] in the statements. -/
def sixState (Q : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ((1 - 2 * Q : ℝ) : ℂ) • pureDensity sixStateBellPair + ((Q / 2 : ℝ) : ℂ) • 1

/-- PDF p.3, (1): independent sixStateCopies, explicitly regrouped as A^I B^I. -/
def sixStateCopies (I : Type) [Fintype I] (Q : ℝ) :
    Matrix ((I → Bool) × (I → Bool)) ((I → Bool) × (I → Bool)) ℂ :=
  fun p q => ∏ i, sixState Q (p.1 i, p.2 i) (q.1 i, q.2 i)

/-- PDF p.3, (2): the codeword-to-label Kraus operator, not a channel. -/
def codeKraus (C : K → (I → Bool)) : Matrix K (I → Bool) ℂ :=
  fun k w => if w = C k then 1 else 0

/-- PDF p.3, (1): Bob-only filtered operator, constructed by actual conjugation. -/
def bobState (C : K → (I → Bool)) (Q : ℝ) :
    Matrix ((I → Bool) × K) ((I → Bool) × K) ℂ :=
  let F := Matrix.kronecker (1 : Matrix (I → Bool) (I → Bool) ℂ) (codeKraus C)
  F * sixStateCopies I Q * Fᴴ

/-- PDF p.7, (20): Alice and Bob both apply the same code filter. -/
def bothState (C : K → (I → Bool)) (Q : ℝ) : Matrix (K × K) (K × K) ℂ :=
  let F := Matrix.kronecker (codeKraus C) (codeKraus C)
  F * sixStateCopies I Q * Fᴴ

/-- PDF pp.1,9: trace out the original B, retaining A and the B-prime copy. -/
def otherMarginal (R : Matrix ((A × B) × B) ((A × B) × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  fun p q => ∑ b, R ((p.1, b), p.2) ((q.1, b), q.2)

/-- PDF pp.1,9 and reference [21], p.10: actual positive-operator extension. -/
def IsBobCopyExtension (P : Matrix (A × B) (A × B) ℂ)
    (R : Matrix ((A × B) × B) ((A × B) × B) ℂ) : Prop :=
  R.PosSemidef ∧ traceRight R = P ∧ otherMarginal R = P

/-- PDF pp.1,9: extendability to a copy of Bob; zero operators are allowed. -/
def BobExtendible (P : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ R, IsBobCopyExtension P R

/-- PDF p.3: upper transition boundary. The inserted zero and the bounded
QBER domain make this supremum nonempty and bounded for every input family.
This formulation records 'beyond which', without assuming a transition theorem. -/
def threshold (P : ℝ → Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup (insert 0 {q : ℝ | 0 ≤ q ∧ q ≤ 1 / 2 ∧ ¬ BobExtendible (P q)})

/-- PDF p.3: Bob-only threshold of the constructed family (1). -/
def bobThreshold (C : K → (I → Bool)) : ℝ := threshold (bobState C)

/-- PDF p.7: threshold in the same-code Alice/Bob regime (20). -/
def bothThreshold (C : K → (I → Bool)) : ℝ := threshold (bothState C)

/-- PDF pp.3–4: coordinatewise XOR. -/
def codeWordXor (u v : I → Bool) : I → Bool := fun i => Bool.xor (u i) (v i)

/-- PDF p.4: equivalence forgets word order as well as coordinate order and translation.
The coordinate bijection also handles differently named finite register sets. -/
def CodeEquivalent (C : K → (I → Bool)) (D : L → (J → Bool)) : Prop :=
  ∃ (p : I ≃ J) (t : I → Bool) (e : K ≃ L),
    ∀ k i, C k i = Bool.xor (D (e k) (p i)) (t i)

/-- PDF p.4: every coordinate assumes both values among codewords. -/
def NoConstantColumns (C : K → (I → Bool)) : Prop :=
  ∀ i, ∃ k l, C k i ≠ C l i

/-- PDF p.4: Cartesian concatenation; the coordinate registers are explicitly a sum. -/
def codeProduct (C : K → (I → Bool)) (D : L → (J → Bool)) :
    (K × L) → (Sum I J → Bool) :=
  fun k => Sum.elim (C k.1) (D k.2)

/-- PDF p.4: the constant-coordinate register of a code. -/
abbrev FixedCoordinates (C : K → (I → Bool)) := {i : I // ∀ k l, C k i = C l i}

/-- PDF p.4: the surviving register after deleting all constant columns. -/
abbrev VaryingCoordinates (C : K → (I → Bool)) := {i : I // ∃ k l, C k i ≠ C l i}

/-- PDF p.4: deletion is a restriction of the actual words, including the empty tail. -/
def deleteConstants (C : K → (I → Bool)) : K → (VaryingCoordinates C → Bool) :=
  fun k i => C k i.val

/-- PDF pp.2,4: the two repetition words; injective only on a nonempty register. -/
def repetition (I : Type) : Bool → (I → Bool) := fun b _ => b

/-- PDF p.5, (9), and p.10, (A3): the exact repetition polynomial. -/
def repetitionPolynomial (n : ℕ) (q : ℝ) : ℝ :=
  4 * q ^ (2 * n) - 4 * q ^ n * (1 - q) ^ n + (1 - 2 * q) ^ (2 * n)

/-- PDF p.5: Chau's limiting QBER. -/
def chau : ℝ := (5 - Real.sqrt 5) / 10

/-- PDF p.5, (10): the displayed approximation, used only at positive block length. -/
def repetitionApprox (n : ℕ) : ℝ :=
  let r := Real.rpow (1 / 4) (1 / (n : ℝ))
  let a := 4 * r + 1
  (a - Real.sqrt (a ^ 2 - 4 * r * a)) / (2 * a)

/-- PDF p.3: the normalized diagonal law; never used without positive trace. -/
def diagonalLaw (P : Matrix (A × B) (A × B) ℂ) (a : A) (b : B) : ℝ :=
  (P (a, b) (a, b)).re / P.trace.re

/-- PDF p.3: acceptance mass in the original computational-basis distribution. -/
def acceptanceMass (C : K → (I → Bool)) (Q : ℝ) : ℝ :=
  ∑ a : I → Bool, ∑ k, (sixStateCopies I Q (a, C k) (a, C k)).re

/-- PDF p.3: XOR-sector block, with all word labels retained. -/
def xorSectorBlock (C : K → (I → Bool)) (Q : ℝ) (beta : I → Bool) : Matrix K K ℂ :=
  fun k l => bobState C Q (codeWordXor beta (C k), k) (codeWordXor beta (C l), l)

/-- PDF p.3, (4): fixed computational-basis permutation (alpha,k) -> (alpha XOR Ck,k). -/
def xorSectorPermutation (C : K → (I → Bool)) :
    Matrix ((I → Bool) × K) ((I → Bool) × K) ℂ :=
  fun p q => if p.1 = codeWordXor q.1 (C q.2) ∧ p.2 = q.2 then 1 else 0

/-- PDF p.3: full compatible-case condition from both Kronecker deltas in (3). -/
def MatrixEntryCompatible (C : K → (I → Bool)) (a a2 : I → Bool) (k l : K) : Prop :=
  codeWordXor a (C k) = codeWordXor a2 (C l) ∧
    ∀ i, ¬ (codeWordXor a (C k) i = true ∧ codeWordXor a a2 i = true)

/-- PDF p.4: a finite iterated Cartesian concatenation, with named coordinate blocks. -/
def multiCode {S : Type} {D M : S → Type} (C : (s : S) → M s → (D s → Bool)) :
    ((s : S) → M s) → (Sigma D → Bool) :=
  fun k i => C i.1 (k i.1) i.2

/-- PDF p.1: maximally noisy endpoint is I/4. -/
example : sixState (1 / 2) = (1 / 4 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  norm_num [sixState]

/-- PDF p.3: no sixStateCopies give the scalar one, a combinatorial helper only. -/
example (q : ℝ) (p r : (Fin 0 → Bool) × (Fin 0 → Bool)) : sixStateCopies (Fin 0) q p r = 1 := by
  simp [sixStateCopies]

/-- PDF p.3: a codeword is sent to its full label with amplitude one. -/
example (C : K → (I → Bool)) (k : K) : codeKraus C k (C k) = 1 := by
  simp [codeKraus]

/-- PDF p.10, reference [21]: the zero positive operator has a zero extension. -/
example : BobExtendible (0 : Matrix (A × B) (A × B) ℂ) := by
  refine ⟨0, Matrix.PosSemidef.zero, ?_, ?_⟩
  · ext p q
    simp [traceRight]
  · ext p q
    simp [otherMarginal]

/-- PDF p.4: the two one-bit repetition words are distinct. -/
example : Function.Injective (repetition (Fin 1)) := by
  intro a b h
  exact congrFun h 0

/-- PDF p.3: the retained announcement is a classical, duplicated public label.
All off-diagonal label blocks vanish; membership is checked on both Bob indices. -/
def publicAnnouncement {n : ℕ} {S : Type} [Fintype S]
    (cells : S → Finset (Qubits n)) (accepted : Finset S) (Q : ℝ) :
    Matrix ((Qubits n × S) × (Qubits n × S))
      ((Qubits n × S) × (Qubits n × S)) ℂ :=
  fun p q =>
    if p.1.2 = p.2.2 ∧ q.1.2 = q.2.2 ∧ p.1.2 = q.1.2 ∧
      p.1.2 ∈ accepted ∧ p.2.1 ∈ cells p.1.2 ∧ q.2.1 ∈ cells p.1.2
    then sixStateCopies (Fin n) Q (p.1.1, p.2.1) (q.1.1, q.2.1) else 0

/-- PDF p.3: forgetting the classical label sums branch operators, not amplitudes. -/
def forgottenAnnouncement {n : ℕ} {S : Type} [Fintype S]
    (cells : S → Finset (Qubits n)) (accepted : Finset S) (Q : ℝ) :
    Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  fun p q => ∑ s ∈ accepted,
    if p.2 ∈ cells s ∧ q.2 ∈ cells s then sixStateCopies (Fin n) Q p q else 0

/-- PDF p.3: with no accepted cells the forgotten branch is the zero operator. -/
example {n : ℕ} {S : Type} [Fintype S] (cells : S → Finset (Qubits n)) (Q : ℝ) :
    forgottenAnnouncement cells ∅ Q = 0 := by
  ext p q
  simp [forgottenAnnouncement]

/-- PDF p.4: action on unordered code sets, coordinate permutation then fixed XOR. -/
def transformCodeSet {n : ℕ} (p : Equiv.Perm (Fin n)) (t : Qubits n)
    (C : Finset (Qubits n)) : Finset (Qubits n) :=
  C.image (fun w i => Bool.xor (w (p i)) (t i))

/-- PDF p.4: the finite orbit of an unordered code, used as its canonical class key. -/
def codeOrbit {n : ℕ} (C : Finset (Qubits n)) : Finset (Finset (Qubits n)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n) × Qubits n)).image
    (fun g => transformCodeSet g.1 g.2 C)

/-- PDF p.4: absence of constant columns for an unordered code set. -/
def SetNoConstantColumns {n : ℕ} (C : Finset (Qubits n)) : Prop :=
  ∀ i, ∃ u ∈ C, ∃ v ∈ C, u i ≠ v i

/-- PDF p.4, Table I: number of distinct orbits of size-m code sets.
Taking the image of full orbits forgets both codeword order and coordinate symmetries. -/
def codeClassCount (n m : ℕ) : ℕ :=
  (((Finset.univ : Finset (Qubits n)).powerset.filter
    (fun C => C.card = m ∧ SetNoConstantColumns C)).image codeOrbit).card

/-- PDF p.4, Table I: all and only the numeric cells, visually checked in the PDF.
Each triple is (block length, number of words, number of inequivalent codes). -/
def tableEntries : List (ℕ × ℕ × ℕ) :=
  [(2,2,1), (2,3,1),
   (3,2,1), (3,3,2), (3,4,5), (3,5,3), (3,6,3), (3,7,1),
   (4,2,1), (4,3,3), (4,4,13), (4,5,24), (4,6,47), (4,7,55),
   (4,8,73), (4,9,56), (4,10,50), (4,11,27), (4,12,19),
   (4,13,6), (4,14,4), (4,15,1),
   (5,2,1), (5,3,4), (5,4,28), (5,5,104), (5,6,422),
   (6,2,1), (6,3,6), (6,4,56), (7,2,1), (7,3,7), (8,2,1), (8,3,9)]

/-- PDF p.4: the identity coordinate action fixes every unordered code. -/
example {n : ℕ} (C : Finset (Qubits n)) :
    transformCodeSet (Equiv.refl _) (fun _ => false) C = C := by
  simp [transformCodeSet]

/-- PDF p.4: the transcription contains 34 asserted numeric cells. -/
example : tableEntries.length = 34 := by rfl

/-- PDF p.5, (11): free Hermitian R with PSD shifted R, not necessarily PSD R. -/
def SDPFeasible (P : Matrix (A × B) (A × B) ℂ) (t : ℝ)
    (R : Matrix ((A × B) × B) ((A × B) × B) ℂ) : Prop :=
  R.IsHermitian ∧ (R + (t : ℂ) • 1).PosSemidef ∧
    traceRight R = P ∧ otherMarginal R = P

/-- PDF p.5, (11): the feasible objective values, with actual marginal constraints. -/
def slackValues (P : Matrix (A × B) (A × B) ℂ) : Set ℝ :=
  {t | ∃ R, SDPFeasible P t R}

/-- PDF p.5: exact SDP value. Feasibility, a lower bound, and attainment are
conclusions of sdpCharacterization, never extra hypotheses deciding extendability. -/
def sdpMinimum (P : Matrix (A × B) (A × B) ℂ) : ℝ := sInf (slackValues P)

/-- PDF p.5, (12): exact function T_C; no spline or grid is used here. -/
def codeSlack (C : K → (I → Bool)) (Q : ℝ) : ℝ := sdpMinimum (bobState C Q)

/-- PDF p.5: zero operator, zero slack, zero R are feasible, including the boundary. -/
example : SDPFeasible (0 : Matrix (A × B) (A × B) ℂ) 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.IsHermitian]
  · simpa using (Matrix.PosSemidef.zero : (0 : Matrix ((A × B) × B) ((A × B) × B) ℂ).PosSemidef)
  · ext p q
    simp [traceRight]
  · ext p q
    simp [otherMarginal]

/-- PDF p.3: linearity means XOR closure, without imposing it on general codes. -/
def CodeLinear (C : K → (I → Bool)) : Prop :=
  ∀ k l, ∃ r, C r = codeWordXor (C k) (C l)

/-- PDF p.6, (14): the four explicit words on a first bit and an n-bit tail. -/
def fourWordCode (n : ℕ) : (Bool × Bool) → (Sum (Fin 1) (Fin n) → Bool) :=
  fun k => Sum.elim (fun _ => k.1) (fun _ => k.2)

/-- PDF p.6: the all-zero word belongs to the constructed four-word family. -/
example (n : ℕ) : fourWordCode n (false, false) = (fun _ => false) := by
  funext i
  exact Sum.rec (fun _ => rfl) (fun _ => rfl) i

/-- PDF p.7: add the new column first; moving it to the last position is a coordinate permutation. -/
def prependCodeColumn {n m : ℕ} (C : Fin m → Qubits n) (v : Fin m → Bool) :
    Fin m → Qubits (n + 1) := fun k => Fin.cons (v k) (C k)

/-- PDF p.7: orbits represented by nonconstant new columns, allowing further identifications. -/
def columnOrbitCandidates {n m : ℕ} (C : Fin m → Qubits n) :
    Finset (Finset (Finset (Qubits (n + 1)))) :=
  ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => ∃ k l, v k ≠ v l)).image
    (fun v => codeOrbit ((Finset.univ : Finset (Fin m)).image (prependCodeColumn C v)))

/-- PDF p.7: the added first bit is the chosen column bit. -/
example {n m : ℕ} (C : Fin m → Qubits n) (v : Fin m → Bool) (k : Fin m) :
    prependCodeColumn C v k 0 = v k := by simp [prependCodeColumn]

/-- PDF p.7, (19): lower block is the complement, not another unchanged copy of C. -/
def complementExtension {n : ℕ} (C : Finset (Qubits n)) : Finset (Qubits (n + 1)) :=
  C.image (fun w => Fin.cons false w) ∪
    C.image (fun w => Fin.cons true (fun i => !(w i)))

/-- PDF p.7: the more general extension uses the equivalent code in its lower block. -/
def twistedExtension {n : ℕ} (C : Finset (Qubits n))
    (p : Equiv.Perm (Fin n)) (t : Qubits n) : Finset (Qubits (n + 1)) :=
  C.image (fun w => Fin.cons false w) ∪
    (transformCodeSet p t C).image (fun w => Fin.cons true w)

/-- PDF p.7: complement closure as a pointwise property of the entire code set. -/
def ComplementClosed {n : ℕ} (C : Finset (Qubits n)) : Prop :=
  ∀ w ∈ C, (fun i => !(w i)) ∈ C

/-- PDF p.7: the converse constructs the first-bit-zero tail code, not a free witness. -/
def zeroTail {n : ℕ} (D : Finset (Qubits (n + 1))) : Finset (Qubits n) :=
  (D.filter (fun w => w 0 = false)).image (fun w i => w i.succ)

/-- PDF p.7: an empty input gives an empty extension; nonemptiness is a theorem hypothesis. -/
example {n : ℕ} : complementExtension (∅ : Finset (Qubits n)) = ∅ := by
  simp [complementExtension]

/-- PDF p.8: equidistance is imposed on every pair of distinct code labels. -/
def Equidistant (C : K → (I → Bool)) (d : ℕ) : Prop :=
  ∀ k l, k ≠ l → hammingDist (C k) (C l) = d

/-- PDF p.8, (21): the common diagonal coefficient s. -/
def simplexS (n : ℕ) (Q : ℝ) : ℝ := ((1 - Q) / 2) ^ n

/-- PDF pp.3,8, (3),(21): the off-equal-label population u. -/
def simplexU (n d : ℕ) (Q : ℝ) : ℝ := Q ^ d * (1 - Q) ^ (n - d) / 2 ^ n

/-- PDF pp.3,8, (3),(21): the coherence coefficient v. -/
def simplexV (n d : ℕ) (Q : ℝ) : ℝ := (1 - 2 * Q) ^ d * (1 - Q) ^ (n - d) / 2 ^ n

/-- PDF p.8, (21)–(22): the positive trace used to normalize the filtered operator. -/
def simplexZ (n m d : ℕ) (Q : ℝ) : ℝ :=
  m * simplexS n Q + m * (m - 1) * simplexU n d Q

/-- PDF p.8, (22): eigenvalue of the distinguished Bell vector. -/
def simplexA (n m d : ℕ) (Q : ℝ) : ℝ :=
  (simplexS n Q + (m - 1) * simplexV n d Q) / simplexZ n m d Q

/-- PDF p.8, (22): the other zero-shift eigenvalue. -/
def simplexB (n m d : ℕ) (Q : ℝ) : ℝ :=
  (simplexS n Q - simplexV n d Q) / simplexZ n m d Q

/-- PDF p.8, (22): the third eigenvalue, computed from the actual code coefficients. -/
def simplexWeights (n m d : ℕ) (Q : ℝ) (k l : Fin m) : ℝ :=
  if k.val = 0 ∧ l.val = 0 then simplexA n m d Q
  else if k.val = 0 then simplexB n m d Q
  else simplexU n d Q / simplexZ n m d Q

/-- PDF p.8: generalized Bell vectors for the source's X(k)Z(l) order.
The clock phase acts on the original second label i, before its cyclic shift by k.
This defines Bell vectors directly, without introducing a duplicate Weyl operator. -/
def cyclicBellVector (m : ℕ) (k l : Fin m) : EuclideanSpace ℂ (Fin m × Fin m) :=
  WithLp.toLp 2 fun p =>
    if p.2.val = (p.1.val + k.val) % m then
      (Real.sqrt (m : ℝ) : ℂ)⁻¹ *
        Complex.exp (((2 * Real.pi * (p.1.val : ℝ) * (l.val : ℝ) / m : ℝ) : ℂ) * Complex.I)
    else 0

/-- PDF p.8: the zero-shift, zero-clock two-dimensional Bell coefficient. -/
example : cyclicBellVector 2 0 0 (0, 0) = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [cyclicBellVector]

/-- PDF p.8: a shifted Bell vector has no coefficient on |00>. -/
example : cyclicBellVector 2 1 0 (0, 0) = 0 := by
  norm_num [cyclicBellVector]

/-- PDF p.8, IV B step 1: vec(sqrt(P)), physical AB first and E1E2 second.
This is an unnormalized purification for general PSD P, not an arbitrary state witness. -/
def vectorPurification (P : Matrix (A × B) (A × B) ℂ) :
    EuclideanSpace ℂ ((A × B) × (A × B)) :=
  WithLp.toLp 2 fun p => cfc Real.sqrt P p.1 p.2

/-- PDF p.8, IV B step 2: candidate E = N after trace E2. -/
def candidateDegrader (N : Superop A B) : Superop (A × B) B :=
  fun X => N (traceRight X)

/-- PDF p.8: complementary Choi operator, obtained by tracing the actual B
from the constructed purification. It is not assumed trace preserving. -/
def complementaryOperator (P : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × (A × B)) (A × (A × B)) ℂ :=
  fun p q => ∑ b, pureDensity (vectorPurification P) ((p.1, b), p.2) ((q.1, b), q.2)

/-- PDF pp.8–9: the proposed extension is constructed by acting on the purification. -/
def candidateExtension (P : Matrix (A × B) (A × B) ℂ) (N : Superop A B) :
    Matrix ((A × B) × B) ((A × B) × B) ℂ :=
  idTensorSuperop (candidateDegrader N) (pureDensity (vectorPurification P))

/-- PDF p.8: pins the vectorization ordering, including off-diagonal coefficients. -/
example (P : Matrix (A × B) (A × B) ℂ) (i j : A × B) :
    vectorPurification P (i, j) = cfc Real.sqrt P i j := by rfl

end QAlgorithms.Papers.Independent.Intakethird100.P30


