-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P95
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:42:45.762894+00:00
-- url     : https://prove2.me/theorems/92f356e1-8876-4b8e-8f85-1b390689f247
-- title:
--   Definitions for Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence
-- statement:
--   The objects the formalized statements of *Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence* (arXiv:1503.06237) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SubsetConfig`: PDF pp.5–7: configurations on a named set of tensor legs.
--   - `mergeSubset`: PDF p.7, (2.4)–(2.5): join complementary coordinate assignments, without conjugation.
--   - `flatten`: PDF p.7, Definition 2: rows are outgoing legs; columns are incoming legs.
--   - `moveInput`: PDF p.7, (2.5): move the first input factor to the second output factor.
--   - `IsPerfect`: PDF p.7, Definition 2: even arity, nonzero, and positive scaled Gram identity for every at-most-half flattening. No marginal or entropy conclusion is assumed.
--   - `subsetDensity`: PDF pp.12–13: actual partial trace retaining A, using the frozen traceLeft. The first coordinate of the reindexed density is the discarded complement.
--   - `entropyV`: PDF pp.12–13: von Neumann entropy in units log(v), obtained from frozen bit entropy.
--   - `tripartiteInfo`: PDF p.21, (4.13): tripartite information, with each union a physical subsystem.
--   - `encoderPurification`: PDF pp.8,45: the normalized pure Choi vector of a one-spin encoder, reference leg last. This coefficient vector is distinct from frozen channel Choi density matrices.
--   - `IsPerfectErasureCode`: PDF pp.8,45: maximum erasure protection for an isometric one-spin encoder: any set of at most n−1 erased physical spins admits a CPTP recovery independent of the input. The conversion theorem separately requires 2n−1 physical spins. Channel equality is on all operators, hence includes arbitrary reference systems. Purity and maximally mixed marginals are not hypotheses of this predicate.
--   - `fiveOps`: PDF p.43, (A.1): the four signed +1 stabilizer generators, in physical wire order.
--   - `fiveGenerator`: PDF p.43, (A.1): the actual generator matrices, including their +1 phases.
--   - `fiveCode`: PDF p.43, (A.2): the simultaneous +1 eigenspace of exactly the A.1 generators.
--   - `fiveProjector`: PDF pp.43–44: the product of the four commuting +1 spectral projectors.
--   - `fiveLogicalZero`: PDF pp.44–45: a fixed normalized + logical-Z codeword; the projection of |00000⟩ has norm 1/4, so its scalar normalization is 4.
--   - `fiveLogicalOne`: PDF p.44, (A.3): logical X maps the chosen zero codeword to the one codeword.
--   - `fiveEncoder`: PDF pp.44–45: the explicit five-qubit encoder in the logical computational basis.
--   - `sixQubitState`: PDF p.45: normalized version of the printed unnormalized six-qubit state, with its reference qubit last.
--   - `sixGenerator`: PDF p.44, (A.5): recycle four checks, then append the all-X and all-Z checks.
--   - `Trit`: PDF pp.45–46: the qutrit computational labels, with arithmetic modulo three.
--   - `qutritWeyl`: PDF p.46, (A.10): X decrements labels, and Z multiplies |j⟩ by omega^j. Here omega = exp(2*pi*i/3). This is the phase-free X^a Z^b representative on m qutrits.
--   - `qutritEncoder`: PDF p.45: the three codewords (000+111+222), (012+120+201), and (021+102+210), each normalized by 1/sqrt(3).
--   - `fourQutritState`: PDF p.45: the nine printed four-qutrit terms, each with amplitude 1/3. The last leg is the logical reference.
--   - `qutritChecks`: PDF p.45, (A.9): identical X- and Z-type check vectors, expressing self-dual CSS.
--   - `qutritCSSSpace`: PDF pp.45–46: the simultaneous +1 subspace for the four A.9 checks. The X and Z checks use the same two check rows, rather than a binary CSS surrogate.
--   - `addDown`: PDF p.46, (A.11): first adder, controlled by wire 0 and targeting wire 1.
--   - `addUp`: PDF p.46, (A.11): second adder, controlled by wire 1 and targeting wire 0.
--   - `qutritCircuit`: PDF p.46, (A.11): the permutation (x1,x2) ↦ (2x1+x2,x1+x2).
--   - `IsQutritClifford`: PDF p.46: a two-qutrit Clifford is unitary and normalizes the actual phase-aware qutrit Pauli group; phases are powers of omega.
--   - `BinaryPhaseSpace`: PDF pp.60–61: a Pauli modulo its scalar phase is a pair of binary exponent vectors.
--   - `normalizerSpace`: PDF pp.60–61: the Pauli centralizer in phase-free coordinates. The set inside span is already a vector subspace, since the displayed form is bilinear.
--   - `supportSpace`: PDF pp.60–61: labels supported within A, in both X and Z coordinates.
--   - `logicalSupportDimension`: PDF pp.60–61: ell(A), dimension of centralizing labels representable within A, modulo the stabilizer label space S. Scalar phases have already been removed. Independence here does not require the represented logical operators to commute.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, https://arxiv.org/abs/1503.06237v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Defs_PauliNoiseFourier

/-!
Statements from Pastawski, Yoshida, Harlow and Preskill, arXiv:1503.06237v2.
Page numbers below are PDF page numbers. Paper-local constructions are explicit;
network results requiring unavailable geometric interfaces are recorded in HARD.md.
Compilation and independent moderation are pending.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF pp.5–7: configurations on a named set of tensor legs. -/
abbrev SubsetConfig (V : Type*) {L : Type*} (A : Finset L) := {i : L // i ∈ A} → V

/-- PDF p.7, (2.4)–(2.5): join complementary coordinate assignments, without conjugation. -/
def mergeSubset {L V : Type*} [Fintype L] [DecidableEq L] (A : Finset L)
    (a : SubsetConfig V A) (b : SubsetConfig V Aᶜ) : L → V :=
  fun i => if h : i ∈ A then a ⟨i, h⟩ else b ⟨i, Finset.mem_compl.mpr h⟩

/-- PDF p.7, Definition 2: rows are outgoing legs; columns are incoming legs. -/
def flatten {L V : Type*} [Fintype L] [DecidableEq L]
    (T : EuclideanSpace ℂ (L → V)) (A : Finset L) :
    Matrix (SubsetConfig V Aᶜ) (SubsetConfig V A) ℂ :=
  fun b a => T (mergeSubset A a b)

/-- PDF p.7, (2.5): move the first input factor to the second output factor. -/
def moveInput {A1 A2 B : Type*} (T : Matrix B (A2 × A1) ℂ) :
    Matrix (B × A2) A1 ℂ := fun ba a1 => T ba.1 (ba.2, a1)

/-- PDF p.7, Definition 2: even arity, nonzero, and positive scaled Gram identity
for every at-most-half flattening. No marginal or entropy conclusion is assumed. -/
def IsPerfect {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]
    (T : EuclideanSpace ℂ (L → V)) : Prop :=
  Even (Fintype.card L) ∧ T ≠ 0 ∧ ∀ A : Finset L,
    2 * A.card ≤ Fintype.card L → ∃ c : ℝ, 0 < c ∧
      (flatten T A)ᴴ * flatten T A = (c : ℂ) • 1

/-- PDF pp.12–13: actual partial trace retaining A, using the frozen traceLeft.
The first coordinate of the reindexed density is the discarded complement. -/
def subsetDensity {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L]
    (A : Finset L) (rho : Matrix (L → V) (L → V) ℂ) :
    Matrix (SubsetConfig V A) (SubsetConfig V A) ℂ :=
  traceLeft (fun p q : SubsetConfig V Aᶜ × SubsetConfig V A =>
    rho (mergeSubset A p.2 p.1) (mergeSubset A q.2 q.1))

/-- PDF pp.12–13: von Neumann entropy in units log(v), obtained from frozen bit entropy. -/
def entropyV {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]
    (psi : EuclideanSpace ℂ (L → V)) (A : Finset L) : ℝ :=
  vnEntropy (subsetDensity A (pureDensity psi)) / Real.logb 2 (Fintype.card V : ℝ)

/-- PDF p.21, (4.13): tripartite information, with each union a physical subsystem. -/
def tripartiteInfo {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]
    (psi : EuclideanSpace ℂ (L → V)) (A B C : Finset L) : ℝ :=
  entropyV psi A + entropyV psi B + entropyV psi C - entropyV psi (A ∪ B) -
    entropyV psi (A ∪ C) - entropyV psi (B ∪ C) + entropyV psi (A ∪ B ∪ C)

/-- PDF pp.8,45: the normalized pure Choi vector of a one-spin encoder, reference leg last.
This coefficient vector is distinct from frozen channel Choi density matrices. -/
def encoderPurification {L V : Type*} [Fintype V] (M : Matrix (L → V) V ℂ) :
    EuclideanSpace ℂ ((L ⊕ Unit) → V) :=
  WithLp.toLp 2 fun z => ((Real.sqrt (Fintype.card V : ℝ))⁻¹ : ℂ) *
    M (fun i => z (Sum.inl i)) (z (Sum.inr ()))

/-- PDF pp.8,45: maximum erasure protection for an isometric one-spin encoder:
any set of at most n−1 erased physical spins admits a CPTP recovery independent
of the input. The conversion theorem separately requires 2n−1 physical spins.
Channel equality is on all operators, hence includes arbitrary reference systems.
Purity and maximally mixed marginals are not hypotheses of this predicate. -/
def IsPerfectErasureCode {L V : Type*} [Fintype L] [Fintype V]
    [DecidableEq L] [DecidableEq V] (n : ℕ) (M : Matrix (L → V) V ℂ) : Prop :=
  Mᴴ * M = 1 ∧ ∀ A : Finset L, A.card ≤ n - 1 →
    ∃ R : Superop (SubsetConfig V Aᶜ) V, IsChannel R ∧
      ∀ rho : Matrix V V ℂ, R (subsetDensity Aᶜ (M * rho * Mᴴ)) = rho

example {L V : Type*} [Fintype L] [DecidableEq L] (A : Finset L)
    (a : SubsetConfig V A) (b : SubsetConfig V Aᶜ) (i : L) (hi : i ∈ A) :
    mergeSubset A a b i = a ⟨i, hi⟩ := by simp [mergeSubset, hi]

example {A1 A2 B : Type*} (T : Matrix B (A2 × A1) ℂ) (b : B) (a2 : A2) (a1 : A1) :
    moveInput T (b, a2) a1 = T b (a2, a1) := rfl

example {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V] :
    ¬ IsPerfect (0 : EuclideanSpace ℂ (L → V)) := by simp [IsPerfect]

example {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] (A : Finset L) :
    subsetDensity A (0 : Matrix (L → V) (L → V) ℂ) = 0 := by
  ext a b
  simp [subsetDensity, traceLeft]

example : (((Fintype.card Unit : ℂ)⁻¹ • (1 : Matrix Unit Unit ℂ)) () ()) = 1 := by
  simp

example {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]
    (A : Finset L) : entropyV (0 : EuclideanSpace ℂ (L → V)) A = 0 := by
  have hp : pureDensity (0 : EuclideanSpace ℂ (L → V)) = 0 := by
    ext a b
    simp [pureDensity]
  have ht : subsetDensity A (0 : Matrix (L → V) (L → V) ℂ) = 0 := by
    ext a b
    simp [subsetDensity, traceLeft]
  rw [entropyV, hp, ht]
  simp [vnEntropy]

/-- PDF p.43, (A.1): the four signed +1 stabilizer generators, in physical wire order. -/
def fiveOps : Fin 4 → Fin 5 → Stabilizer.Pauli :=
  ![![.X, .Z, .Z, .X, .I], ![.I, .X, .Z, .Z, .X],
    ![.X, .I, .X, .Z, .Z], ![.Z, .X, .I, .X, .Z]]

/-- PDF p.43, (A.1): the actual generator matrices, including their +1 phases. -/
def fiveGenerator (j : Fin 4) : Matrix (Qubits 5) (Qubits 5) ℂ := pauliOps (fiveOps j)

/-- PDF p.43, (A.2): the simultaneous +1 eigenspace of exactly the A.1 generators. -/
def fiveCode : Submodule ℂ (EuclideanSpace ℂ (Qubits 5)) :=
  ⨅ j : Fin 4, LinearMap.ker (Matrix.toEuclideanLin (fiveGenerator j - 1))

/-- PDF pp.43–44: the product of the four commuting +1 spectral projectors. -/
def fiveProjector : Matrix (Qubits 5) (Qubits 5) ℂ :=
  (List.ofFn fun j : Fin 4 => (2⁻¹ : ℂ) • (1 + fiveGenerator j)).prod

/-- PDF pp.44–45: a fixed normalized + logical-Z codeword; the projection of
|00000⟩ has norm 1/4, so its scalar normalization is 4. -/
def fiveLogicalZero : EuclideanSpace ℂ (Qubits 5) := 4 • act fiveProjector (zeroKet 5)

/-- PDF p.44, (A.3): logical X maps the chosen zero codeword to the one codeword. -/
def fiveLogicalOne : EuclideanSpace ℂ (Qubits 5) :=
  act (pauliOps (fun _ : Fin 5 => Stabilizer.Pauli.X)) fiveLogicalZero

/-- PDF pp.44–45: the explicit five-qubit encoder in the logical computational basis. -/
def fiveEncoder : Matrix (Qubits 5) Bool ℂ :=
  fun z b => if b then fiveLogicalOne z else fiveLogicalZero z

/-- PDF p.45: normalized version of the printed unnormalized six-qubit state,
with its reference qubit last. -/
def sixQubitState : EuclideanSpace ℂ (Qubits 6) :=
  WithLp.toLp 2 fun z => ((Real.sqrt 2)⁻¹ : ℂ) *
    fiveEncoder (fun i : Fin 5 => z ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩) (z 5)

/-- PDF p.44, (A.5): recycle four checks, then append the all-X and all-Z checks. -/
def sixGenerator (j : Fin 6) : Matrix (Qubits 6) (Qubits 6) ℂ :=
  if h : j.val < 4 then
    pauliOps (fun q : Fin 6 => if hq : q.val < 5 then fiveOps ⟨j.val, h⟩ ⟨q.val, hq⟩ else .I)
  else if j.val = 4 then pauliOps (fun _ => Stabilizer.Pauli.X)
  else pauliOps (fun _ => Stabilizer.Pauli.Z)

example : fiveOps 0 0 = Stabilizer.Pauli.X := rfl

example : fiveEncoder (fun _ => false) false = fiveLogicalZero (fun _ => false) := rfl

/-- PDF pp.45–46: the qutrit computational labels, with arithmetic modulo three. -/
abbrev Trit := ZMod 3

/-- PDF p.46, (A.10): X decrements labels, and Z multiplies |j⟩ by omega^j.
Here omega = exp(2*pi*i/3). This is the phase-free X^a Z^b representative on m qutrits. -/
def qutritWeyl (m : ℕ) (a b : Fin m → Trit) :
    Matrix (Fin m → Trit) (Fin m → Trit) ℂ :=
  fun y x => if ∀ i, y i = x i - a i then
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)) ^ (∑ i, b i * x i).val else 0

/-- PDF p.45: the three codewords (000+111+222), (012+120+201),
and (021+102+210), each normalized by 1/sqrt(3). -/
def qutritEncoder : Matrix (Fin 3 → Trit) Trit ℂ :=
  fun y l => if y 1 = y 0 + l ∧ y 2 = y 0 + 2 * l then
    ((Real.sqrt 3)⁻¹ : ℂ) else 0

/-- PDF p.45: the nine printed four-qutrit terms, each with amplitude 1/3.
The last leg is the logical reference. -/
def fourQutritState : EuclideanSpace ℂ (Fin 4 → Trit) :=
  WithLp.toLp 2 fun y => if y 1 = y 0 + y 3 ∧ y 2 = y 0 + 2 * y 3 then (1 / 3 : ℂ) else 0

/-- PDF p.45, (A.9): identical X- and Z-type check vectors, expressing self-dual CSS. -/
def qutritChecks : Fin 2 → Fin 4 → Trit := ![![1, 1, 1, 0], ![1, -1, 0, 1]]

/-- PDF pp.45–46: the simultaneous +1 subspace for the four A.9 checks.
The X and Z checks use the same two check rows, rather than a binary CSS surrogate. -/
def qutritCSSSpace : Submodule ℂ (EuclideanSpace ℂ (Fin 4 → Trit)) :=
  (⨅ j : Fin 2, LinearMap.ker
    (Matrix.toEuclideanLin (qutritWeyl 4 (qutritChecks j) 0 - 1))) ⊓
  (⨅ j : Fin 2, LinearMap.ker
    (Matrix.toEuclideanLin (qutritWeyl 4 0 (qutritChecks j) - 1)))

example : fourQutritState ![0, 0, 0, 0] = (1 / 3 : ℂ) := by
  change (if (0 : Trit) = 0 + 0 ∧ (0 : Trit) = 0 + 2 * 0 then
    (1 / 3 : ℂ) else 0) = (1 / 3 : ℂ)
  norm_num

example : qutritChecks 1 1 = (-1 : Trit) := rfl

/-- PDF p.46, (A.11): first adder, controlled by wire 0 and targeting wire 1. -/
def addDown : Matrix (Fin 2 → Trit) (Fin 2 → Trit) ℂ :=
  fun y x => if y 0 = x 0 ∧ y 1 = x 0 + x 1 then 1 else 0

/-- PDF p.46, (A.11): second adder, controlled by wire 1 and targeting wire 0. -/
def addUp : Matrix (Fin 2 → Trit) (Fin 2 → Trit) ℂ :=
  fun y x => if y 0 = x 0 + x 1 ∧ y 1 = x 1 then 1 else 0

/-- PDF p.46, (A.11): the permutation (x1,x2) ↦ (2x1+x2,x1+x2). -/
def qutritCircuit : Matrix (Fin 2 → Trit) (Fin 2 → Trit) ℂ :=
  fun y x => if y 0 = 2 * x 0 + x 1 ∧ y 1 = x 0 + x 1 then 1 else 0

/-- PDF p.46: a two-qutrit Clifford is unitary and normalizes the actual
phase-aware qutrit Pauli group; phases are powers of omega. -/
def IsQutritClifford (U : Matrix (Fin 2 → Trit) (Fin 2 → Trit) ℂ) : Prop :=
  Uᴴ * U = 1 ∧ ∀ a b : Fin 2 → Trit, ∃ aout bout : Fin 2 → Trit, ∃ c : Trit,
    U * qutritWeyl 2 a b * Uᴴ =
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)) ^ c.val • qutritWeyl 2 aout bout

example : qutritCircuit ![2, 1] ![1, 0] = 1 := by norm_num [qutritCircuit]

/-- PDF pp.60–61: a Pauli modulo its scalar phase is a pair of binary exponent vectors. -/
abbrev BinaryPhaseSpace (n : ℕ) := SparsePauliNoise.Label n

/-- PDF pp.60–61: the Pauli centralizer in phase-free coordinates. The set inside
span is already a vector subspace, since the displayed form is bilinear. -/
def normalizerSpace {n : ℕ} (S : Submodule (ZMod 2) (BinaryPhaseSpace n)) :
    Submodule (ZMod 2) (BinaryPhaseSpace n) :=
  Submodule.span (ZMod 2) {a | ∀ b ∈ S, SparsePauliNoise.symplecticPairing a b = 0}

/-- PDF pp.60–61: labels supported within A, in both X and Z coordinates. -/
def supportSpace {n : ℕ} (A : Finset (Fin n)) :
    Submodule (ZMod 2) (BinaryPhaseSpace n) :=
  Submodule.span (ZMod 2) {a | ∀ i, i ∉ A → a.1 i = 0 ∧ a.2 i = 0}

/-- PDF pp.60–61: ell(A), dimension of centralizing labels representable within A,
modulo the stabilizer label space S. Scalar phases have already been removed.
Independence here does not require the represented logical operators to commute. -/
def logicalSupportDimension {n : ℕ} (S : Submodule (ZMod 2) (BinaryPhaseSpace n))
    (A : Finset (Fin n)) : ℕ :=
  Module.finrank (ZMod 2) ((normalizerSpace S ⊓ supportSpace A).map S.mkQ)

example {n : ℕ} (a : BinaryPhaseSpace n) : SparsePauliNoise.symplecticPairing 0 a = 0 := by
  simp [SparsePauliNoise.symplecticPairing, dotProduct]

example {n : ℕ} (A : Finset (Fin n)) : (0 : BinaryPhaseSpace n) ∈ supportSpace A :=
  Submodule.zero_mem _

end

end QAlgorithms.Papers.Independent.Intakenext100.P95


