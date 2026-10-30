-- Prove2me | Definitions.Def_QAlgorithms_Defs_LocalHamiltonian
-- name    : QAlgorithms_Defs_LocalHamiltonian
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:16:19.476167+00:00
-- url     : https://prove2.me/theorems/c6d434d8-1309-48e4-9cb0-54743dbc5bb3
-- title:
--   prove2quantum library: Defs.LocalHamiltonian
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.LocalHamiltonian`), reused by its paper formalizations.
--
--   - `LocalTerm`: de Wolf p.129–130: one term of a `k`-local Hamiltonian on `n` qubits: the `k` distinct qubits it acts on (in order) and its `2^k × 2^k` matrix, whose entries are Gaussian rationals given by their real and imaginary parts (the source's "each complex entry represented with poly(n) bits").
--   - `LocalTerm.mat`: The `2^k × 2^k` complex matrix of a term.
--   - `LocalTerm.toMatrix`: de Wolf p.129 ("we will implicitly treat `H_C` as an `n`-qubit Hamiltonian, by tensoring it with identity for the other qubits"): the term as an operator on all `n` qubits.
--   - `Instance`: de Wolf p.129 (Definition 2), p.130: an instance of the `k`-local Hamiltonian problem: the number of qubits `n`, the terms `H_1, …, H_m`, and the thresholds `a, b`.
--   - `Instance.hamiltonian`: de Wolf p.129 ((14.2)): `H = Σ_j H_j`.
--   - `Instance.Valid`: de Wolf p.129 (Definition 2: "`0 ⪯ H_j ⪯ I`, and given parameters `a, b ∈ [0, m]` with `b − a ≥ 1/poly(n)`"): every term satisfies `0 ⪯ H_j ⪯ I` (positive semidefinite, hence Hermitian), `0 ≤ a`, `b ≤ m`, and the gap satisfies `(b − a) · g(n) ≥ 1` for the polynomial `g` (written without division, so a `g` vanishing at `n` admits no instance).
--   - `encBin`: A natural number in self-delimiting binary: each bit `β` of `Nat.bits` (least significant first) is written as the pair `1β`, and `00` ends the number.
--   - `encInt`: An integer: a sign bit, then the absolute value in self-delimiting binary.
--   - `encRat`: A rational number: numerator, then denominator.
--   - `encTerm`: A term: its `k` wires, then its `4^k` entries (rows and columns in the order of `bitsEquivFin`), each as real part then imaginary part.
--   - `encode`: de Wolf p.130 ("the description of `H` that is given as input will just consist of each of the `m` terms as a `2^k × 2^k` matrix and … bits telling us for each of the `m` terms on which `k` qubits that term acts"): the binary encoding of an instance: `n`, `m`, the terms, `a`, `b`. All numbers are in self-delimiting binary (not unary), so the input length matches the source's description.
--   - `problem`: de Wolf p.129 (Definition 2: "promised that `H`'s minimal eigenvalue `λ_min` is either `≤ a` or `≥ b`, decide which is the case"; p.129: the "`≤ a`" instances form `L_1`, the "`≥ b`" instances form `L_0`): the `k`-local Hamiltonian promise problem with gap `b − a ≥ 1/g(n)`. Strings that encode no valid instance are in `L_*`. The clause "`w ∉ L_1`" in `L_0` only makes the disjointness of the two sets hold by definition: since `encode` is injective (every field is self-delimiting and read left to right) and `a < b` for a valid instance, it removes nothing; injectivity is not proved here.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.LocalHamiltonian

import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

-- encBin, encRat, encInt: identical copies already published on Prove2Me; imported instead of re-declared

/-!
# The k-local Hamiltonian problem (shared definition layer)

de Wolf §14.2, Definition 2 (p.129) and the input description on p.130. An instance is given
classically: the number `n` of qubits, the `m` terms (each a `2^k × 2^k` matrix with
finitely described entries, here Gaussian rationals, together with the `k` qubits it acts on),
and the thresholds `a, b`.
-/

namespace QAlgorithms.LocalHamiltonian

open scoped ComplexOrder

open QAlgorithms.Complexity

/-- de Wolf p.129–130: one term of a `k`-local Hamiltonian on `n` qubits: the `k` distinct qubits it
acts on (in order) and its `2^k × 2^k` matrix, whose entries are Gaussian rationals given by their
real and imaginary parts (the source's "each complex entry represented with poly(n) bits"). -/
structure LocalTerm (n k : ℕ) where
  /-- The qubits the term acts on. -/
  wires : Fin k ↪ Fin n
  /-- The entries, as (real part, imaginary part). -/
  entries : Qubits k → Qubits k → ℚ × ℚ

/-- The `2^k × 2^k` complex matrix of a term. -/
def LocalTerm.mat {n k : ℕ} (t : LocalTerm n k) : Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun a b => ((t.entries a b).1 : ℂ) + ((t.entries a b).2 : ℂ) * Complex.I

/-- de Wolf p.129 ("we will implicitly treat `H_C` as an `n`-qubit Hamiltonian, by tensoring it
with identity for the other qubits"): the term as an operator on all `n` qubits. -/
def LocalTerm.toMatrix {n k : ℕ} (t : LocalTerm n k) : Matrix (Qubits n) (Qubits n) ℂ :=
  embedOp t.mat t.wires

/-- de Wolf p.129 (Definition 2), p.130: an instance of the `k`-local Hamiltonian problem: the
number of qubits `n`, the terms `H_1, …, H_m`, and the thresholds `a, b`. -/
structure Instance (k : ℕ) where
  /-- The number of qubits. -/
  n : ℕ
  /-- The terms `H_j`. -/
  terms : List (LocalTerm n k)
  /-- The threshold `a`. -/
  a : ℚ
  /-- The threshold `b`. -/
  b : ℚ

/-- de Wolf p.129 ((14.2)): `H = Σ_j H_j`. -/
def Instance.hamiltonian {k : ℕ} (I : Instance k) : Matrix (Qubits I.n) (Qubits I.n) ℂ :=
  (I.terms.map LocalTerm.toMatrix).sum

/-- de Wolf p.129 (Definition 2: "`0 ⪯ H_j ⪯ I`, and given parameters `a, b ∈ [0, m]` with
`b − a ≥ 1/poly(n)`"): every term satisfies `0 ⪯ H_j ⪯ I` (positive semidefinite, hence
Hermitian), `0 ≤ a`, `b ≤ m`, and the gap satisfies `(b − a) · g(n) ≥ 1` for the polynomial `g`
(written without division, so a `g` vanishing at `n` admits no instance). -/
def Instance.Valid {k : ℕ} (I : Instance k) (g : Polynomial ℕ) : Prop :=
  (∀ t ∈ I.terms, t.mat.PosSemidef ∧ (1 - t.mat).PosSemidef) ∧
    0 ≤ I.a ∧ I.b ≤ I.terms.length ∧ 1 ≤ (I.b - I.a) * ((g.eval I.n : ℕ) : ℚ)

/-- A term: its `k` wires, then its `4^k` entries (rows and columns in the order of
`bitsEquivFin`), each as real part then imaginary part. -/
def encTerm {n k : ℕ} (t : LocalTerm n k) : Str :=
  (List.ofFn fun a : Fin k => encBin (t.wires a)).flatten ++
    (List.ofFn fun r : Fin (2 ^ k) => (List.ofFn fun c : Fin (2 ^ k) =>
      encRat (t.entries ((bitsEquivFin k).symm r) ((bitsEquivFin k).symm c)).1 ++
      encRat (t.entries ((bitsEquivFin k).symm r) ((bitsEquivFin k).symm c)).2).flatten).flatten

/-- de Wolf p.130 ("the description of `H` that is given as input will just consist of each of the
`m` terms as a `2^k × 2^k` matrix and … bits telling us for each of the `m` terms on which `k`
qubits that term acts"): the binary encoding of an instance: `n`, `m`, the terms, `a`, `b`. All
numbers are in self-delimiting binary (not unary), so the input length matches the source's
description. -/
def encode {k : ℕ} (I : Instance k) : Str :=
  encBin I.n ++ encBin I.terms.length ++ (I.terms.map encTerm).flatten ++ encRat I.a ++ encRat I.b

/-- de Wolf p.129 (Definition 2: "promised that `H`'s minimal eigenvalue `λ_min` is either `≤ a` or
`≥ b`, decide which is the case"; p.129: the "`≤ a`" instances form `L_1`, the "`≥ b`" instances
form `L_0`): the `k`-local Hamiltonian promise problem with gap `b − a ≥ 1/g(n)`. Strings that
encode no valid instance are in `L_*`. The clause "`w ∉ L_1`" in `L_0` only makes the disjointness
of the two sets hold by definition: since `encode` is injective (every field is self-delimiting
and read left to right) and `a < b` for a valid instance, it removes nothing; injectivity is not
proved here. -/
def problem (k : ℕ) (g : Polynomial ℕ) : PromiseProblem where
  yes := {w | ∃ I : Instance k, w = encode I ∧ I.Valid g ∧ minEigenvalue I.hamiltonian ≤ I.a}
  no := {w | (∃ I : Instance k, w = encode I ∧ I.Valid g ∧ (I.b : ℝ) ≤ minEigenvalue I.hamiltonian) ∧
    ¬ ∃ I : Instance k, w = encode I ∧ I.Valid g ∧ minEigenvalue I.hamiltonian ≤ I.a}
  disjoint := Set.disjoint_left.2 fun _ hy hn => hn.2 hy

/-! ### Sanity tests -/

example : encBin 0 = [false, false] := by decide

example : encBin 2 = [true, false, true, true, false, false] := by decide

/-- A term with zero matrix contributes the zero operator. -/
example {n k : ℕ} (w : Fin k ↪ Fin n) : (LocalTerm.mk w fun _ _ => (0, 0)).toMatrix = 0 := by
  ext y z
  simp [LocalTerm.toMatrix, LocalTerm.mat, embedOp]

/-- An instance without terms has `H = 0`. -/
example (n : ℕ) (a b : ℚ) : (Instance.mk (k := 2) n [] a b).hamiltonian = 0 := rfl

end QAlgorithms.LocalHamiltonian


