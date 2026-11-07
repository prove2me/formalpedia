-- Prove2me | Definitions.Def_QiOPoQ_GateSet
-- name    : QiOPoQ_GateSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:35.700496+00:00
-- url     : https://prove2.me/theorems/fb1d5429-cc36-4b73-8502-fc45eaf04227
-- title:
--   The gate set: finitely many unitaries with $I$, $X$, CNOT, closed under adjoints
-- statement:
--   Section 3.1 fixes "a finite universal gate set" that "contains $I$, $X$, and CNOT, and is closed under adjoints". A gate set here consists of finitely many gates, each acting on a fixed number of qubits and given by a unitary matrix on $\{0,1\}^{\text{arity}}$. Three gates are designated: the identity $I$ and the bit flip $X$ on one qubit, and CNOT on two qubits (first gate qubit the control, second the target). Every gate has an adjoint gate on the same number of qubits whose matrix is its conjugate transpose.
--
--   The adjoint closure makes $V^\dagger$ a circuit with exactly as many gates as $V$, which is what makes the circuits $D_x$ of Lemma 4.4 have the same shape as the padded circuits.
--
--   **Formalization Note** Universality is not part of the structure: no step of Section 4 uses it. Every statement over an arbitrary gate set applies in particular to any finite universal gate set of the required form, such as Clifford+T with $S^\dagger, T^\dagger$, $I$ and $X$. Measurement gates are not part of the gate set, since the paper passes to the deferred-measurement form.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13

import Mathlib

set_option autoImplicit false

namespace QiOPoQ

/-- **The gate set of §3.1.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage
and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), §3.1,
p.13: "We fix a finite universal gate set, so that the gate count and description length are
polynomially related. Further, it will be convenient for us to pick the gate set so that it
contains I, X, and CNOT, and is closed under adjoints."

A gate set is a finite list of `k` gates; gate `i` acts on `arity i` qubits and is given by its
unitary matrix on `{0,1}^{arity i}` (row = output string, column = input string). Three gates are
designated: the identity `I` and the bit flip `X` (one qubit) and `CNOT` (two qubits, wire `0`
of the gate is the control, wire `1` the target). Every gate `i` has an adjoint gate `adj i` on
the same number of qubits whose matrix is the conjugate transpose of gate `i`.

**Formalization Note.** Universality is not assumed: no step of §4 uses it, so every theorem
stated for an arbitrary `GateSet` covers in particular every finite universal gate set with
`I, X, CNOT` closed under adjoints (e.g. Clifford+T with `S†, T†`). Measurement gates are not
part of the gate set: as on p.13, a circuit is taken in its deferred-measurement form, a
unitary `U_C` with input, ancilla, output and junk registers. -/
structure GateSet where
  /-- The number of gates. -/
  k : ℕ
  /-- The number of qubits gate `i` acts on. -/
  arity : Fin k → ℕ
  /-- The matrix of gate `i`, entry `(y, y')` = `⟨y|U_i|y'⟩`. -/
  mat : (i : Fin k) → Matrix (Fin (arity i) → Bool) (Fin (arity i) → Bool) ℂ
  /-- Every gate is unitary. -/
  mat_unitary : ∀ i, mat i ∈ Matrix.unitaryGroup (Fin (arity i) → Bool) ℂ
  /-- The designated identity gate `I`. -/
  gI : Fin k
  /-- The designated bit flip gate `X`. -/
  gX : Fin k
  /-- The designated `CNOT` gate. -/
  gCNOT : Fin k
  arity_gI : arity gI = 1
  arity_gX : arity gX = 1
  arity_gCNOT : arity gCNOT = 2
  /-- `I` is the identity matrix. -/
  mat_gI : mat gI = 1
  /-- `X|a⟩ = |¬a⟩`. -/
  mat_gX : ∀ y y' : Fin (arity gX) → Bool, mat gX y y' = if ∀ j, y j = !(y' j) then 1 else 0
  /-- `CNOT|c, a⟩ = |c, a ⊕ c⟩`, control = gate wire `0`, target = gate wire `1`. -/
  mat_gCNOT : ∀ c t : Fin (arity gCNOT), c.val = 0 → t.val = 1 →
    ∀ y y' : Fin (arity gCNOT) → Bool,
      mat gCNOT y y' = if y c = y' c ∧ y t = (y' t ^^ y' c) then 1 else 0
  /-- The adjoint gate. -/
  adj : Fin k → Fin k
  arity_adj : ∀ i, arity (adj i) = arity i
  /-- The matrix of `adj i` is the conjugate transpose of the matrix of `i` (indices transported
  along `arity (adj i) = arity i`). -/
  mat_adj : ∀ i, mat (adj i) =
    Matrix.reindex (Equiv.arrowCongr (finCongr (arity_adj i).symm) (Equiv.refl Bool))
      (Equiv.arrowCongr (finCongr (arity_adj i).symm) (Equiv.refl Bool)) (mat i).conjTranspose

end QiOPoQ


