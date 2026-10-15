-- Prove2me | Definitions.Def_QuantumSDP18_MeasureBE_Setting
-- name    : QuantumSDP18_MeasureBE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:41.127899+00:00
-- url     : https://prove2.me/theorems/7ed3daa2-5445-4baf-bb76-42c57e181263
-- title:
--   §4.1, pp. 24–25 — a two-outcome measurement on a quantum computer: ancillas, acceptance projector, acceptance probability, the block K, U′ = U ⊗ I₂, I ⊗ CNOT
-- statement:
--   These definitions set up the closing remark of §4.1 of van Apeldoorn and Gilyén, which describes how a two-outcome POVM measurement $\{M, I-M\}$ is performed on a quantum computer.
--
--   The input is a mixed state $\rho$ on a finite-dimensional **system** register with computational basis indexed by a finite set $\iota$. A **density matrix** is a positive semidefinite $\rho$ with $\operatorname{Tr}\rho = 1$.
--
--   The procedure attaches $a = c + 1$ **ancilla qubits** in the state $|0\rangle^{\otimes a}$, applies a unitary $U$ to system and ancillas, and measures in the computational basis, accepting when the **last** ancilla qubit reads $|0\rangle$:
--
--   $$
--   \rho \;\to\; \rho\otimes|0\rangle\langle 0|^{\otimes a} \;\to\; U\big(\rho\otimes|0\rangle\langle 0|^{\otimes a}\big)U^\dagger \;\to\; \operatorname{Tr}\Big((I\otimes|0\rangle\langle 0|)\,U\big(\rho\otimes|0\rangle\langle 0|^{\otimes a}\big)U^\dagger\Big).
--   $$
--
--   The objects defined are:
--
--   1. the ancilla register $\{0,1\}^{c}\times\{0,1\}$, whose last factor is the measured qubit, and its all-zero basis state $|0\rangle^{\otimes a}$;
--   2. the isometry $I\otimes|0\rangle^{\otimes a}$ (system first), the projector $|0\rangle\langle 0|^{\otimes a}$ and the state $\rho\otimes|0\rangle\langle 0|^{\otimes a}$;
--   3. the acceptance projector $I\otimes|0\rangle\langle 0|$ on the last qubit, and the acceptance probability $\operatorname{Tr}\big((I\otimes|0\rangle\langle 0|)U(\rho\otimes|0\rangle\langle 0|^{\otimes a})U^\dagger\big)$, kept as a complex number;
--   4. the block $K = (I\otimes\langle 0|^{\otimes a})\,U^\dagger(I\otimes|0\rangle\langle 0|)U\,(I\otimes|0\rangle^{\otimes a})$, an operator on the system;
--   5. with one fresh qubit appended last: $U' = U\otimes I_2$; the gate $I\otimes\mathrm{CNOT}$, where the CNOT is controlled by the measured (last) ancilla qubit and targets the fresh qubit, $|b, t\rangle\mapsto|b, t\oplus b\rangle$; and the isometry $I\otimes|0\rangle^{\otimes a'}$ with $a' = a+1$;
--   6. the regrouping of registers that moves the $a'$ ancilla qubits in front of the system, as Definition 2 of the paper writes a block-encoding.
--
--   These are the objects of the derivation on p. 25 that turns an $\varepsilon$-biased implementation of the measurement into a $(1, a+1, \varepsilon)$-block-encoding of $M$.
--
--   **Formalization Note** The system register is an arbitrary finite type $\iota$ rather than $w$ qubits (a generalization; $w$ qubits is the instance $\iota = \{0,1\}^w$). The number of ancillas is written $a = c+1$, so $a \ge 1$: "the last qubit" is read as the last ancilla qubit. The basis state $|0\rangle$ of a register is its all-`false` index. The CNOT is the platform's `QAlgorithms.cnot` (control first), placed on (last ancilla, fresh qubit) by a reindexing; the page does not print the CNOT's direction, and this is the only direction under which the identity of p. 25 holds.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, pp. 24–25, §4.1 closing remark (the procedure display, (14), and the display after 'Finally let a′ := a + 1')

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Defs_Gates

namespace QuantumSDP18.MeasureBE

open scoped ComplexOrder

/-!
# Two-outcome measurements implemented on a quantum computer (§4.1, pp. 24–25)

J. van Apeldoorn, A. Gilyén, *Improvements in quantum SDP-solving with applications*,
arXiv:1804.05058v1, §4.1, pp. 24–25 (the closing remark "As a final remark …").

The input state `ρ` lives on a finite system register with basis `ι`. We attach `a = c + 1`
ancilla qubits, indexed by `Anc c = Qubits c × Bool`; the `Bool` factor is the **last** qubit, the
one that is measured. The basis state `|0⟩` of a register is its all-`false` index.
-/

/-- The `a = c + 1` ancilla qubits of §4.1, p. 25: the first `c` of them (`Qubits c`) and the last
one (`Bool`), which is the qubit measured at the end of the procedure. -/
abbrev Anc (c : ℕ) := QAlgorithms.Qubits c × Bool

/-- The all-`|0⟩` basis state `|0⟩^{⊗a}` of the ancilla register. -/
def ancZero (c : ℕ) : Anc c := (fun _ => false, false)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A mixed state (density matrix) `ρ` on the system: positive semidefinite with trace one. -/
def IsDensity (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- `I ⊗ |0⟩^{⊗a}`, the isometry attaching the `a` ancilla qubits in the state `|0⟩^{⊗a}`
(system first, ancillas second). -/
def ketZero (c : ℕ) : Matrix (ι × Anc c) ι ℂ :=
  Matrix.of fun x i => if x.1 = i ∧ x.2 = ancZero c then 1 else 0

/-- The projector `|0⟩⟨0|^{⊗a}` onto the all-zero state of the ancilla register. -/
def zeroProj (c : ℕ) : Matrix (Anc c) (Anc c) ℂ :=
  Matrix.of fun z w => if z = ancZero c ∧ w = ancZero c then 1 else 0

/-- `ρ ⊗ |0⟩⟨0|^{⊗a}`: the input state with the ancillas attached. -/
def embedZero (c : ℕ) (ρ : Matrix ι ι ℂ) : Matrix (ι × Anc c) (ι × Anc c) ℂ :=
  Matrix.kroneckerMap (· * ·) ρ (zeroProj c)

/-- The acceptance projector `I ⊗ |0⟩⟨0|` on the last qubit (the measured ancilla qubit):
the diagonal matrix with entry `1` exactly at the basis states whose last qubit is `0`. -/
def accProj (c : ℕ) : Matrix (ι × Anc c) (ι × Anc c) ℂ :=
  Matrix.diagonal fun x => if x.2.2 = false then 1 else 0

/-- The acceptance probability of the procedure on input `ρ` (p. 25, last term of the summary):
`Tr((I ⊗ |0⟩⟨0|) U (ρ ⊗ |0⟩⟨0|^{⊗a}) U†)`, kept as a complex number. -/
def accProb (c : ℕ) (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) (ρ : Matrix ι ι ℂ) : ℂ :=
  (accProj (ι := ι) c * U * embedZero c ρ * U.conjTranspose).trace

/-- The block `(I ⊗ ⟨0|^{⊗a}) U† (I ⊗ |0⟩⟨0|) U (I ⊗ |0⟩^{⊗a})` of p. 25. -/
def blockK (c : ℕ) (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) : Matrix ι ι ℂ :=
  (ketZero (ι := ι) c).conjTranspose * U.conjTranspose * accProj (ι := ι) c * U * ketZero (ι := ι) c

/-- `U′ := U ⊗ I₂` (p. 25): `U` on the system and the `a` ancillas, the identity on one fresh
qubit, placed last. -/
def Uprime (c : ℕ) (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) :
    Matrix ((ι × Anc c) × Bool) ((ι × Anc c) × Bool) ℂ :=
  Matrix.kroneckerMap (· * ·) U (1 : Matrix Bool Bool ℂ)

/-- Regrouping of registers used to place the CNOT: `((i, z), (b, t)) ↦ ((i, (z, b)), t)`, where
`b` is the last (measured) ancilla qubit and `t` the fresh qubit. -/
def cnotRegs (c : ℕ) : (ι × QAlgorithms.Qubits c) × (Bool × Bool) ≃ (ι × Anc c) × Bool where
  toFun x := ((x.1.1, (x.1.2, x.2.1)), x.2.2)
  invFun y := ((y.1.1, y.1.2.1), (y.1.2.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- `I ⊗ CNOT` (p. 25): the platform's `QAlgorithms.cnot` (`|b, t⟩ ↦ |b, t ⊕ b⟩`, control first)
acting on the last ancilla qubit `b` (control) and the fresh qubit `t` (target), and the identity
on the system and the other `c` ancilla qubits. -/
def cnotLast (c : ℕ) : Matrix ((ι × Anc c) × Bool) ((ι × Anc c) × Bool) ℂ :=
  Matrix.reindex (cnotRegs c) (cnotRegs c)
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (ι × QAlgorithms.Qubits c) (ι × QAlgorithms.Qubits c) ℂ)
      QAlgorithms.cnot)

/-- `I ⊗ |0⟩^{⊗a′}` with `a′ = a + 1`: attaches the `a` ancillas and the fresh qubit, all in
`|0⟩`. -/
def ketZeroPrime (c : ℕ) : Matrix ((ι × Anc c) × Bool) ι ℂ :=
  Matrix.of fun x i => if x.1 = (i, ancZero c) ∧ x.2 = false then 1 else 0

/-- Moves the `a′ = a + 1` ancilla qubits in front of the system,
`((i, z), b) ↦ ((z, b), i)`, as `QAlgorithms.IsBlockEncoding` (Definition 2, p. 4) expects. -/
def reorder (c : ℕ) : (ι × Anc c) × Bool ≃ (Anc c × Bool) × ι where
  toFun x := ((x.1.2, x.2), x.1.1)
  invFun y := ((y.2, y.1.1), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end QuantumSDP18.MeasureBE


