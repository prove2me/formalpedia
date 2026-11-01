-- Prove2me | Definitions.Def_HeisenbergRep_Knill_stabilizerOf
-- name    : HeisenbergRep_Knill_stabilizerOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:28.612935+00:00
-- url     : https://prove2.me/theorems/e1562dc6-466b-4cce-8ad5-14eaab13ab73
-- title:
--   The stabilizer $S$ of a set of allowed inputs (Eq. (19))
-- statement:
--   Let $\Psi$ be a set of vectors of $\mathbb C^{2^n}$, the allowed inputs of an $n$-qubit computer, and let $\mathcal P$ be the $n$-qubit Pauli group (all $i^cP_1\otimes\cdots\otimes P_n$, $c\in\mathbb Z/4$, $P_q\in\{I,X,Y,Z\}$). The **stabilizer** of $\Psi$ is
--
--   $$S=\{M\in\mathcal P \;:\; M|\psi\rangle=|\psi\rangle\ \text{for all }|\psi\rangle\in\Psi\}.$$
--
--   It is closed under products and inverses, hence a subgroup of the unitary group $U(2^n)$ (and of $\mathcal P$).
--
--   The stabilizer is the object the Heisenberg representation follows in place of the state: a state, or a set of allowed states, is described by the Pauli operators that fix it.
--
--   **Formalization Note** No hypothesis on $\Psi$ is built in; theorems about $S$ state the ones they need (for instance that some allowed input is nonzero). The closure properties are proved inside the definition.
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §4, Eq. (19), p. 9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer

/-- **The stabilizer `S` of a set of allowed input states (Eq. (19)).**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §4,
Eq. (19), p. 9: "it will be helpful to consider the set of operators in `P` for which the input
states are `+1` eigenvectors. The set of such operators is closed under multiplication, and
therefore forms a group, known as the stabilizer `S`.
`S = {M ∈ P such that M|ψ⟩ = |ψ⟩ for all allowed inputs |ψ⟩}`".

`stabilizerOf Ψ` is the subgroup of the unitary group `U(2^n)` whose elements are the members `M`
of the Pauli group `P = pauliGroup n` with `M ψ = ψ` for every `ψ ∈ Ψ`.

**Formalization Note.** The set of allowed inputs `Ψ` is an arbitrary set of vectors of
`ℂ^{2^n}` (no hypothesis is built in: the theorems about `S` add the ones they need). The closure
under products and inverses (`M⁻¹ = M†`, and `M† ψ = M† M ψ = ψ`) is proved here, as the paper's
"therefore forms a group". -/
noncomputable def stabilizerOf {n : ℕ} (Ψ : Set (EuclideanSpace ℂ (Qubits n))) :
    Subgroup (Matrix.unitaryGroup (Qubits n) ℂ) where
  carrier := {U | U ∈ pauliGroup n ∧ ∀ ψ ∈ Ψ, act (U : Matrix (Qubits n) (Qubits n) ℂ) ψ = ψ}
  one_mem' := by
    refine ⟨one_mem _, fun ψ _ => ?_⟩
    simp [act]
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun ψ hψ => ?_⟩
    have key : act ((a * b : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) ψ =
        act (a : Matrix (Qubits n) (Qubits n) ℂ) (act (b : Matrix (Qubits n) (Qubits n) ℂ) ψ) := by
      simp [act, Matrix.mulVec_mulVec]
    rw [key, hb' ψ hψ, ha' ψ hψ]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun ψ hψ => ?_⟩
    have key : act ((a⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ)
        (act (a : Matrix (Qubits n) (Qubits n) ℂ) ψ) =
        act ((a⁻¹ * a : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) ψ := by
      simp [act, Matrix.mulVec_mulVec]
    rw [ha' ψ hψ, inv_mul_cancel] at key
    rw [key]
    simp [act]

end HeisenbergRep.Knill


