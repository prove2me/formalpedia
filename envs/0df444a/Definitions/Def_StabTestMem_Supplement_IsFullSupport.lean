-- Prove2me | Definitions.Def_StabTestMem_Supplement_IsFullSupport
-- name    : StabTestMem_Supplement_IsFullSupport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:40:28.339291+00:00
-- url     : https://prove2.me/theorems/825b1d42-ccf7-4137-a84b-e9dd77e56300
-- title:
--   Full-support states
-- statement:
--   An $n$-qubit state $|\psi\rangle=\sum_y\psi_y|y\rangle$ is **full-support** if every computational-basis amplitude is nonzero:
--   $$\psi_y\neq0\quad\text{for all }y\in\{0,1\}^n.$$
--
--   For a stabilizer state this is equivalent to $M_\psi\cap\mathcal Z=\{0\}$, where $\mathcal Z=\{0\}\times\mathbb F_2^n$ is the all-$Z$ Lagrangian, and to $M_\psi=\{(u,Bu):u\in\mathbb F_2^n\}$ for a unique symmetric $B$. It is the hypothesis of Theorem 6.2.
--
--   **Formalization Note** The amplitude form is the definition; the equivalence with $M_\psi\cap\mathcal Z=\{0\}$ for stabilizer states is the paper's observation on p. 52.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §6.1, p. 52

import Definitions.Def_QAlgorithms_Defs_Basic

namespace StabTestMem.Supplement

open QAlgorithms

/-- **Full-support state.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with
limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §6.1, p. 52: "Let |ϕ⟩ be a
state with full-support stabilizer form … Observe that |ϕ⟩ is full-support if and only if
M_ϕ ∩ Z = {0}", with `Z = {0} × F_2^n` the all-Z Lagrangian.

`IsFullSupport ψ`: every computational-basis amplitude of `ψ` is nonzero.

**Formalization Note.** The amplitude form is used; for a stabilizer state it is equivalent to the
paper's `M_ψ ∩ Z = {0}` (the support of a stabilizer state is an affine subspace of size
`2^{n − dim(M_ψ ∩ Z)}`). -/
def IsFullSupport {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) : Prop :=
  ∀ y : Qubits n, ψ y ≠ 0

end StabTestMem.Supplement


