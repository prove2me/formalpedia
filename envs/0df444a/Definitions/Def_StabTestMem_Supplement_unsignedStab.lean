-- Prove2me | Definitions.Def_StabTestMem_Supplement_unsignedStab
-- name    : StabTestMem_Supplement_unsignedStab
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:39:59.8476+00:00
-- url     : https://prove2.me/theorems/872ef01a-c4c7-49e6-af78-a0e5db145b4a
-- title:
--   The unsigned stabilizer group $M_\psi$
-- statement:
--   For an $n$-qubit unit vector $|\psi\rangle$, the **unsigned stabilizer group** is the set of Pauli labels $u=(x,z)\in\mathbb F_2^n\times\mathbb F_2^n$ whose Hermitian Pauli operator $P_u=i^{x\cdot z}X^xZ^z$ stabilizes $|\psi\rangle$ up to a sign:
--   $$M_\psi=\{u\in\mathbb F_2^{2n}:|\langle\psi|P_u|\psi\rangle|=1\}=\{u:P_u|\psi\rangle=\pm|\psi\rangle\}.$$
--
--   For a stabilizer state, $M_\psi$ is a Lagrangian subspace of $\mathbb F_2^{2n}$. Bell sampling sees only $|\langle\psi^*|P_u|\psi\rangle|^2$, so it can recover $M_\psi$ but not the signs; $M_\psi$ is what Theorem 6.2 recovers.
--
--   **Formalization Note** $P_u$ is the published `StabTestMem.weyl`, with labels the published `CutRankSched.Pauli n`. Since $P_u$ is Hermitian and unitary, $|\langle\psi|P_u|\psi\rangle|=1$ for a unit vector $\psi$ is equivalent to $P_u\psi=\pm\psi$. That $M_\psi$ is a subspace is a fact, not part of the definition.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §6.1, pp. 52–53; Lemma 4.3, p. 26

import Definitions.Def_StabTestMem_weyl

namespace StabTestMem.Supplement

open QAlgorithms

/-- **The unsigned stabilizer group `M_ψ ≤ F₂^{2n}`.** Arunachalam, Schatzki, *Optimal stabilizer
testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §6.1,
p. 52: "Let |ϕ⟩ be a state with full-support stabilizer form with unsigned stabilizer group
M_ϕ ≤ F_2^{2n}"; p. 53: Bell sampling "cannot distinguish the cases P_u|ψ_j⟩ = +|ψ_j⟩ and
P_u|ψ_j⟩ = −|ψ_j⟩".

`unsignedStab ψ` is the set of Pauli labels `u = (x, z)` (the published `CutRankSched.Pauli n`)
whose Hermitian Weyl operator `P_u` (the published `StabTestMem.weyl`) satisfies
`|⟨ψ|P_u|ψ⟩| = 1`.

**Formalization Note.** For a unit vector `ψ`, `P_u` being Hermitian and unitary, `|⟨ψ|P_u|ψ⟩| = 1`
holds iff `P_u ψ = ±ψ`, the paper's "stabilize |ψ⟩ up to signs". For a stabilizer state this set
is a Lagrangian subspace of size `2ⁿ`; that is a fact, not part of the definition. -/
noncomputable def unsignedStab {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    Set (CutRankSched.Pauli n) :=
  {u | ‖inner ℂ ψ (act (weyl u) ψ)‖ = 1}

end StabTestMem.Supplement


