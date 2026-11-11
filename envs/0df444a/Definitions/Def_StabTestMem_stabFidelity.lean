-- Prove2me | Definitions.Def_StabTestMem_stabFidelity
-- name    : StabTestMem_stabFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:33.453976+00:00
-- url     : https://prove2.me/theorems/ece9deee-fe7b-4a8d-bfc0-89375f9b514d
-- title:
--   Stabilizer fidelity $\mathcal F_{\mathsf{Stab}}(|\psi\rangle)$
-- statement:
--   Let $\mathsf{Stab}$ be the set of $n$-qubit stabilizer states. The **stabilizer fidelity** of a state $|\psi\rangle$ is
--
--   $$\mathcal F_{\mathsf{Stab}}(|\psi\rangle)=\max_{|\phi\rangle\in\mathsf{Stab}}|\langle\psi|\phi\rangle|^2 .$$
--
--   It equals $1$ exactly when $|\psi\rangle$ is a stabilizer state (up to a global phase), and measures how close $|\psi\rangle$ is to the class $\mathsf{Stab}$. The testing problem of the paper is to tell $\mathcal F_{\mathsf{Stab}}=1$ from $\mathcal F_{\mathsf{Stab}}\le1-\varepsilon$.
--
--   **Formalization Note** Stabilizer states are the shared `QAlgorithms.IsStabilizerState`: a unit vector fixed by every element of a commuting subgroup of the Pauli group of order $2^n$ not containing $-I$ (the signs of Definition 2.2 are part of the group elements $\pm P_u$). The maximum is written as the supremum of the set of overlaps; this set is nonempty, bounded and finite-valued, so the supremum is attained.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §1.1, p. 4; Definition 2.2, p. 13

import Definitions.Def_QAlgorithms_Defs_StabilizerLearning

namespace StabTestMem

open QAlgorithms

/-- **Stabilizer fidelity `F_Stab(|ψ⟩) = max_{|ϕ⟩ ∈ Stab} |⟨ψ|ϕ⟩|²`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §1.1, p. 4: "For a
state |ψ⟩, let F_Stab(|ψ⟩) := max_{|ϕ⟩∈Stab} |⟨ψ|ϕ⟩|^2 be the fidelity of |ψ⟩ with respect to
Stab", where Stab is the class of `n`-qubit stabilizer states (Definition 2.2, p. 13).

**Formalization Note.** Stabilizer states are `QAlgorithms.IsStabilizerState` (a unit vector
fixed by every element of a commuting subgroup of the Pauli group of order `2ⁿ` not containing
`−I`; the signs `χ(u)` of Definition 2.2 are absorbed into the group elements `±P_u`). The max
is written `sSup` of the set of overlaps: the set is nonempty (`|0ⁿ⟩` is a stabilizer state),
bounded by `‖ψ‖²`, and takes finitely many values (finitely many stabilizer states up to a global
phase), so `sSup` is attained and equals the paper's max. -/
noncomputable def stabFidelity {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) : ℝ :=
  sSup {f : ℝ | ∃ φ : EuclideanSpace ℂ (Qubits n), IsStabilizerState φ ∧ f = ‖inner ℂ φ ψ‖ ^ 2}

end StabTestMem


