-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_IsSupercoherent
-- name    : BaconThesis_Supercoherence_IsSupercoherent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:36.741775+00:00
-- url     : https://prove2.me/theorems/6c4dcb07-da2b-49d9-9c11-f0154b7ade5b
-- title:
--   Supercoherent Hamiltonian (Definition 15.2.1)
-- statement:
--   Definition 15.2.1 (Supercoherence). An $n$-qubit Hamiltonian $H$ is **supercoherent** if
--
--   1. $H$ is Hermitian;
--   2. its ground state is degenerate: with $E$ the lowest eigenvalue of $H$ and $\mathcal G$ the eigenspace of $E$, $\dim \mathcal G \ge 2$;
--   3. every single-qubit operator takes the system out of the ground space, in the form of (15.10): for every qubit $k$, every traceless $2\times 2$ matrix $O$ and all $|i\rangle, |j\rangle \in \mathcal G$,
--
--   $$\langle j |\, O^{(k)} \,| i \rangle = 0 ,$$
--
--   where $O^{(k)}$ is $O$ acting on qubit $k$. Equivalently, every such $O^{(k)}$ maps $\mathcal G$ into its orthogonal complement, the span of the higher-energy eigenstates.
--
--   Information stored in such a degenerate ground space is the book's supercoherent qubit: every single-qubit error must raise the energy, so at low temperature only heating processes can decohere it.
--
--   **Formalization Note** "Every single qubit operator" ranges over the traceless operators, the span of $\sigma_x, \sigma_y, \sigma_z$ (the single-qubit errors $\sigma_\alpha^{(i)}$ of §15.2; p.172 lists $|0\rangle\langle 1|$, $|1\rangle\langle 0|$ and $\sigma_z$). Read over every operator, (15.10) with $o = I$ would require $\langle i|i\rangle = 0$ for every ground state, and no Hamiltonian would qualify; the identity part of an operator leaves every state in place. The book's remark extending the definition to arbitrary subsystems is not formalized; this definition is the qubit case it states.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Definition 15.2.1 (Supercoherence) and eq. (15.10), pp.170–171 (PDF pp.187–188)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_onQubit
import Definitions.Def_BaconThesis_Supercoherence_groundSpace
import Definitions.Def_BaconThesis_Supercoherence_IsGroundEnergy

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, Definition 15.2.1 (Supercoherence) with eq. (15.10), pp.170–171 (PDF pp.187–188):
"A system of qubits with a system Hamiltonian H which has a degenerate ground state and for which
every single qubit operator takes the system out states in this degenerate ground state is called a
supercoherent Hamiltonian", with the condition (15.10) `⟨j|o^{(k)}|i⟩ = 0` for all `|i⟩, |j⟩` in the
degenerate ground state and every single-subsystem operator `o^{(k)}` acting on the `k`th subsystem.

An `n`-qubit Hamiltonian `H` is supercoherent when
1. `H` is Hermitian;
2. its ground space (the eigenspace of its lowest eigenvalue `E`) has dimension at least 2;
3. for every qubit `k`, every traceless single-qubit operator `O` and all ground states `ψ, φ`,
   `⟨φ| O^{(k)} |ψ⟩ = 0`, i.e. `O^{(k)}` maps the ground space into its orthogonal complement.

**Formalization Note.** *Reading of "every single qubit operator".* The quantifier ranges over the
traceless operators `O` (the span of `σ_x, σ_y, σ_z`, the single-qubit errors `σ_α^{(i)}` the
section uses; p.172 lists `|0⟩⟨1|`, `|1⟩⟨0|`, `σ_z`). Read literally over every operator, (15.10)
with `o = I` would demand `⟨i|i⟩ = 0` for every ground state and no Hamiltonian would qualify; the
identity component of an operator leaves every state in place, so it is excluded. The ground
energy is an existential `E` with `IsGroundEnergy H E` (unique when it exists). Inner product
`⟨φ|w⟩ = star φ ⬝ᵥ w`. The more general subsystem version sketched after the definition is not
formalized. -/
def IsSupercoherent {n : ℕ} (H : Operator n) : Prop :=
  H.IsHermitian ∧
    ∃ E : ℝ, IsGroundEnergy H E ∧ 2 ≤ Module.finrank ℂ (groundSpace H E) ∧
      ∀ (k : Fin n) (O : Matrix (Fin 2) (Fin 2) ℂ), O.trace = 0 →
        ∀ ψ ∈ groundSpace H E, ∀ φ ∈ groundSpace H E, star φ ⬝ᵥ (onQubit k O *ᵥ ψ) = 0

end BaconThesis.Supercoherence


