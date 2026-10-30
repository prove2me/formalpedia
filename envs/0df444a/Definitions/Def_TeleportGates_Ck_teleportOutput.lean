-- Prove2me | Definitions.Def_TeleportGates_Ck_teleportOutput
-- name    : TeleportGates_Ck_teleportOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:18.477486+00:00
-- url     : https://prove2.me/theorems/c4787bca-dac1-4d8d-87bb-02e32cab4225
-- title:
--   Post-measurement output state $(\langle\beta|\otimes I)(\psi\otimes\Phi)$
-- statement:
--   Let $\psi\in\mathbb C^{\iota}$ be an input state, $\Phi\in\mathbb C^{\iota}\otimes\mathbb C^{\iota}$ a resource state (upper register, lower register) and $\beta\in\mathbb C^{\iota}\otimes\mathbb C^{\iota}$ a vector on (input register, upper register). The output vector is
--
--   $$(\langle\beta|\otimes I)(\psi\otimes\Phi)(c)=\sum_{a}\sum_{b}\overline{\beta(a,b)}\,\psi(a)\,\Phi(b,c).$$
--
--   When the input and upper registers are measured and the outcome is $\beta$, this is the unnormalized state left in the lower register: its squared norm is the probability of outcome $\beta$ (Born rule), and the paper's $|\psi_{\mathrm{out}}\rangle$ is this vector up to normalization.
--
--   **Formalization Note** The literal contraction with complex conjugation of $\beta$; nothing is normalized.
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §I, p. 1 (the output qubit after the Bell measurement) and §II, Eq. (4), p. 3 (|ψout⟩)

import Mathlib

namespace TeleportGates.Ck

/-- **The post-measurement state of the output register for Bell outcome `β`.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §I, p. 1 ("The output qubit is then in the
initial state |α⟩, but with an additional single-qubit Pauli operation") and §II, Eq. (4), p. 3
("take the input state |ψ⟩ and do Bell basis measurements on this and the n upper qubits of
|Ψn_U⟩, leaving us with n qubits in the state |ψout⟩").

For an input state `ψ` on `ι`, a resource state `Φ` on `ι × ι` (upper register, lower
register) and a vector `β` on `ι × ι` (input register, upper register), `teleportOutput β ψ Φ` is
`(⟨β| ⊗ I)(ψ ⊗ Φ)`:
`teleportOutput β ψ Φ c = ∑_a ∑_b conj(β (a, b)) · ψ a · Φ (b, c)`.
When `β` is a measurement outcome, this is the unnormalized state of the lower register after the
input and upper registers are projected onto `β`; its squared norm is the Born probability of
outcome `β`, and the paper's `|ψout⟩` is this vector up to normalization.

**Formalization Note.** The vector is the literal contraction; nothing is normalized. `star` is
complex conjugation, so the definition is the partial inner product for every `β`. -/
noncomputable def teleportOutput {ι : Type*} [Fintype ι] (β : EuclideanSpace ℂ (ι × ι))
    (ψ : EuclideanSpace ℂ ι) (Φ : EuclideanSpace ℂ (ι × ι)) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun c => ∑ a : ι, ∑ b : ι, star (β (a, b)) * ψ a * Φ (b, c)

end TeleportGates.Ck


