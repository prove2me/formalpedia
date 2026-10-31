-- Prove2me | Definitions.Def_RainsSep_Distill_choiState
-- name    : RainsSep_Distill_choiState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:57:07.415501+00:00
-- url     : https://prove2.me/theorems/c178f386-144d-432d-8f32-42359993189d
-- title:
--   The state $\rho(U)=2^{-n}|U^t\rangle\langle U^t|$
-- statement:
--   Let $V$ be an $n$-qubit register and $U$ an operator on $V$. Then
--
--   $$
--   \rho(U)=2^{-n}\,|U^t\rangle\langle U^t| ,
--   $$
--
--   an operator on $V\otimes V$ with entries $\rho(U)_{(a,b),(c,d)}=2^{-n}U_{ab}\overline{U_{cd}}$. For $U=1$ it is the maximally entangled state of $n$ pairs; for a Pauli product $E$ it is that state with $E$ applied to Alice's half. Mixtures of such states (in particular $\Delta(\epsilon)^{\otimes n}$) have output fidelities that are linear combinations of the $F_{\mathcal P}(U)$.
--
--   **Formalization Note** Defined for every operator $U$ (the paper takes $U$ unitary). Alice's qubit $k$ is paired with Bob's qubit $k$.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (14), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_RainsSep_Distill_opVec

namespace RainsSep.Distill

/-- **The state `ρ(U) = 2^{−n} |Uᵗ⟩⟨Uᵗ|`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (14), p. 2: "Consider, in particular, the case in which ρ is the pure state
ρ(U) = 2^{−n}|U^t⟩⟨U^t|, (14) where U is an arbitrary unitary operation."

For an operator `U` on the `n`-qubit register `V`, `ρ(U)` is the operator on `V ⊗ V` with
entries `ρ(U)_{(a,b),(c,d)} = 2^{−n} U_{ab} \overline{U_{cd}}` (since `|Uᵗ⟩_{(a,b)} = U_{ab}`).
`ρ(1)` is the maximally entangled state of `n` pairs, and `ρ(E)` for a Pauli product `E` is
that state with `E` applied to Alice's half.

**Formalization Note.** Defined for every operator `U` (the paper takes `U` unitary; for a
non-unitary `U` the trace is not 1). Alice's qubit `k` is paired with Bob's qubit `k`, as in
`pairPower`. -/
noncomputable def choiState {n : ℕ} (U : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ) :
    Matrix (QAlgorithms.Qubits n × QAlgorithms.Qubits n)
      (QAlgorithms.Qubits n × QAlgorithms.Qubits n) ℂ :=
  ((2 ^ n : ℂ)⁻¹) • QAlgorithms.pureDensity (opVec U.transpose)

end RainsSep.Distill


