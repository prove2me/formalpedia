-- Prove2me | Definitions.Def_RainsSep_Distill_pauliFid
-- name    : RainsSep_Distill_pauliFid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:58:10.937876+00:00
-- url     : https://prove2.me/theorems/05e3318a-7612-4e14-b1e0-2df36a4bb930
-- title:
--   $F_{\mathcal P}(E)$: output fidelity on a Pauli-twisted maximally entangled state
-- statement:
--   Let $V$ be an $n$-qubit register, $\mathcal P$ a superoperator from $V\otimes V$ to $\mathbb C^K\otimes\mathbb C^K$, and $E=E_1\otimes\cdots\otimes E_n$ a tensor product of matrices from $\{1,\sigma_x,\sigma_y,\sigma_z\}$. Then
--
--   $$
--   F_{\mathcal P}(E)=F\big(\mathcal P(\rho(E))\big)
--   $$
--
--   is the entanglement fidelity of the output of $\mathcal P$ on the maximally entangled state of $n$ pairs twisted by $E$ on Alice's side.
--
--   **Formalization Note** $E$ is the phase-$+1$ Pauli product with $\sigma_y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$, given by its list of single-qubit labels.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eqs. (14)–(15), p. 2, and Eqs. (21)–(22), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_RainsSep_Distill_entFidelity
import Definitions.Def_RainsSep_Distill_choiState

namespace RainsSep.Distill

/-- **`F_P(E)`: the output fidelity on the Pauli-twisted maximally entangled state.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eqs. (14)–(15), p. 2: "To any state ρ on V⊗V, we can associate a fidelity F_P(ρ) between 0
and 1, namely the fidelity of P(ρ). … F_P(U) := F_P(ρ(U))"; Eqs. (21)–(22): "E ranges over the
set E of tensor products of matrices from the set {1, σx, σy, σz}".

For a superoperator `P` from `V ⊗ V` (`V` an `n`-qubit register) to `ℂ^K ⊗ ℂ^K` and a Pauli
product `E = E_1 ⊗ ⋯ ⊗ E_n` (labels `o`), `F_P(E) = F(P(ρ(E)))`.

**Formalization Note.** `E` is the phase-`+1` product `pauliOps o` with
`σy = [[0, −i], [i, 0]]`. -/
noncomputable def pauliFid {n K : ℕ}
    (P : QAlgorithms.Superop (QAlgorithms.Qubits n × QAlgorithms.Qubits n) (Fin K × Fin K))
    (o : Fin n → QAlgorithms.Stabilizer.Pauli) : ℝ :=
  entFidelity (P (choiState (QAlgorithms.pauliOps o)))

end RainsSep.Distill


