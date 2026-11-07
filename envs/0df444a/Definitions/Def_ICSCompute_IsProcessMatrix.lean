-- Prove2me | Definitions.Def_ICSCompute_IsProcessMatrix
-- name    : ICSCompute_IsProcessMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:48:08.349199+00:00
-- url     : https://prove2.me/theorems/d0278838-0b71-485e-b570-4e26e9577716
-- title:
--   Process matrix (for $n$ single-qubit feedback pairs)
-- statement:
--   Let $W\in\mathcal L(H_{AI}\otimes H_P\otimes H_{AO}\otimes H_F)$ with $n$ single-qubit feedback pairs. $W$ is a **process matrix** if
--
--   1. $W$ is positive semidefinite, and
--   2. for every collection of auxiliary registers $E_i, E'_i$ and every choice of local quantum channels $A_i : \mathcal L(H_{S_i}\otimes H_{E_i}) \to \mathcal L(H_{R_i}\otimes H_{E'_i})$, the induced map $\mathrm{PMO}(W,H_{AI},H_{AO})[A]$ is a quantum channel.
--
--   Validity is the defining constraint of the process-matrix formalism: whatever local operations the laboratories apply, the global result must be a physical channel.
--
--   **Formalization Note** The paper's default of $n$ separate single-qubit feedback pairs (stated after Definition 4.4) is built in. The auxiliary registers are qubit registers of arbitrary sizes, input and output sizes independent, and the local operations range over all quantum channels (not only unitaries).
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 4.4, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ICSCompute_IsQuantumChannel
import Definitions.Def_ICSCompute_pmo

namespace ICSCompute

open QAlgorithms
open scoped ComplexOrder

/-- **Process matrix** (Shmueli, *What Can Be Computed with Indefinite Causal Structure?*,
arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definition 4.4, p.19 (PDF p.21)):
`W ∈ L(H_AI ⊗ H_P ⊗ H_AO ⊗ H_F)` is a process matrix if `W` is positive semidefinite and, for
every collection of auxiliary registers and every choice of local quantum channels `A`, the
induced map `PMO(W, H_AI, H_AO)[A]` is a quantum channel.

**Formalization Note** `n` separate single-qubit feedback pairs (the paper's default, stated
after Definition 4.4). The auxiliary registers are arbitrary qubit registers `Eᵢ = S(e i)`,
`E'ᵢ = S(e' i)`, with input and output sizes independent and zero allowed; the local operations
range over **all** quantum channels `Aᵢ : L(Sᵢ ⊗ Eᵢ) → L(Rᵢ ⊗ E'ᵢ)` (Definition 3.13). -/
def IsProcessMatrix {n : ℕ} {P F : Type*} [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]
    (W : Matrix ((Qubits n × P) × (Qubits n × F)) ((Qubits n × P) × (Qubits n × F)) ℂ) : Prop :=
  W.PosSemidef ∧
    ∀ (e e' : Fin n → ℕ) (A : (i : Fin n) → LocalMap e e' i),
      (∀ i, IsQuantumChannel (A i)) → IsQuantumChannel (pmo W A)

end ICSCompute


