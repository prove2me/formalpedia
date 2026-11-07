-- Prove2me | Definitions.Def_ICSCompute_ancChannel
-- name    : ICSCompute_ancChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:47:37.934043+00:00
-- url     : https://prove2.me/theorems/21cbf17a-99a3-45db-871d-edc25a8a33fe
-- title:
--   The channel $C_{(U,k)}(\rho) = U(\rho\otimes|0^k\rangle\langle0^k|)U^\dagger$
-- statement:
--   For a matrix $U$ on $m+k$ qubits, the linear map
--   $$C_{(U,k)}(\rho) := U\big(\rho\otimes|0^k\rangle\langle 0^k|\big)U^\dagger$$
--   sends an $m$-qubit operator to an $(m+k)$-qubit operator: $k$ ancillas in $|0\rangle$ are appended after the input and $U$ is applied. When $U$ is unitary it is the channel of an isometry.
--
--   Lemma 4.1 compares the identity connection of $\mathrm{CJ}(C_{(U,k)})$ with $C_{(U_G,k)}$ for $U_G = \operatorname{Tr}_{H_{AI}}(U)$, which need not be unitary.
--
--   **Formalization Note** `splitQ3` splits $\mathcal S(n+r+k)$ as $\mathcal S(n)\otimes\mathcal S(r+k)$ and `castQ` re-brackets $n+r+k = n+(r+k)$; both are the identity on qubit order.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Lemma 4.1, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ICSCompute_splitQ
import Definitions.Def_ICSCompute_QCirc

namespace ICSCompute

open QAlgorithms

/-- Re-bracketing `S(n + r + k) = S(n + (r + k))` (the identity on bit strings). -/
def castQ (n r k : ℕ) : Qubits (n + r + k) ≃ Qubits (n + (r + k)) :=
  Equiv.arrowCongr (finCongr (Nat.add_assoc n r k)) (Equiv.refl Bool)

/-- The split of `S(n + r + k)` into its first `n` qubits and its last `r + k` qubits. -/
def splitQ3 (n r k : ℕ) : Qubits (n + r + k) ≃ Qubits n × Qubits (r + k) :=
  (castQ n r k).trans (splitQ n (r + k))

/-- **The channel `C_(U,k)`** (Shmueli, *What Can Be Computed with Indefinite Causal
Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Lemma 4.1, p.20
(PDF p.22)): `C_(U,k)(ρ) := U (ρ ⊗ |0ᵏ⟩⟨0ᵏ|) U†` for a matrix `U` on `m + k` qubits, a linear map
from `L(S(m))` to `L(S(m + k))`. The `k` ancilla qubits in `|0⟩` are the last `k` qubits.

**Formalization Note** `U` is not required to be unitary in the definition (Lemma 4.1 applies it
to `U_G`, which "does not need to be unitary"). -/
def ancChannel {m : ℕ} (k : ℕ) (U : Matrix (Qubits (m + k)) (Qubits (m + k)) ℂ) :
    Matrix (Qubits m) (Qubits m) ℂ →ₗ[ℂ] Matrix (Qubits (m + k)) (Qubits (m + k)) ℂ where
  toFun ρ := U * padZero k ρ * U.conjTranspose
  map_add' ρ σ := by rw [padZero_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c ρ := by simp [padZero_smul]

end ICSCompute


