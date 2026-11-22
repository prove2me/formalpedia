-- Prove2me | Definitions.Def_QMAPlusGap_prodWitness
-- name    : QMAPlusGap_prodWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:36.598602+00:00
-- url     : https://prove2.me/theorems/470dff8d-44ce-4e9d-8a94-a8960a6dfead
-- title:
--   Tensor product of $k$ proofs on a witness block
-- statement:
--   Let a witness block of $W$ qubits be split into $k$ proofs of $w$ qubits each by a bijection $e:\{0,\dots,W-1\}\to\{0,\dots,k-1\}\times\{0,\dots,w-1\}$. For proof states $|\psi_1\rangle,\dots,|\psi_k\rangle$ on $w$ qubits, the product state $|\psi_1\rangle\otimes\cdots\otimes|\psi_k\rangle$ on the block has amplitude
--   $$
--   \prod_{i=1}^{k}\psi_i\big(y|_{\text{wires of proof }i}\big)
--   $$
--   at the basis string $y$.
--
--   In $\mathsf{QMA}^+(k,c,s)$ the verifier's witness block carries exactly such a product of $k$ unentangled proofs.
--
--   **Formalization Note** In `QMAplus` the split is the standard one $\{0,\dots,kw-1\}\cong\{0,\dots,k-1\}\times\{0,\dots,w-1\}$, so proof $i$ occupies the contiguous wires $iw,\dots,iw+w-1$.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Definition 4, p.11

import Mathlib
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace QMAPlusGap

/-- The **tensor product of `k` proof states** `|ψ₁⟩ ⊗ ⋯ ⊗ |ψ_k⟩` on a witness block of `W` qubits, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…),
Definition 4, p.11 ("k(n) mutually unentangled proof states … whose tensor product is accepted").

The bijection `e : Fin W ≃ Fin k × Fin w` assigns to each witness wire the proof `i` and the qubit `j` of that
proof it carries. The amplitude of the product state at the basis string `y` of the block is
`∏_i ψ_i(y restricted to the wires of proof i)`.

**Formalization Note** Proof states are `ShiShallow.QState w` (amplitude vectors on `w` qubits). In
`QMAplus` the bijection is `Fin (k·w) ≃ Fin k × Fin w` from `finProdFinEquiv`, so proof `i` occupies the
contiguous wires `i·w, …, i·w + w − 1` of the witness block. -/
def prodWitness {W k w : ℕ} (e : Fin W ≃ Fin k × Fin w) (ψs : Fin k → ShiShallow.QState w) :
    ShiShallow.QState W :=
  fun y => ∏ i : Fin k, ψs i (fun j : Fin w => y (e.symm (i, j)))

end QMAPlusGap


