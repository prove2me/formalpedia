-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_prefixState
-- name    : TwoFoldOPI_Supplement_prefixState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:53:05.263209+00:00
-- url     : https://prove2.me/theorems/5c6d5738-4ed9-4218-8184-70525a123636
-- title:
--   The reduced state of the first $k$ qubits of a pure state
-- statement:
--   For a state $\psi$ on $N$ qubits and $k\le N$, the reduced density matrix of the first $k$ qubits is
--   $$\rho(y,y')=\sum_{e\in\{0,1\}^{N-k}}\psi(y,e)\,\overline{\psi(y',e)} .$$
--
--   It measures the quality of a prepared register when work qubits remain entangled (Theorem 10.5).
--
--   **Formalization Note** Statements use $k\le N$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26; §10.2, Theorem 10.5, p. 54

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **The state of the first `k` qubits of an `N`-qubit pure state (the others traced out).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26: "Preparation error means trace distance";
§10.2, Theorem 10.5, p.54 ("the state |T⟩ can be prepared to trace-distance error ϵ").

For `ψ` on `N` qubits and `k ≤ N`, `prefixState k N ψ` is the reduced density matrix of wires
`0, …, k−1`: `ρ(y, y′) = Σ_e ψ(y, e) · conj ψ(y′, e)`, the sum over the values `e` of wires
`k, …, N−1`.

**Formalization Note.** The sum runs over all `z ∈ {0,1}^N` whose first `k` bits are `y`, pairing
`z` with the string whose first `k` bits are replaced by `y′`. Statements require `k ≤ N`. -/
noncomputable def prefixState (k N : ℕ) (ψ : EuclideanSpace ℂ (Qubits N)) :
    Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun y y' => ∑ z : Qubits N,
    if (∀ i : Fin N, ∀ h : i.val < k, z i = y ⟨i.val, h⟩) then
      ψ z * star (ψ (fun i => if h : i.val < k then y' ⟨i.val, h⟩ else z i))
    else 0

end Supplement

end TwoFoldOPI


