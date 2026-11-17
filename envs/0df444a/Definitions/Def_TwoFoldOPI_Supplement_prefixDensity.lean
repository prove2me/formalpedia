-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_prefixDensity
-- name    : TwoFoldOPI_Supplement_prefixDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:03:29.639097+00:00
-- url     : https://prove2.me/theorems/ae258c5e-15cd-4c10-9e33-0c8d093ce044
-- title:
--   The reduced state of the first $k$ qubits of a density matrix
-- statement:
--   For a density matrix $\rho$ on $N$ qubits and $k\le N$, the partial trace over the last $N-k$ qubits is
--   $$\sigma(y,y')=\sum_{e}\rho\big((y,e),(y',e)\big).$$
--
--   It measures the register prepared by a preparation program (Theorem 5.28).
--
--   **Formalization Note** Statements use $k\le N$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26; Theorem 5.28, p. 27

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **The reduced state of the first `k` qubits of an `N`-qubit density matrix.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26: "Preparation error means trace distance, with the
convention D(σ, τ) = ½‖σ − τ‖_1"; Theorem 5.28, p.27 ("a state δ-close to |A⟩ can be prepared").

For `ρ` on `N` qubits and `k ≤ N`, `prefixDensity k N ρ` is the partial trace over wires
`k, …, N−1`: `σ(y, y′) = Σ_e ρ((y, e), (y′, e))`.

**Formalization Note.** The sum runs over all `z ∈ {0,1}^N` whose first `k` bits are `y`, pairing
`z` with the string whose first `k` bits are replaced by `y′` (the density version of
`prefixState`). Statements use `k ≤ N`. -/
noncomputable def prefixDensity (k N : ℕ) (ρ : Matrix (Qubits N) (Qubits N) ℂ) :
    Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun y y' => ∑ z : Qubits N,
    if (∀ i : Fin N, ∀ h : i.val < k, z i = y ⟨i.val, h⟩) then
      ρ z (fun i => if h : i.val < k then y' ⟨i.val, h⟩ else z i)
    else 0

end Supplement

end TwoFoldOPI


