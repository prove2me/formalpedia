-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_loadState
-- name    : TwoFoldOPI_Supplement_loadState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:58:22.986241+00:00
-- url     : https://prove2.me/theorems/cf587b9a-3ab4-43a8-9396-6d685dd666c4
-- title:
--   The load state $|\mathcal T\rangle$ on qubits
-- statement:
--   For a nonempty load set $\mathcal T\subseteq[n]^m$,
--   $$|\mathcal T\rangle=\frac{1}{\sqrt{|\mathcal T|}}\sum_{x\in\mathcal T}|x\rangle,$$
--   where a word $x$ is written on $m\lceil\log_2 n\rceil$ qubits, each symbol in $\lceil\log_2n\rceil$ bits, most significant bit first.
--
--   **Formalization Note** Used only for $\mathcal T\ne\emptyset$, where it is a unit vector.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.1, Definition 10.2, eq. (23), p. 53

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **The load state `|T⟩ = |T|^{−1/2} Σ_{x ∈ T} |x⟩` on qubits.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.1, Definition 10.2, eq. (23), p.53: "If T ≠ ∅, we may also define the quantum state:
|T⟩ := (1/√|T|) Σ_{x∈T} |x⟩."

A word `x ∈ [n]^m` is written on `m · ⌈log₂ n⌉` qubits: symbol `x_j` (`0 ≤ x_j < n`) in
`⌈log₂ n⌉` bits, most significant bit first (`natToBits`), symbol `0` first. `loadState m n T` is
the uniform superposition of these basis states over `x ∈ T`.

**Formalization Note.** Used only for `T ≠ ∅`, where it is a unit vector (distinct words give
distinct basis states). -/
noncomputable def loadState (m n : ℕ) (T : Finset (Fin m → Fin n)) :
    EuclideanSpace ℂ (Qubits (m * Nat.clog 2 n)) :=
  ∑ x ∈ T, ((Real.sqrt (T.card : ℝ))⁻¹ : ℂ) •
    ket (fun i : Fin (m * Nat.clog 2 n) =>
      natToBits (Nat.clog 2 n) (x (finProdFinEquiv.symm i).1).val (finProdFinEquiv.symm i).2)

end Supplement

end TwoFoldOPI


