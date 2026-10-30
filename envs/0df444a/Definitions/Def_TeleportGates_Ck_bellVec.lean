-- Prove2me | Definitions.Def_TeleportGates_Ck_bellVec
-- name    : TeleportGates_Ck_bellVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:54.868487+00:00
-- url     : https://prove2.me/theorems/9dea7164-e999-4dce-b49f-e0b05e51c428
-- title:
--   $n$-pair Bell basis vector $\beta_{xz}=\bigotimes_i \beta_{x_iz_i}$ on input and upper registers
-- statement:
--   Let $x,z\in\{0,1\}^n$. The Bell basis vector with outcome strings $(x,z)$ on the $2n$ qubits made of an $n$-qubit input register and an $n$-qubit upper register is
--
--   $$\beta_{xz}(a,b)=\prod_{i=1}^n \beta_{x_iz_i}(a_i,b_i),\qquad a,b\in\{0,1\}^n,$$
--
--   where $\beta_{x_iz_i}$ is the single-qubit Bell vector. Input qubit $i$ is paired with upper qubit $i$, and the pair's outcome is $(x_i,z_i)$. This is the outcome vector of the $n$ Bell measurements "on [the input] and the $n$ upper qubits".
--
--   **Formalization Note** Registers are indexed by bit strings $\{0,1\}^n$ (`QAlgorithms.Qubits n`). The vector is normalized.
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §II, unnumbered, p. 3 (Bell basis measurements on the input and the n upper qubits); one-pair Bell basis §I, p. 1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_TeleportGates_Ck_bell1

namespace TeleportGates.Ck

open QAlgorithms

/-- **The n-pair Bell basis vector `β_{xz}` (Bell measurement of n input qubits against n upper
qubits).**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §II, unnumbered, p. 3: "take the input state |ψ⟩
and do Bell basis measurements on this and the n upper qubits of |Ψn_U⟩"; the one-pair Bell basis
is that of §I, p. 1.

For outcome strings `x z : Qubits n`, `bellVec n x z` is the vector of
`(ℂ²)^{⊗n} ⊗ (ℂ²)^{⊗n}` (input register, upper register) given by
`bellVec n x z (a, b) = ∏ᵢ bell1 (x i) (z i) (a i, b i)`: input qubit `i` and upper qubit `i` are
projected onto the one-pair Bell vector `(|0xᵢ⟩ + (−1)^{zᵢ}|1x̄ᵢ⟩)/√2`.

**Formalization Note.** The pairing is wire by wire: input qubit `i` is measured with upper
qubit `i`, giving outcome bits `(xᵢ, zᵢ)`. The register order of the index `(a, b)` is (input,
upper), as in `bell1` (teleported qubit first). Normalized. -/
noncomputable def bellVec (n : ℕ) (x z : Qubits n) : EuclideanSpace ℂ (Qubits n × Qubits n) :=
  WithLp.toLp 2 fun p => ∏ i : Fin n, bell1 (x i) (z i) (p.1 i, p.2 i)

end TeleportGates.Ck


