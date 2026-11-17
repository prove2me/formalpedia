-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_blockOracle
-- name    : TwoFoldOPI_Supplement_blockOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:59:43.704647+00:00
-- url     : https://prove2.me/theorems/006b5d86-3d9e-4a5d-9e2d-1b8a9011f78e
-- title:
--   Quantum oracle access to block functions $H_i:\mathbb F_q^s\to[n]$
-- statement:
--   Oracle $i$ of a program is the reversible evaluation $|x,z\rangle\mapsto|x,z\oplus H_i(x)\rangle$ of $H_i$, where $x\in\mathbb F_q^s$ is written in $s\cdot b$ qubits (the field layout) and $H_i(x)\in[n]$ in $\lceil\log_2 n\rceil$ bits.
--
--   **Formalization Note** An oracle whose declared arity is not $s\,b+\lceil\log_2n\rceil$, or whose index is at least $m$, is the identity; statements fix the number of oracles and their arities.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26; §11, Definition 11.2, p. 57

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits
import Definitions.Def_TwoFoldOPI_Supplement_fnOracle

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **Quantum oracle access to block functions `H_1, …, H_m : F_q^s → [n]`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26: "Classical function oracles use reversible
evaluation, |x, z⟩ ↦ |x, z ⊕ H(x)⟩, with a fixed binary encoding of the output"; Definition 11.2,
p.57 ("together with quantum oracle access to the H_i's").

Oracle `k` of a program (`k < m`) is `fnOracle` of `H_k`: its first `s · b` wires hold a block
`x ∈ F^s` (each symbol in `b = bitsPerSymbol F` bits, `elemBits` layout, read back by
`decodeElem`), and its last `⌈log₂ n⌉` wires receive `H_k(x)` XOR-ed in (`natToBits`, most
significant bit first). Oracles `k ≥ m` are the identity.

**Formalization Note.** The arities `a k` are those declared by the program; an oracle whose
declared arity is not `s · b + ⌈log₂ n⌉` is the identity (`fnOracle`'s guard). Statements fix the
number of oracles to `m` and every arity to `s · b + ⌈log₂ n⌉`. -/
noncomputable def blockOracle (F : AvgCaseTI.FieldPres) {r : ℕ} (a : Fin r → ℕ) {s m n : ℕ}
    (H : Fin m → (Fin s → F.F) → Fin n) (k : Fin r) : Matrix (Qubits (a k)) (Qubits (a k)) ℂ :=
  if hk : k.val < m then
    fnOracle (a k) (s * bitsPerSymbol F) (Nat.clog 2 n) fun bits =>
      natToBits (Nat.clog 2 n)
        (H ⟨k.val, hk⟩ fun j => decodeElem F fun t => bits (finProdFinEquiv (j, t))).val
  else 1

end Supplement

end TwoFoldOPI


