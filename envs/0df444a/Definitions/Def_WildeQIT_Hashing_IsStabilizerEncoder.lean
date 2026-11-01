-- Prove2me | Definitions.Def_WildeQIT_Hashing_IsStabilizerEncoder
-- name    : WildeQIT_Hashing_IsStabilizerEncoder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:20:54.227366+00:00
-- url     : https://prove2.me/theorems/ae0d1977-05a4-42d7-985c-fa7d8cca4d5d
-- title:
--   Encoding isometry $V$ of $k$ qubits into the codespace of $\mathcal S$
-- statement:
--   Let $\mathcal S$ be a subgroup of the $n$-qubit Pauli group. A $2^n\times2^k$ matrix $V$ is an **encoder** for the stabilizer code of $\mathcal S$ when
--
--   1. $V$ is an isometry, $V^\dagger V=I_{2^k}$;
--   2. every encoded state lies in the codespace: $S\,V|x\rangle=V|x\rangle$ for every $S\in\mathcal S$ and every computational basis state $|x\rangle$ of the $k$ logical qubits.
--
--   The encoding channel is $\rho\mapsto V\rho V^\dagger$. For an $[n,k]$ code the codespace has dimension $2^k$, so the image of $V$ is the whole codespace, as for the repetition-code encoding $\alpha|0\rangle+\beta|1\rangle\mapsto\alpha|000\rangle+\beta|111\rangle$ of (24.85).
--
--   **Formalization Note** The codespace is the published `QAlgorithms.stabilizedSpace S`; condition 2 is stated column by column.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.6.1–24.6.2, pp. 671–673, (24.85), (24.96)

import Definitions.Def_QAlgorithms_Defs_QECC

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.6.1–24.6.2,
pp. 671–673 (encoding `k` logical qubits into the codespace of a stabilizer code).
-/

namespace WildeQIT.Hashing

open QAlgorithms
open scoped Matrix

/-- **Encoding isometry of a stabilizer code** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, (24.85), p. 671, and (24.96), p. 673): `V : ℋ_{A₁} → (ℂ²)^{⊗n}`
with `A₁` the `k` logical qubits is an isometry, `V†V = I`, whose image lies in the codespace
`{|ψ⟩ : S|ψ⟩ = |ψ⟩ ∀ S ∈ S}` of `S`. The encoding channel is `ρ ↦ VρV†`.

**Formalization Note.** `V` is a `2ⁿ × 2^k` matrix indexed by `Qubits n × Qubits k`; the
codespace is the published `stabilizedSpace S`; "the image lies in the codespace" is stated
column by column (column `x` is `V|x⟩`). For an `[n, k]` stabilizer code the codespace has
dimension `2^k`, so the image of such a `V` is the whole codespace. -/
def IsStabilizerEncoder {n k : ℕ} (S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (V : Matrix (Qubits n) (Qubits k) ℂ) : Prop :=
  Vᴴ * V = 1 ∧ ∀ x : Qubits k, (WithLp.toLp 2 fun y => V y x) ∈ stabilizedSpace S

end WildeQIT.Hashing


