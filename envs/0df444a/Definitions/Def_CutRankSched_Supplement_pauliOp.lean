-- Prove2me | Definitions.Def_CutRankSched_Supplement_pauliOp
-- name    : CutRankSched_Supplement_pauliOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:37:33.516574+00:00
-- url     : https://prove2.me/theorems/c5e90af1-f5bc-491e-a477-4a881dae51a2
-- title:
--   Hermitian Pauli operator $P(p)=i^{x\cdot z}X^xZ^z$
-- statement:
--   Operators on $m$ qubits are $2^m\times 2^m$ complex matrices indexed by computational basis strings $a\in\mathbb F_2^m$. For a binary Pauli vector $p=(x,z)\in\mathbb F_2^{2m}$, its **Hermitian Pauli operator** is
--   $$
--   P(p) = i^{\,x\cdot z}\, X^x Z^z,\qquad X^xZ^z\,|b\rangle = (-1)^{z\cdot b}\,|b+x\rangle ,
--   $$
--   where $X^x=\prod_q X_q^{x_q}$, $Z^z=\prod_q Z_q^{z_q}$ and $x\cdot z$ is the number of qubits with $x_q=z_q=1$ (the positions carrying $Y = iXZ$). Thus $P(p)$ is the tensor product of the single-qubit Paulis $I, X, Y, Z$ prescribed by $p$.
--
--   This is the fixed Hermitian representative $P(p)$ about which every event of the trace rotates.
--
--   **Formalization Note** The type of operators is `Op m`, matrices over `Fin m → ZMod 2`. The exponent of $i$ counts the $Y$ positions over $\mathbb N$, not modulo $2$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.1, p.4

import Mathlib
import Definitions.Def_CutRankSched_Pauli

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The `2^m × 2^m` complex matrices acting on `m` qubits, indexed by computational basis strings
`a : Fin m → ZMod 2` (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.1, p.4). -/
abbrev Op (m : ℕ) : Type := Matrix (Fin m → ZMod 2) (Fin m → ZMod 2) ℂ

/-- The fixed Hermitian representative `P(p)` of the Pauli operator of a binary Pauli vector
`p = (x, z)` (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.1, p.4): `P(p) = i^{x·z} X^x Z^z`, where `X^x = ∏_q X_q^{x_q}`,
`Z^z = ∏_q Z_q^{z_q}` and `x·z` is the number of qubits with `x_q = z_q = 1` (the `Y` positions,
`Y = iXZ`). As a matrix, `X^x Z^z |b⟩ = (−1)^{z·b} |b + x⟩`.

**Formalization Note** The paper fixes "a fixed Hermitian representative"; this is the standard
one, `P(p) = ⊗_q σ_q` with `σ ∈ {I, X, Y, Z}`. The exponent of `i` counts `Y` positions over `ℕ`,
not mod 2. -/
noncomputable def pauliOp {m : ℕ} (p : Pauli m) : Op m :=
  fun a b =>
    Complex.I ^ (Finset.univ.filter fun q => p.1 q = 1 ∧ p.2 q = 1).card *
      (if a = b + p.1 then (-1 : ℂ) ^ (dotProduct p.2 b).val else 0)

end Supplement

end CutRankSched


