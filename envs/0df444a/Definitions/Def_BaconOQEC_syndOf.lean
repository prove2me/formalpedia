-- Prove2me | Definitions.Def_BaconOQEC_syndOf
-- name    : BaconOQEC_syndOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:52.676636+00:00
-- url     : https://prove2.me/theorems/e27719f2-1828-4090-9cc4-70628b8adeca
-- title:
--   Syndrome of a Pauli error
-- statement:
--   Measuring the $2(n-1)$ commuting generators $S^X_i$, $S^Z_j$ after a Pauli error $P(a,b)$ has acted on the code sector produces the **syndrome** $s = (s^X, s^Z)$. Its bit $s^X_i$ records whether $P(a,b)$ anticommutes with $S^X_i$, and its bit $s^Z_j$ whether it anticommutes with $S^Z_j$:
--
--   $$
--   s^X_i = \langle (a,b), S^X_i\rangle,\qquad s^Z_j = \langle (a,b), S^Z_j\rangle .
--   $$
--
--   **Formalization Note** A syndrome is a pair of strings of $n-1$ bits in `ZMod 2`. Bit $0$ stands for eigenvalue $+1$ and bit $1$ for $-1$, so the code sector "$s^X_i = s^Z_i = +1$" is $s = 0$.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.B, eq. (14), p.6; §IV.C, eqs. (22)–(23), p.7

import Mathlib
import Definitions.Def_BaconOQEC_symp
import Definitions.Def_BaconOQEC_SX
import Definitions.Def_BaconOQEC_SZ

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.B, eq. (14), p.6 and §IV.C, eqs. (22)–(23), p.7: the syndrome of the
Pauli error `P(a, b)`, the outcomes of measuring the `2(n − 1)` generators `S^X_i`, `S^Z_j` after
`P(a, b)` acts on the code sector: bit `i` of the first string is `1` exactly when `P(a, b)`
anticommutes with `S^X_i`, bit `j` of the second exactly when it anticommutes with `S^Z_j`.

**Formalization Note.** A syndrome is a pair `s = (s^X, s^Z)` of strings `Fin m → ZMod 2`
(`n − 1 = m` bits each). Bit `0` stands for the eigenvalue `+1` and bit `1` for `−1` (the paper's
`±1`-valued `s^X_i`, `s^Z_i`); the code sector "s^X_i = s^Z_i = +1" is `s = 0`. -/
def syndOf {m : ℕ} (a b : Bits m) : (Fin m → ZMod 2) × (Fin m → ZMod 2) :=
  (fun i => symp (a, b) (SX i), fun j => symp (a, b) (SZ j))

end BaconOQEC


