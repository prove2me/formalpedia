-- Prove2me | Definitions.Def_SingleInteraction_twoQubit
-- name    : SingleInteraction_twoQubit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:31.506619+00:00
-- url     : https://prove2.me/theorems/f4b48081-84aa-44f5-bf1e-cc22f3763b15
-- title:
--   Two-qubit tensor product $A\otimes B$
-- statement:
--   For one-qubit operators $A$ and $B$, $A\otimes B$ is the two-qubit operator whose first tensor factor $A$ acts on the first qubit and whose second factor $B$ acts on the second:
--
--   $$\langle s_0s_1|\,A\otimes B\,|t_0t_1\rangle=A_{s_0t_0}\,B_{s_1t_1}.$$
--
--   It is the building block of the interactions $Z\otimes Z+X\otimes Y-Y\otimes X$ of eq. (30) and $X\otimes X+Y\otimes Y$.
--
--   **Formalization Note** Two-qubit basis states are maps $\{0,1\}\to\{0,1\}$; bit $0$ is $|0\rangle$ and bit $1$ is $|1\rangle$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.1, p.15 (operator support and ordering)

import Mathlib

namespace SingleInteraction

/-- The two-qubit operator `A ⊗ B` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.1, p.15): the first tensor factor `A` acts on
qubit `0` and the second factor `B` on qubit `1`.

**Formalization Note** Two-qubit basis states are `Fin 2 → Fin 2`; the bit `0` is `|0⟩` and the bit
`1` is `|1⟩`. The entry at `(s, t)` is `A (s 0) (t 0) * B (s 1) (t 1)`. -/
def twoQubit (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  fun s t => A (s 0) (t 0) * B (s 1) (t 1)

end SingleInteraction


