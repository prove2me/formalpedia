-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_cnotFromSelect
-- name    : ShendeQSD_Synthesis_cnotFromSelect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:32.100562+00:00
-- url     : https://prove2.me/theorems/ef3a3f55-bd25-4f60-8843-33eba7e8731c
-- title:
--   CNOT from the extra select qubit to the target (Theorem 8)
-- statement:
--   On a register made of a target qubit $t$, an extra select qubit $s_0$ and further select qubits $r$, this is the CNOT with control $s_0$ and target $t$:
--
--   $$
--   |t\rangle|s_0\rangle|r\rangle\longmapsto|t\oplus s_0\rangle|s_0\rangle|r\rangle .
--   $$
--
--   It is the two-qubit gate appearing twice in the right-hand circuit of Theorem 8.
--
--   **Formalization Note** The index is `Bool × (Bool × σ)` = (target, (extra select, other selects)), matching the orientation of `muxRot`.
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Theorem 8, p. 11

import Mathlib

namespace ShendeQSD.Synthesis

/-- **The CNOT of Theorem 8, from the extra select qubit to the target.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Theorem 8, p. 11: in the right-hand circuit, a CNOT whose control is the most significant select
qubit and whose target is the data qubit of the multiplexed rotation.

On the index `Bool × (Bool × σ)` = (target `t`, (select `s₀`, other selects `r`)), it maps
`|t, s₀, r⟩ ↦ |t XOR s₀, s₀, r⟩`.

**Formalization Note.** The order of the tensor factors (target first) is the one of `muxRot`. -/
def cnotFromSelect {σ : Type*} [DecidableEq σ] :
    Matrix (Bool × (Bool × σ)) (Bool × (Bool × σ)) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 ∧ p.1 = xor q.1 q.2.1 then 1 else 0

end ShendeQSD.Synthesis


