-- Prove2me | Definitions.Def_AKNMixed_FQP_detPerm
-- name    : AKNMixed_FQP_detPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:36.929791+00:00
-- url     : https://prove2.me/theorems/1ccb98e0-d0a1-4f61-9eaf-234d52a22192
-- title:
--   Permutation $U_d:|i,x\rangle\mapsto|i,x\oplus d(i)\rangle$ of a deterministic function
-- statement:
--   Let $d:\{0,1\}^m\to\{0,1\}^p$ be a deterministic function. $U_d$ is the permutation matrix on $m+p$ qubits (input register first) given on basis vectors by
--
--   $$U_d\,|i,x\rangle=|i,\;x\oplus d(i)\rangle ,$$
--
--   with $\oplus$ the bitwise exclusive or. In particular $U_d|i,0\rangle=|i,d(i)\rangle$, which is how Definition 5 specifies $U_d$.
--
--   **Formalization Note** The paper fixes $U_d$ only on the vectors $|i,0\rangle$. The exclusive-or completion makes $U_d$ a permutation (hence unitary) on the whole space and agrees with the paper on $|i,0\rangle$.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 5, p. 10 ("U_d is defined by U_d|i, 0⟩ = |i, d(i)⟩")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace AKNMixed.FQP

open QAlgorithms

/-- **The permutation `U_d : |i, x⟩ ↦ |i, x ⊕ d(i)⟩` of a deterministic function `d`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 5, p. 10: "U_d is defined by U_d|i, 0⟩ = |i, d(i)⟩".

For `d : {0,1}^m → {0,1}^p`, `detPerm d` is the `(m + p)`-qubit permutation matrix with entry
`1` at `((i, x ⊕ d i), (i, x))` and `0` elsewhere: it sends the basis vector `|i, x⟩` to
`|i, x ⊕ d(i)⟩`, bitwise exclusive or.

**Formalization Note.** The paper fixes `U_d` only on the vectors `|i, 0⟩`; this definition
completes it to a unitary by the exclusive or (the standard reversible evaluation of `d`), which
agrees with the paper on `|i, 0⟩`. The input register is the first factor of the index
`Qubits m × Qubits p`. -/
def detPerm {m p : ℕ} (d : Qubits m → Qubits p) :
    Matrix (Qubits m × Qubits p) (Qubits m × Qubits p) ℂ :=
  Matrix.of fun y z => if y.1 = z.1 ∧ y.2 = (fun t => xor (z.2 t) (d z.1 t)) then 1 else 0

end AKNMixed.FQP


