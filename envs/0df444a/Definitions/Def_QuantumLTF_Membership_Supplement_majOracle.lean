-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_majOracle
-- name    : QuantumLTF_Membership_Supplement_majOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:32:25.722192+00:00
-- url     : https://prove2.me/theorems/15fb5ef1-b86e-43ce-8ddf-27b3ecaeeb61
-- title:
--   Boolean membership oracle $O_{f_A}$ of the Majority junta
-- statement:
--   The bit oracle of $f_A$ on $n+1$ qubits:
--   $$O_{f_A}|S\rangle|b\rangle=|S\rangle|b\oplus \bar f_A(S)\rangle,\qquad \bar f=(1-f)/2.$$
--   Qubit $i<n$ of the query register is $1$ iff $i\in S$ (that is, $x_i=+1$); the last qubit is the target.
--
--   The paper's §4 uses the phase oracle $O^\pm_A|S\rangle=f_A(S)|S\rangle$ (Eq. (129)). The two are equivalent when they can be applied in a controlled manner (p. 4), and the oracle circuits of the theorems allow controlled calls.
--
--   **Formalization Note** A permutation matrix on $\{0,1\}^{n+1}$; column $z$ is the image of $|z\rangle$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Eq. (1), p. 4 (PDF p. 5); Eq. (129), p. 50 (PDF p. 51)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_Supplement_majJunta

namespace QuantumLTF.Membership.Supplement

open QAlgorithms

/-- **The Boolean membership oracle of the Majority junta.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Eq. (1), p. 4 (PDF p. 5), and
Eq. (129), p. 50 (PDF p. 51): the bit oracle `O_f : |S⟩|b⟩ ↦ |S⟩|b ⊕ f̄_A(S)⟩` with
`f̄ := (1 − f)/2`, on `n + 1` wires.

**Formalization Note.** Wire `i < n` of the query register is `true` iff `i ∈ S`, i.e. `x_i = +1`;
the last wire is the target. A permutation matrix; column `z` is the image of `|z⟩`. The paper's §4
uses the phase oracle `O^±_A|S⟩ = f_A(S)|S⟩`; p. 4 notes that the two are equivalent when they can be
applied in a controlled manner, and `OracleCircuit` allows controlled calls (one query each). -/
noncomputable def majOracle {n : ℕ} (A : Finset (Fin n)) :
    Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  Matrix.of fun y z =>
    if y = Fin.snoc (α := fun _ => Bool) (Fin.init z)
        (xor (z (Fin.last n))
          (decide (majJunta A (Finset.univ.filter fun i => Fin.init z i = true) = -1)))
    then 1 else 0

end QuantumLTF.Membership.Supplement


