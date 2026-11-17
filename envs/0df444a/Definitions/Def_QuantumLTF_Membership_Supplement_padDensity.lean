-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_padDensity
-- name    : QuantumLTF_Membership_Supplement_padDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:41:04.063532+00:00
-- url     : https://prove2.me/theorems/e2b0ff36-bc5d-47aa-875d-15287a8053b8
-- title:
--   Mixed input followed by clean ancillas, $\rho\otimes|0^e\rangle\langle0^e|$
-- statement:
--   The density matrix $\rho\otimes|0^e\rangle\langle 0^e|$: a mixed state of the first $N$ qubits followed by $e$ ancilla qubits in $|0\rangle$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §C.5, p. 95 (PDF p. 96); Theorem 5.6, p. 70 (PDF p. 71)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership.Supplement

open QAlgorithms

/-- **`ρ ⊗ |0^e⟩⟨0^e|`: a mixed input on the first `N` wires, `e` clean ancillas after it.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331,
§C.5, p. 95 (PDF p. 96), clean ancillas; Theorem 5.6, p. 70 (PDF p. 71), input `ρ_K`. Entry `(z, z')`
is `ρ(z_{<N}, z'_{<N})` if the last `e` bits of `z` and of `z'` are `0`, and `0` otherwise. -/
noncomputable def padDensity {N : ℕ} (e : ℕ) (ρ : Matrix (Qubits N) (Qubits N) ℂ) :
    Matrix (Qubits (N + e)) (Qubits (N + e)) ℂ :=
  Matrix.of fun z z' =>
    if (∀ j : Fin e, z (Fin.natAdd N j) = false) ∧ (∀ j : Fin e, z' (Fin.natAdd N j) = false) then
      ρ (fun i => z (Fin.castAdd e i)) (fun i => z' (Fin.castAdd e i))
    else 0

end QuantumLTF.Membership.Supplement


