-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_padKet
-- name    : QuantumLTF_Membership_Supplement_padKet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:40:42.375319+00:00
-- url     : https://prove2.me/theorems/551b9781-ecab-4f49-9a29-9238b34a9599
-- title:
--   Input state followed by clean ancillas, $|\psi\rangle|0^e\rangle$
-- statement:
--   The vector $|\psi\rangle\otimes|0^e\rangle$: a state of the first $N$ qubits followed by $e$ ancilla qubits in $|0\rangle$. Section C.5 assumes clean ancillas.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §C.5, p. 95 (PDF p. 96)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership.Supplement

open QAlgorithms

/-- **`|ψ⟩ ⊗ |0^e⟩`: an input state on the first `N` wires, `e` clean ancillas after it.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331,
§C.5, p. 95 (PDF p. 96): "we also assume that we have access to clean ancillas". The amplitude of the
string `z` is `ψ(z_0 … z_{N−1})` if the last `e` bits of `z` are `0`, and `0` otherwise. -/
noncomputable def padKet {N : ℕ} (e : ℕ) (ψ : EuclideanSpace ℂ (Qubits N)) :
    EuclideanSpace ℂ (Qubits (N + e)) :=
  WithLp.toLp 2 fun z =>
    if ∀ j : Fin e, z (Fin.natAdd N j) = false then ψ (fun i => z (Fin.castAdd e i)) else 0

end QuantumLTF.Membership.Supplement


