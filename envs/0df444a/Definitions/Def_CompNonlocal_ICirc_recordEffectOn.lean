-- Prove2me | Definitions.Def_CompNonlocal_ICirc_recordEffectOn
-- name    : CompNonlocal_ICirc_recordEffectOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:11.237544+00:00
-- url     : https://prove2.me/theorems/27088f0d-c01b-4975-87d1-7e4c90564ac4
-- title:
--   The effect of a complete measurement record
-- statement:
--   For a circuit $C$ with classical input $x$, run on an $m$-qubit input register, and a computational-basis outcome $z$ of **all** its wires, the effect of the event "the complete record is $z$" on the input register is
--   $$E_z=(I\otimes\langle x,0|)\,U^\dagger|z\rangle\langle z|U\,(I\otimes|x,0\rangle)$$
--   on the qubits the circuit reads, tensored with the identity on the qubits it does not read. The probability of the record on the input state $\rho$ is $\operatorname{Tr}(E_z\rho)$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 1, p.26 and Lemma 11, p.36

import Mathlib
import Definitions.Def_CompNonlocal_ICirc

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The effect of a complete measurement record. For a circuit `C` with classical input `x`, run on
an `m`-qubit input register, this is the effect on the register of the event "measuring every wire
of `C` in the computational basis at the end gives the outcome `z`":
`E_z = (I ⊗ ⟨x, 0|) U† |z⟩⟨z| U (I ⊗ |x, 0⟩)` on the qubits the circuit reads, tensored with the
identity on the qubits it does not read. This is the effect of Lemma 1, p.26 of Głuch, Morimae,
*From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), and the "effect … corresponding to the complete outcome" of
Lemma 11, p.36.

**Formalization Note** Entry `(q', q)` is `conj(U_{z, in(q')}) · U_{z, in(q)}` when `q, q'` agree on the
qubits `j ≥ nq` (which the circuit does not read), else `0`; so `Pr[z] = Tr(E_z ρ)` with
`Tr(E ρ) = Σ_{q', q} E q' q · ρ q q'`. -/
noncomputable def ICirc.recordEffectOn (C : ICirc) (m : ℕ) (x : Str) (z : Bits C.width) :
    Matrix (Bits m) (Bits m) ℂ :=
  Matrix.of fun q' q =>
    if (∀ j : Fin m, C.nq ≤ (j : ℕ) → q' j = q j) then
      star (C.unitary z (C.feed x q')) * C.unitary z (C.feed x q)
    else 0

end CompNonlocal


