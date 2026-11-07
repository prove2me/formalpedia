-- Prove2me | Definitions.Def_CompNonlocal_ICirc_branchWires
-- name    : CompNonlocal_ICirc_branchWires
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:41.192447+00:00
-- url     : https://prove2.me/theorems/6f97e600-48b3-47e7-bc50-eba1522ce4ff
-- title:
--   The instrument branch of a classical-output event
-- statement:
--   For a circuit $C$ with classical input $x$, input state $\rho$ on $m$ qubits and a set $P$ of output strings, this is the unnormalized state of a chosen list of wires after the event "the classical output lies in $P$":
--   $$\operatorname{Tr}_{\text{other wires}}\big[(\Pi_P\otimes I)\,U(|x\rangle\langle x|\otimes\rho\otimes|0\rangle\langle0|)U^\dagger(\Pi_P\otimes I)\big],$$
--   with $\Pi_P$ the projector of the measured wires onto outcomes in $P$ (the input qubits the circuit does not read are traced out). Its trace is the probability of the event. It is linear in $\rho$, so it acts on halves of entangled states.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.4, p.20

import Mathlib
import Definitions.Def_CompNonlocal_ICirc

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The branch (instrument element) of a circuit for a classical-output event, keeping the wires
`ws`. For a circuit `C` with classical input `x` run on the `m`-qubit input state `ρ`, this is the
unnormalized state of the wires `ws` after the event "the classical output satisfies `P`": with
`σ = U (|x⟩⟨x| ⊗ ρ ⊗ |0⟩⟨0|) U†` (the qubits of `ρ` beyond the `nq` read ones traced out), it is
`Tr_{other wires}[(Π_P ⊗ I) σ (Π_P ⊗ I)]`, where `Π_P` projects the measured wires onto the outcomes
satisfying `P`. Its trace is the probability of the event. This is the QCCC execution model of
Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*,
manuscript (STOC 2027 submission, sha256 e245edd7…), §4.4, p.20 ("Honest algorithms … may retain
quantum states locally, and exchange only classical messages").

**Formalization Note** Entry `(s, s')` sums `σ_{z z'}` over pairs of full outcomes `z, z'` that agree
on every wire outside `ws`, have `z|_ws = s`, `z'|_ws = s'`, and whose classical output satisfies `P`.
The map is linear in `ρ`. -/
noncomputable def ICirc.branchWires (C : ICirc) {k : ℕ} (ws : Fin k → Fin C.width) (m : ℕ)
    (x : Str) (ρ : Matrix (Bits m) (Bits m) ℂ) (P : Str → Bool) : Matrix (Bits k) (Bits k) ℂ :=
  Matrix.of fun s s' =>
    ∑ z : Bits C.width, ∑ z' : Bits C.width,
      if P (C.clOut z) ∧ (∀ i, z (ws i) = s i) ∧ (∀ i, z' (ws i) = s' i) ∧
          (∀ w : Fin C.width, (∀ i, ws i ≠ w) → z w = z' w) then
        ∑ q : Bits m, ∑ q' : Bits m,
          if (∀ j : Fin m, C.nq ≤ (j : ℕ) → q j = q' j) then
            ρ q q' * C.unitary z (C.feed x q) * star (C.unitary z' (C.feed x q'))
          else 0
      else 0

end CompNonlocal


