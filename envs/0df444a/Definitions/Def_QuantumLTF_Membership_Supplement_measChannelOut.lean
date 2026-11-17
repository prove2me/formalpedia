-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_measChannelOut
-- name    : QuantumLTF_Membership_Supplement_measChannelOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:41:57.578874+00:00
-- url     : https://prove2.me/theorems/9ab50504-8c38-433f-a4ab-12f21e9f288a
-- title:
--   Channel with one round of single-qubit measurements and classical control
-- statement:
--   The output of the channel that does the following on a pure input $\psi$ of $m$ qubits:
--
--   1. applies a unitary $V$;
--   2. measures $r$ designated qubits in the computational basis, with outcome $t$;
--   3. applies a unitary $W_t$ chosen by $t$;
--   4. traces out every qubit except $o$ designated output qubits;
--   5. averages over the outcomes.
--
--   In formulas,
--   $$\mathcal C(|\psi\rangle\langle\psi|)=\sum_t \mathrm{Tr}_{\mathrm{rest}}\big(W_t\Pi_tV|\psi\rangle\langle\psi|V^\dagger\Pi_tW_t^\dagger\big),$$
--   with $\Pi_t$ the projector on outcome $t$. This is the form of the band-conversion channel of Theorem 5.4, which measures blank markers and moves the nonblank registers by a classically controlled permutation (p. 69).
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.4, pp. 67–69 (PDF pp. 68–70)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership.Supplement

open QAlgorithms
open scoped ComplexConjugate

/-- **Output of a channel with mid-circuit measurements and classical control.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.4,
pp. 67–69 (PDF pp. 68–70): the band-conversion channel applies a circuit, measures single qubits,
"use[s] a classically controlled permutation to move any K nonblank registers to the first K output
positions and discard[s] all remaining registers" (p. 69). Here: the unitary `V` on `m` wires is
applied to the pure input `ψ`; the `r` wires `meas` are measured in the computational basis, with
outcome `t`; the unitary `W t` (chosen by `t`) is applied; all wires except the `o` output wires
`out` are traced out, and the outcomes are averaged:

`C(|ψ⟩⟨ψ|) = Σ_t Tr_{rest}(W_t Π_t V |ψ⟩⟨ψ| V† Π_t W_t†)`, `Π_t` the projector on outcome `t`.

**Formalization Note.** Entry `(y, y')` sums `φ_t(z) conj(φ_t(z'))` over `t` and over strings `z, z'`
reading `y, y'` on the output wires and agreeing elsewhere (the partial trace), with
`φ_t = W_t Π_t V ψ`. The map is a quantum channel by construction (trace preserving on unit `ψ`). -/
noncomputable def measChannelOut {m r o : ℕ} (V : Matrix (Qubits m) (Qubits m) ℂ)
    (W : Qubits r → Matrix (Qubits m) (Qubits m) ℂ) (meas : Fin r ↪ Fin m) (out : Fin o ↪ Fin m)
    (ψ : EuclideanSpace ℂ (Qubits m)) : Matrix (Qubits o) (Qubits o) ℂ :=
  let φ : Qubits r → Qubits m → ℂ := fun t =>
    Matrix.mulVec (W t) (fun z => if z ∘ meas = t then (act V ψ) z else 0)
  Matrix.of fun y y' => ∑ t : Qubits r, ∑ z : Qubits m, ∑ z' : Qubits m,
    if z ∘ out = y ∧ z' ∘ out = y' ∧ ∀ j : Fin m, (∀ i : Fin o, out i ≠ j) → z j = z' j then
      φ t z * conj (φ t z')
    else 0

end QuantumLTF.Membership.Supplement


