-- Prove2me | Definitions.Def_RainsSep_Distill_depolarizing
-- name    : RainsSep_Distill_depolarizing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:14.046537+00:00
-- url     : https://prove2.me/theorems/cf429d24-b342-4b02-aa51-23ec5d781e0c
-- title:
--   The depolarizing two-qubit state $\Delta(\epsilon)$
-- statement:
--   For a real parameter $\epsilon$, the **depolarizing state** $\Delta(\epsilon)$ is the two-qubit operator
--
--   $$
--   \Delta(\epsilon)=\frac{\epsilon}{4}\,\mathrm{Id}+\frac{1-\epsilon}{2}\,\big(|00\rangle+|11\rangle\big)\big(\langle 00|+\langle 11|\big).
--   $$
--
--   It is the maximally entangled pair $\Phi^+$ mixed with white noise. Its entanglement fidelity is $f=1-\tfrac34\epsilon$, and it is a density matrix exactly when $0\le\epsilon\le 4/3$, i.e. when $f\in[0,1]$.
--
--   **Formalization Note** The first qubit is Alice's; $|0\rangle$ is the basis vector labelled `false`. The definition accepts every real $\epsilon$.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (19), p. 2

import Mathlib

namespace RainsSep.Distill

/-- **The depolarizing two-qubit state `Δ(ε)`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (19), p. 2: "the state ∆(ǫ) with density matrix (ǫ/4) Id + ((1 − ǫ)/2)(|00⟩ +
|11⟩)(⟨00| + ⟨11|), (19) on a two-state Hilbert space."

The operator `(ε/4)·Id + ((1−ε)/2)·|φ⟩⟨φ|` on `ℂ² ⊗ ℂ²` with `φ = |00⟩ + |11⟩` (unnormalized).
Its entanglement fidelity is `f = 1 − 3ε/4` (Eq. (20)).

**Formalization Note.** `false` is `|0⟩`; the first factor is Alice's qubit. The definition is
stated for every real `ε`; it is a density matrix exactly when `0 ≤ ε ≤ 4/3`, i.e. when its
fidelity lies in `[0, 1]`. -/
noncomputable def depolarizing (ε : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ((ε / 4 : ℝ) : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) +
    (((1 - ε) / 2 : ℝ) : ℂ) • Matrix.of fun p q : Bool × Bool =>
      (if p.1 = p.2 then (1 : ℂ) else 0) * (if q.1 = q.2 then (1 : ℂ) else 0)

end RainsSep.Distill


