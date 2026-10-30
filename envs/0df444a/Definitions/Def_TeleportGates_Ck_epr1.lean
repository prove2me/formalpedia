-- Prove2me | Definitions.Def_TeleportGates_Ck_epr1
-- name    : TeleportGates_Ck_epr1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:13.500671+00:00
-- url     : https://prove2.me/theorems/3346bfc2-d383-4d09-beca-b334e079cc12
-- title:
--   EPR pair $|\Psi\rangle=(|00\rangle+|11\rangle)/\sqrt2$
-- statement:
--   The EPR pair is the two-qubit state
--
--   $$|\Psi\rangle=\frac{1}{\sqrt2}\bigl(|00\rangle+|11\rangle\bigr).$$
--
--   Its first qubit is the *upper* half, which is measured together with the input; its second qubit is the *lower* half, which carries the output.
--
--   **Formalization Note** Amplitudes $\Psi(b,c)=1/\sqrt2$ if $b=c$ and $0$ otherwise.
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §I, unnumbered, p. 1

import Mathlib

namespace TeleportGates.Ck

/-- **The EPR pair `|Ψ⟩ = (|00⟩ + |11⟩)/√2`.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §I, unnumbered, p. 1: "an EPR state
|Ψ⟩ = (|00⟩ + |11⟩)/√2".

`epr1 (b, c) = 1/√2` if `b = c` and `0` otherwise.

**Formalization Note.** Basis index `Bool`, `false` = `|0⟩`. The first factor `b` is the
upper half of the pair (the one measured), the second factor `c` the lower half (the output). -/
noncomputable def epr1 : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

end TeleportGates.Ck


