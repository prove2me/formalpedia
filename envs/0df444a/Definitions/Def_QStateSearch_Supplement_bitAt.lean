-- Prove2me | Definitions.Def_QStateSearch_Supplement_bitAt
-- name    : QStateSearch_Supplement_bitAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:06:04.547301+00:00
-- url     : https://prove2.me/theorems/f0060e4c-a320-4ac9-922b-c0c241ae5c2a
-- title:
--   Bit of a basis state on a wire
-- statement:
--   For a computational-basis state $z\in\{0,1\}^w$ of a $w$-qubit register and a wire index $i\in\mathbb N$, $\mathrm{bit}_z(i)$ is the value $z_i$ of wire $i$ if $i<w$, and $0$ otherwise.
--
--   A pure state of $w$ qubits is a function $\{0,1\}^w\to\mathbb C$; this helper reads the classical value of one wire in a basis state and is used to state every gate action.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Sections 2.2–2.3 and 6.1, pp.8–10, 16

import Mathlib

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- The value of wire `i` in the computational-basis state `z` of a `w`-qubit register
(`false` = `|0⟩`, `true` = `|1⟩`); wires outside the register read as `false`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Sections 2.2–2.3 and 6.1, pp.8–9, 16 (explicit circuits on qubit registers).

**Formalization Note.** A basis state of `w` qubits is a function `Fin w → Bool`; a pure state
is a function `(Fin w → Bool) → ℂ`. -/
def bitAt {w : ℕ} (z : Fin w → Bool) (i : ℕ) : Bool :=
  if h : i < w then z ⟨i, h⟩ else false

end QStateSearch.Supplement


