-- Prove2me | Definitions.Def_FowlerLSQC_Steane_bitString
-- name    : FowlerLSQC_Steane_bitString
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:09.664119+00:00
-- url     : https://prove2.me/theorems/87835490-753c-4007-944e-f5da67001bd6
-- title:
--   Basis label of a printed seven-character bit string
-- statement:
--   A seven-qubit computational basis state is labelled by a string $b_0b_1\dots b_6$ of binary digits. This definition turns such a string into the label used by the register type, so that the book's ket $|b_0b_1\dots b_6\rangle$ can be written with its digits in the printed order.
--
--   The digit $1$ becomes the value `true`, the digit $0$ becomes `false`, and the character at position $q$ from the left becomes wire $q$.
--
--   The order of the wires matters: it is the order in which the codewords (10.5)–(10.6) and the Pauli strings (10.7)–(10.12) line up.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.2, (10.5)–(10.6), p.112 (PDF p.130)

import Definitions.Def_QAlgorithms_Defs_Basic

namespace FowlerLSQC.Steane

open QAlgorithms

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.2, (10.5)–(10.6),
p.112 (PDF p.130): the computational-basis label of a seven-character bit string as printed in the
kets `|b₀b₁b₂b₃b₄b₅b₆⟩` of the book, written `bitString ![b₀, b₁, b₂, b₃, b₄, b₅, b₆]`.

**Formalization Note.** The published register type is `Qubits 7 = Fin 7 → Bool`; the digit `1`
becomes `true`, the digit `0` becomes `false`, and wire `q` is the character at position `q` from
the left, so wire `0` is the leftmost character of the book's strings. -/
def bitString (s : Fin 7 → Fin 2) : Qubits 7 :=
  fun q => decide (s q = 1)

end FowlerLSQC.Steane


