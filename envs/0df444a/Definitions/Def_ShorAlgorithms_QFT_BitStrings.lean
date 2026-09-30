-- Prove2me | Definitions.Def_ShorAlgorithms_QFT_BitStrings
-- name    : ShorAlgorithms_QFT_BitStrings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:56:03.591358+00:00
-- url     : https://prove2.me/theorems/331875fe-7505-41ae-b784-a11848afdd46
-- title:
--   Bit strings: value ∑ 2^j a_j, bit reversal, basis states |a⟩
-- statement:
--   Fix a number of bits $l \ge 0$. A basis state of an $l$-bit register is a bit string $a = (a_{l-1}, \dots, a_0)$ with each $a_j \in \{0, 1\}$, written $|a_{l-1} a_{l-2} \dots a_0\rangle$. This file defines three objects on such strings.
--
--   1. **Value.** The integer encoded by $a$, with $a_0$ the least significant bit:
--   $$a = \sum_{j=0}^{l-1} 2^j a_j \in \{0, 1, \dots, 2^l - 1\}.$$
--   2. **Bit reversal.** The string $c$ obtained by reading the bits of $b$ from right to left:
--   $$c_j = b_{l-1-j} \qquad (0 \le j < l).$$
--   3. **Basis state.** The state $|a\rangle$, i.e. the amplitude vector over bit strings that is $1$ at $a$ and $0$ at every other string.
--
--   These are the bookkeeping objects in which the quantum Fourier transform circuit of Shor's §4 is stated: the circuit acts on basis states $|a\rangle$, the phase it produces is expressed through the values $a$ and $c$, and its output register is read in bit-reversed order.
--
--   **Formalization Note** A bit string is a function `Fin l → Fin 2`, and a state on $l$ bits is a function from bit strings to $\mathbb C$ (the amplitudes). The value is a natural number. The case $l = 0$ is allowed: there is one (empty) bit string, of value $0$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1495, §4 ("let us represent an integer a in binary as |a_{l-1}a_{l-2}…a_0⟩"); p. 1496 (bit reversal: "the binary number obtained by reading the bits of c from right to left"); p. 1497, eq. (4.10)

import Mathlib

namespace ShorAlgorithms.QFT

/-- The integer encoded by an `l`-bit string `a = |a_{l-1} … a_0⟩`, least significant bit first:
`bitsVal a = ∑_j 2^j a_j` (Shor 1997, eq. (4.10)). -/
def bitsVal {l : ℕ} (a : Fin l → Fin 2) : ℕ :=
  ∑ j : Fin l, 2 ^ (j : ℕ) * (a j : ℕ)

/-- Bit reversal: `(bitRev b)_j = b_{l-1-j}`, the string obtained by reading the bits of `b`
from right to left (Shor 1997, p. 1496). -/
def bitRev {l : ℕ} (b : Fin l → Fin 2) : Fin l → Fin 2 :=
  fun j => b (Fin.rev j)

/-- The computational basis state `|a⟩` on `l` bits: amplitude `1` at `a`, `0` elsewhere. -/
noncomputable def basisState {l : ℕ} (a : Fin l → Fin 2) : (Fin l → Fin 2) → ℂ :=
  fun b => if b = a then 1 else 0

end ShorAlgorithms.QFT


