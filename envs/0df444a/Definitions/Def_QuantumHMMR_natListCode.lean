-- Prove2me | Definitions.Def_QuantumHMMR_natListCode
-- name    : QuantumHMMR_natListCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:26.790192+00:00
-- url     : https://prove2.me/theorems/81ce7f4e-8708-48f6-b4ff-8135d0ae4a71
-- title:
--   Self-delimiting binary code of a list of natural numbers
-- statement:
--   Classical descriptions of circuits are written over the alphabet $\{0, 1\}$. A natural number $k$ is encoded by the self-delimiting binary code
--   $$
--   \mathrm{code}(0) = 0, \qquad \mathrm{code}(k) = 1\,b_0\,\mathrm{code}(\lfloor k/2 \rfloor) \quad (k > 0),
--   $$
--   where $b_0 = k \bmod 2$; a list of numbers is encoded by concatenating the codes of its entries. The code of $k > 0$ has length $2\lfloor \log_2 k \rfloor + 3$, linear in the binary length of $k$.
--
--   **Formalization Note** The code is injective (the verification file proves it), so a machine's output determines the list. It is the description format used by the uniformity notion of this mission.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 3, p.11 (classical descriptions of a uniform family)

import Mathlib

namespace QuantumHMMR

/-- The self-delimiting binary code of a natural number used to write classical descriptions
(Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §3, p.11: a uniform family is output as a "classical description"): `0 ↦ [false]`, and
`k > 0 ↦ true :: (k mod 2 = 1) :: code ⌊k/2⌋`. Its length is `2⌊log₂ k⌋ + 3` for `k > 0`, linear in
the binary length of `k`. -/
def natCode : ℕ → List Bool
  | 0 => [false]
  | k + 1 => true :: ((k + 1) % 2 == 1) :: natCode ((k + 1) / 2)
decreasing_by omega

/-- The binary code of a list of natural numbers: the concatenation of the self-delimiting codes
`natCode` of its entries (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §3, p.11). Numbers are written in binary, so the code of a
description has length linear in its bit size.

**Formalization Note** The code is injective (each `natCode` is self-delimiting); the verification
file proves it. -/
def natListCode (l : List ℕ) : List Bool :=
  l.flatMap natCode

end QuantumHMMR


