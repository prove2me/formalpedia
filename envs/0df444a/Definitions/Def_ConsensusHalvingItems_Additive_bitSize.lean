-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_bitSize
-- name    : ConsensusHalvingItems_Additive_bitSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:21:47.935036+00:00
-- url     : https://prove2.me/theorems/7e4aae6c-b9eb-4a13-8c42-b09a276a1dfa
-- title:
--   Bit size of a rational number
-- statement:
--   For a rational number $q = p/r$ in lowest terms with $r > 0$, its **bit size** is
--
--   $$
--   \operatorname{bitSize}(q) = \operatorname{size}(|p|) + \operatorname{size}(r) + 1,
--   $$
--
--   where $\operatorname{size}(k)$ is the number of binary digits of the natural number $k$ (with $\operatorname{size}(0) = 0$). Up to an additive constant this is the length of the standard binary encoding of $q$. For example $\operatorname{bitSize}(0) = 2$ and $\operatorname{bitSize}(1/2) = 4$.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
--
--   **Formalization Note** Mathlib stores rationals in lowest terms, so `q.num` and `q.den` are coprime; `Nat.size` counts binary digits.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm")

import Mathlib

namespace ConsensusHalvingItems.Additive

/-- **Bit size of a rational number.**
Cost model of the mission for "polynomial-time" in Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1,
Theorem 2.2, p. 4.

For a rational `q = p / r` in lowest terms (`r > 0`), `bitSize q` is the number of binary
digits of `|p|` plus the number of binary digits of `r` plus one (for the sign). This is the
length of the standard binary encoding of `q` up to an additive constant.

**Formalization Note.** Mathlib's `ℚ` stores `q.num` and `q.den` coprime, so the encoding is the
reduced one. `Nat.size k` is the number of binary digits of `k` (`Nat.size 0 = 0`). Hence
`bitSize 0 = 2` and `bitSize (1/2) = 4`. -/
def bitSize (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den + 1

end ConsensusHalvingItems.Additive


