-- Prove2me | Definitions.Def_OnlineSetCover_LowerBound_BitFamily
-- name    : OnlineSetCover_LowerBound_BitFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:46:52.883266+00:00
-- url     : https://prove2.me/theorems/be5e8273-ecf6-424c-9d9b-e5dc71b80396
-- title:
--   The bit family $F_1,\dots,F_k$ on $\{0,\dots,2^k-1\}$ (Proposition 4.1)
-- statement:
--   Let $k \ge 1$ and $X = \{0, 1, \dots, 2^k - 1\}$. For $1 \le i \le k$, let
--
--   $$F_i = \{\, j \in X : \text{the } i\text{th bit of the binary representation of } j \text{ is } 1 \,\},$$
--
--   and let $\mathcal F = \{F_1, \dots, F_k\}$. This is the instance of Proposition 4.1, on which every deterministic online algorithm can be forced to take all $k$ sets although a single set covers the elements presented. The same construction, applied inside each block, is the building block of the family of Proposition 4.2.
--
--   **Formalization Note** $X$ is `Fin (2^k)`. Bits are counted from the least significant one, which is bit $1$; bit $i$ of $j$ is `Nat.testBit j (i - 1)`, so the set $F_{t+1}$ is `bitSet k t` for `t : Fin k`. Which end the bits are counted from does not change the family. The family is the image of `bitSet k` over `Fin k`.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 368, Proposition 4.1

import Mathlib

namespace OnlineSetCover.LowerBound

/-- The set `F_{t+1}` of Proposition 4.1 (Alon et al. 2009, p. 368): the elements `j` of
`X = {0, 1, …, 2^k − 1}` whose bit number `t + 1` (counting from the least significant bit,
which is bit `1`) is on, i.e. `Nat.testBit j t`. -/
def bitSet (k : ℕ) (t : Fin k) : Finset (Fin (2 ^ k)) :=
  Finset.univ.filter (fun j => j.val.testBit t.val)

/-- The family `F = {F_1, …, F_k}` of Proposition 4.1 on `X = {0, …, 2^k − 1}`. -/
def bitFamily (k : ℕ) : Finset (Finset (Fin (2 ^ k))) :=
  Finset.univ.image (bitSet k)

end OnlineSetCover.LowerBound


