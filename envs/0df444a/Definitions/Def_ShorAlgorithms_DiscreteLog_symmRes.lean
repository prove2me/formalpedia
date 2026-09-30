-- Prove2me | Definitions.Def_ShorAlgorithms_DiscreteLog_symmRes
-- name    : ShorAlgorithms_DiscreteLog_symmRes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T00:29:36.390878+00:00
-- url     : https://prove2.me/theorems/6734f0a5-621e-4176-8dbb-a47857a24353
-- title:
--   The symmetric residue $\{z\}_q$
-- statement:
--   For integers $q>0$ and $z$, the **symmetric residue** $\{z\}_q$ is the unique integer with
--
--   $$
--   \{z\}_q\equiv z\pmod q,\qquad -\frac q2<\{z\}_q\le\frac q2 .
--   $$
--
--   It is obtained from the least nonnegative residue $m=z\bmod q\in[0,q)$ by keeping $m$ when $2m\le q$ and replacing it by $m-q$ otherwise. It measures how far $z$ is from the nearest multiple of $q$, and appears in the definition of the good outputs of the discrete-logarithm algorithm through $\{c(p-1)\}_q$.
--
--   **Formalization Note** Defined on `ℤ` via `Int.emod`. For $q=0$ the value is a meaningless default; every use in this mission has $q>0$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1499, §5 (definition after eq. (5.6)), and p. 1503, §6 (after eq. (6.9))

import Mathlib

namespace ShorAlgorithms.DiscreteLog

/-- Shor (1997), p. 1499 (after (5.6)) and p. 1503 (after (6.9)): the symmetric residue
`{z}_q`, the residue of `z (mod q)` with `-q/2 < {z}_q ≤ q/2`. For `q > 0`, `z % q` is the
least nonnegative residue in `[0, q)`; it is kept when `2 (z % q) ≤ q` and shifted down by `q`
otherwise. (For `q = 0` the value is junk; every use has `q > 0`.) -/
def symmRes (q z : ℤ) : ℤ :=
  if 2 * (z % q) ≤ q then z % q else z % q - q

end ShorAlgorithms.DiscreteLog


