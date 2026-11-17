-- Prove2me | Definitions.Def_NearOptOWF_Supplement_blocks
-- name    : NearOptOWF_Supplement_blocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:10:39.19741+00:00
-- url     : https://prove2.me/theorems/8b31400f-fa3a-4c3e-b482-54b2a7fde114
-- title:
--   Splitting a string into $t$ blocks of $n$ bits
-- statement:
--   A string $s$ is read as the $t$-tuple $(x_1,\dots,x_t)$ whose $i$-th component consists of bits $(i-1)n+1,\dots,in$ of $s$. On strings of length exactly $tn$ this is the fixed injective split used to read an adversary's output $(x_1,\dots,x_t)$ in Definition 5.1.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 5.1, p.23 (PDF p.25)

import Mathlib

namespace NearOptOWF.Supplement

/-- Reading a string as a `t`-tuple of `n`-bit blocks (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 5.1, p.23 (PDF p.25):
"`A(1^λ, H_k) → (x₁, x₂, …, x_t)`"): the `i`-th component is the block of bits `i·n, …, i·n + n − 1`.

**Formalization Note** On a string of length exactly `t·n` this is the fixed injective split into `t`
blocks of length `n`; the output-intractability event requires that length. -/
def blocks (n t : ℕ) (s : List Bool) : Fin t → List Bool :=
  fun i => (s.drop (i.1 * n)).take n

end NearOptOWF.Supplement


