-- Prove2me | Definitions.Def_QRetrieval_Adaptive_B
-- name    : QRetrieval_Adaptive_B
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:23.383286+00:00
-- url     : https://prove2.me/theorems/42aaf7ae-3d5b-4ab2-9650-3d80ad954081
-- title:
--   $B(m,n)$: the $m$-bit strings of Hamming weight at most $n$
-- statement:
--   For natural numbers $m$ and $n$, let $\mathrm{wt}_H(x)$ denote the **Hamming weight** of a string $x\in\{0,1\}^m$, the number of coordinates equal to $1$. The set of strings to be compressed is
--
--   $$
--   B(m,n)=\{x\in\{0,1\}^m:\ \mathrm{wt}_H(x)\le n\}.
--   $$
--
--   Every compression scheme of the mission stores exactly these strings, and validity is required for every element of $B(m,n)$.
--
--   **Formalization Note** A string is a function $x:\mathrm{Fin}\,m\to\mathrm{Bool}$ (the index $i\in[m]$ is $i-1\in\mathrm{Fin}\,m$, and the bit $1$ is `true`); the weight is the shared `QAlgorithms.hammingWeight`.
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, §2 (Preliminaries), p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QRetrieval.Adaptive

/-- **The strings to be compressed: `B(m, n)`, the `m`-bit strings of Hamming weight at most `n`.**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, §2 (Preliminaries), p. 4: "We write `B(m, n)` for the set of all strings in
`{0,1}^m` with weight at most `n`, that is, `B(m, n) = {x ∈ {0,1}^m : wt_H(x) ≤ n}`."

`B m n` is the subtype of `x : Fin m → Bool` with `QAlgorithms.hammingWeight x ≤ n`.

**Formalization Note.** The index set `[m] = {1, …, m}` is `Fin m` (0-based: the source's index
`i` is `i - 1 : Fin m`), and the bit `1` is `true`. The Hamming weight is the shared
`QAlgorithms.hammingWeight` (number of coordinates equal to `true`). -/
abbrev B (m n : ℕ) : Type := {x : Fin m → Bool // QAlgorithms.hammingWeight x ≤ n}

end QRetrieval.Adaptive


