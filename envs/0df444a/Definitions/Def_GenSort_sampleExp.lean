-- Prove2me | Definitions.Def_GenSort_sampleExp
-- name    : GenSort_sampleExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:19.224408+00:00
-- url     : https://prove2.me/theorems/64c5e9e7-ec4b-45dd-b1d3-deb87788e8f2
-- title:
--   Expectation over $k$ independent uniform samples
-- statement:
--   For a finite set $B$ and a function $g$ of $k$ samples,
--   $$
--   \mathbb E_{x}[g(x)] = \frac{1}{|B|^k} \sum_{x \in B^k} g(x),
--   $$
--   the expectation when $x_1, \dots, x_k$ are drawn independently and uniformly from $B$. In Lemma 3.5, $B$ is the set of bad edges and $S$ is the multiset of right endpoints of $s$ such samples.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 3.5, p.8 (PDF p.10)

import Mathlib

namespace GenSort

/-- **Expectation over `k` i.i.d. uniform samples from a finite set `B`**:
`E_x[g(x)] = |B|^{-k} Σ_{x ∈ B^k} g(x)`. Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 3.5, p.8 (PDF p.10): `E_S` over the multiset
`S` of right endpoints of `s` uniformly random bad edges, sampled with replacement. -/
noncomputable def sampleExp {α : Type*} (B : Finset α) (k : ℕ) (g : (Fin k → α) → ℝ) : ℝ :=
  (∑ y : Fin k → B, g fun i => (y i : α)) / (B.card : ℝ) ^ k

end GenSort


