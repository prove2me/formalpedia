-- Prove2me | Definitions.Def_GenSort_distOrd
-- name    : GenSort_distOrd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:28.084107+00:00
-- url     : https://prove2.me/theorems/5e568777-d0b1-47a7-b906-24088c23662d
-- title:
--   $\mathrm{dist}_F(\pi, \sigma)$: disagreements of two orders on an edge set
-- statement:
--   For two total orderings $\pi, \sigma$ of $[n]$ and a set $F$ of edges,
--   $$
--   \mathrm{dist}_F(\pi, \sigma) = \sum_{(u,v) \in F} \mathbf 1\big[\mathbf 1[u \prec_\pi v] \ne \mathbf 1[u \prec_\sigma v]\big],
--   $$
--   the number of edges of $F$ that $\pi$ and $\sigma$ orient differently.
--
--   **Formalization Note** $F$ is a finite set of unordered pairs and each edge is counted once: $\{u, v\}$ counts iff $u \prec_\pi v$ and $v \prec_\sigma u$ for one of its two labellings, which for $u \ne v$ is exactly the disagreement above.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Definition 2.1, p.4 (PDF p.6)

import Mathlib

namespace GenSort

/-- **`dist_F(π, σ)`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Definition 2.1, p.4 (PDF p.6):
`dist_F(π, σ) = Σ_{(u,v)∈F} 1[1[u ≺_π v] ≠ 1[u ≺_σ v]]`, the number of edges of `F` on which the
total orderings `π` and `σ` disagree.

**Formalization Note.** `F` is a finset of unordered pairs and each edge is counted once: an
edge `{u, v}` counts iff `u ≺_π v` and `v ≺_σ u` for one of its two labellings. For `u ≠ v` this
is exactly `1[u ≺_π v] ≠ 1[u ≺_σ v]`; a diagonal pair never counts. -/
noncomputable def distOrd {n : ℕ} (F : Finset (Sym2 (Fin n))) (π σ : Equiv.Perm (Fin n)) : ℕ :=
  open Classical in
  (F.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ π.symm u < π.symm v ∧ σ.symm v < σ.symm u).card

end GenSort


