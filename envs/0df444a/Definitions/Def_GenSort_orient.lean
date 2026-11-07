-- Prove2me | Definitions.Def_GenSort_orient
-- name    : GenSort_orient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:40.821437+00:00
-- url     : https://prove2.me/theorems/889807dc-5141-46ea-8e47-5735f64f6aeb
-- title:
--   Edges of $F$ oriented by $\sigma$
-- statement:
--   For an edge set $F$ and a permutation $\sigma$, every edge $\{u, v\} \in F$ is oriented from its $\sigma$-earlier endpoint to its $\sigma$-later one: the set of ordered pairs $(u, v)$ with $\{u, v\} \in F$ and $u \prec_\sigma v$. In the bipartite graph of §3.2, the pair $(u, v)$ joins a left copy of $u$ to a right copy of $v$, so $\sigma$ predicts every edge to go from left to right.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8)

import Mathlib

namespace GenSort

/-- **The edges of `F` oriented by `σ`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8): "For every edge `(u, v) ∈ F`
with `u ≺_σ v`, we add an edge between the copy of `u` in `L` and the copy of `v` in `R`." The
oriented pair `(u, v)` has `{u, v} ∈ F` and `u ≺_σ v`; each edge of `F` gives exactly one pair. -/
noncomputable def orient {n : ℕ} (F : Finset (Sym2 (Fin n))) (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n × Fin n) :=
  open Classical in Finset.univ.filter fun p => s(p.1, p.2) ∈ F ∧ σ.symm p.1 < σ.symm p.2

end GenSort


