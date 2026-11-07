-- Prove2me | Definitions.Def_GenSort_score
-- name    : GenSort_score
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:03.163249+00:00
-- url     : https://prove2.me/theorems/7693a457-b5c4-46be-b07a-e71c76245ab0
-- title:
--   $\mathrm{Score}_\tau(u)$: minimum rank of a sampled neighbour
-- statement:
--   Let $S = (S_1, \dots, S_s)$ be the sampled right vertices (a multiset) and $\tau$ an ordering of $S$. The **score** of a left vertex $u$ is the minimum rank in $\tau$ of its neighbours in $S$,
--   $$
--   \mathrm{Score}_\tau(u) = \min_{v \in \Gamma(u) \cap S} \tau(v),
--   $$
--   and $s + 1$ if $u$ has no neighbour in $S$. Neighbours are taken in the current graph.
--
--   **Formalization Note** $S$ is indexed by $\{1, \dots, s\}$ so that repeated samples are separate entries, $\tau$ is a permutation of the indices, and ranks are $1, \dots, s$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 step 3, p.7 (PDF p.9)

import Mathlib

namespace GenSort

/-- **`Score_τ(u)`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 step 3, p.7 (PDF p.9): for the sampled multiset `S = (S_1, …, S_s)`
of right vertices and an ordering `τ` of it, the score of a left vertex `u` is the minimum rank in
`τ` over its neighbours in `S`, `min_{v ∈ Γ(u) ∩ S} τ(v)`, and `s + 1` if `u` has no neighbour in
`S`. Neighbours are taken in the current edge set `E`.

**Formalization Note.** `S` is indexed by `Fin s`, so repeated samples are distinct entries; `τ`
is a permutation of the indices and the (1-based) rank of entry `i` is `τ i + 1`. -/
noncomputable def score {L R : Type*} {s : ℕ} (E : Finset (L × R)) (S : Fin s → R)
    (τ : Equiv.Perm (Fin s)) (u : L) : ℕ :=
  open Classical in
  if h : (Finset.univ.filter fun i => (u, S i) ∈ E).Nonempty then
    (Finset.univ.filter fun i => (u, S i) ∈ E).inf' h fun i => (τ i : ℕ) + 1
  else s + 1

end GenSort


