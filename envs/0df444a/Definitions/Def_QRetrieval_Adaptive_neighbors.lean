-- Prove2me | Definitions.Def_QRetrieval_Adaptive_neighbors
-- name    : QRetrieval_Adaptive_neighbors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:16.194043+00:00
-- url     : https://prove2.me/theorems/66c0154e-6069-47f0-9e33-404c947f0223
-- title:
--   Neighbourhood $\Gamma_G(A)$ in a bipartite graph $G:[k]\times[d]\to R$
-- statement:
--   A bipartite graph is represented as a function $G:[k]\times[d]\to R$: the left vertex $v\in[k]$ has $d$ edges, labelled by $[d]$, and the edge with label $j$ goes to the right vertex $G(v,j)\in R$. The neighbourhood of a left vertex is $\Gamma_G(v)=\{w\in R:\exists j\in[d],\ G(v,j)=w\}$, and of a set $A\subseteq[k]$ of left vertices
--
--   $$
--   \Gamma_G(A)=\bigcup_{a\in A}\Gamma_G(a)=\{G(a,j): a\in A,\ j\in[d]\}.
--   $$
--
--   Lemma 3 and the remark after it are stated with this neighbourhood.
--
--   **Formalization Note** $[k]$ and $[d]$ are $\mathrm{Fin}\,k$ and $\mathrm{Fin}\,d$ (0-based) and $G$ is curried, $G:\mathrm{Fin}\,k\to\mathrm{Fin}\,d\to R$, for any right vertex type $R$ with decidable equality; the paper's $R$ is $[2n]$.
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, §2.1 (Expander graphs), p. 5

import Mathlib

namespace QRetrieval.Adaptive

/-- **Neighbourhood `Γ_G(A)` of a set of left vertices in a bipartite graph `G : [k] × [d] → R`.**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, §2.1 (Expander graphs), p. 5: bipartite graphs are represented "as functions of
the form `G : L × D → R`", where the left vertex `v` has its `|D|` edges labelled by `D`, and
"`Γ_G(v) = {w ∈ R : ∃ j ∈ D, G(v, j) = w}`". For a set `A ⊆ L` (as used in Lemma 3),
`Γ_G(A) = ⋃_{a ∈ A} Γ_G(a)`.

`neighbors G A` is the finite set `⋃_{a ∈ A} {G a j : j ∈ Fin d}`.

**Formalization Note.** The left vertex set `[k]` and the label set `[d]` are `Fin k` and
`Fin d` (0-based), and `G : [k] × [d] → R` is curried, `G : Fin k → Fin d → R`. The right vertex
set `R` is any type with decidable equality (in the paper it is `[2n]`). -/
def neighbors {k d : ℕ} {R : Type*} [DecidableEq R] (G : Fin k → Fin d → R)
    (A : Finset (Fin k)) : Finset R :=
  A.biUnion fun a => Finset.univ.image (G a)

end QRetrieval.Adaptive


