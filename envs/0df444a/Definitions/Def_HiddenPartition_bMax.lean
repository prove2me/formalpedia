-- Prove2me | Definitions.Def_HiddenPartition_bMax
-- name    : HiddenPartition_bMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:14.684859+00:00
-- url     : https://prove2.me/theorems/d975ddfd-e35f-4ea4-ac73-b915fd26a47f
-- title:
--   Maximum number of edges on at most $s$ vertices, $B_G(s)$
-- statement:
--   For a finite simple graph $G$ and $s\ge0$,
--
--   $$B_G(s)=\max_{S\subseteq V(G),\ |S|\le s}|E(G[S])|,$$
--
--   the largest number of edges spanned by at most $s$ vertices of $G$. The empty set is admissible, and for $s\ge|V(G)|$ the maximum is $|E(G)|$.
--
--   It is the source-side quantity that controls the density of small vertex sets of the target graph in Theorem 1.1(3) and Lemma 4.1.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), Theorem 1.1, p.2 (pdf p.4); Lemma 4.1, p.17 (pdf p.19)

import Mathlib
import Definitions.Def_HiddenPartition_edgeCount

set_option autoImplicit false

namespace HiddenPartition

/-- **The quantity `B_G(s)`** (Agrawal et al., STOC 2027 submission, manuscript sha256
17239d0b…, Theorem 1.1, p.2 (pdf p.4), and Lemma 4.1, p.17 (pdf p.19)).

`B_G(s) = max_{S ⊆ V(G), |S| ≤ s} |E(G[S])|`, the largest number of edges spanned by at most
`s` vertices of `G`.

**Formalization Note.** The maximum is a `Finset.sup` over all subsets of the finite vertex set
of size at most `s`; the empty set is among them, so the maximum is taken over a non-empty
family, and for `s ≥ |V(G)|` it equals `|E(G)|`. -/
noncomputable def bMax {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter (fun S => S.card ≤ s)).sup (edgeCount G)

end HiddenPartition


