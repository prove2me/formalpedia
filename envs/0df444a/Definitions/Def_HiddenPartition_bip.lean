-- Prove2me | Definitions.Def_HiddenPartition_bip
-- name    : HiddenPartition_bip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:30.718297+00:00
-- url     : https://prove2.me/theorems/c1bceddc-7fc6-4b5c-8424-417dd1271320
-- title:
--   Bipartite graph $J=(A,B,E)$ of a biadjacency matrix
-- statement:
--   For $M\ge0$ and a $0/1$ matrix $R\in\{0,1\}^{M\times M}$, $J=\mathrm{bip}(R)$ is the simple bipartite graph with sides $A=\{a_0,\dots,a_{M-1}\}$ and $B=\{b_0,\dots,b_{M-1}\}$ in which $a_i$ and $b_j$ are adjacent exactly when $R_{ij}=1$; no two vertices of the same side are adjacent.
--
--   Every simple bipartite graph with a fixed bipartition $(A,B)$, $|A|=|B|=M$, is of this form. It is the object constructed in Lemma 3.2 and [LUW95, Theorem 3.2].
--
--   **Formalization Note** The sides are the two summands of `Fin M ⊕ Fin M`.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), Lemma 3.2, p.14 (pdf p.16)

import Mathlib

set_option autoImplicit false

namespace HiddenPartition

/-- **Bipartite graph of a biadjacency matrix** (Agrawal et al., STOC 2027 submission,
manuscript sha256 17239d0b…, Lemma 3.2, p.14 (pdf p.16), where `J = (A, B, E)` with
`|A| = |B| = M`).

For `R : Fin M → Fin M → Bool`, `bip R` is the simple bipartite graph with sides
`A = {inl a}` and `B = {inr b}` (two copies of `Fin M`) in which `inl a` and `inr b` are adjacent
exactly when `R a b = true`; there are no edges inside a side.

**Formalization Note.** Built with `SimpleGraph.fromRel`, which symmetrizes the relation and
removes loops; the relation only relates `inl a` to `inr b`, so the graph is bipartite with the
fixed bipartition `(A, B)` and simple. -/
def bip {M : ℕ} (R : Fin M → Fin M → Bool) : SimpleGraph (Fin M ⊕ Fin M) :=
  SimpleGraph.fromRel (fun x y => ∃ a b, x = Sum.inl a ∧ y = Sum.inr b ∧ R a b = true)

end HiddenPartition


