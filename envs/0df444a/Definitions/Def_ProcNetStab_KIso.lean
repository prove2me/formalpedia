-- Prove2me | Definitions.Def_ProcNetStab_KIso
-- name    : ProcNetStab_KIso
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:46.126915+00:00
-- url     : https://prove2.me/theorems/16fabbb9-45ed-41c5-935c-63ca2c7f0387
-- title:
--   $k$-isomorphic relation $(i,h) \simeq_k (i',h')$
-- statement:
--   Let $g$ be the observed network, $k \in \mathbb N$, and let every node carry a type through a map $L : V \to T$. For agents $i, i'$ and networks $h, h'$ we write $(i, h) \simeq_k (i', h')$ if
--
--   1. $h$ and $h'$ are both adjacent to $g$, and
--   2. there is an isomorphism $\sigma$ from the $k$-neighborhood $N^k_i(h)$ to the $k$-neighborhood $N^k_{i'}(h')$ with $\sigma(i) = i'$ that preserves types: $L(u) = L(\sigma(u))$ for every node $u$ of $N^k_i(h)$.
--
--   Here an isomorphism is a bijection between the node sets of the two neighborhoods with $uv$ a link of $N^k_i(h)$ iff $\sigma(u)\sigma(v)$ is a link of $N^k_{i'}(h')$. Agents related by $\simeq_k$ occupy the same position in their local networks; the relation is the similarity relation on which $k$-anonymity is built.
--
--   **Formalization Note** The node set $V$ and the type space $T$ are arbitrary types; untyped networks (Definition 3.4) are the case $T$ = `Unit`. The isomorphism is a Mathlib graph isomorphism `≃g` between the induced subgraphs. The relation is not declared an equivalence relation by fiat: it is empty off the networks adjacent to $g$, and on them it is reflexive, symmetric and transitive by construction.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 3.8, p.10 (= Definition A.1, p.OA-1); types-preserving isomorphism, Definitions 3.4–3.5, pp.8–9

import Mathlib
import Definitions.Def_ProcNetStab_IsAdjacentNet
import Definitions.Def_ProcNetStab_kNbhd

namespace ProcNetStab

/-- The **`k`-isomorphic relation** `(i, h) ≃k (i', h')` (Chiong, Qi, *Stability of Procurement
Networks* (authors' manuscript, 2025), Definition 3.8, p.10, restated as Definition A.1, p.OA-1;
types-preserving isomorphism, Definition 3.5, p.9): both `h` and `h'` are adjacent to the observed
network `g`, and there is an isomorphism `σ` from the `k`-neighborhood of `i` in `h` to the
`k`-neighborhood of `i'` in `h'` with `σ(i) = i'` that preserves the types `L`.

**Formalization Note** Nodes form an arbitrary type `V` and types an arbitrary type `T`, with type
map `L : V → T` (take `T = Unit` for untyped networks, Definition 3.4). The isomorphism is a
Mathlib graph isomorphism `≃g` of the induced subgraphs `kNbhd`. The relation is not made an
equivalence relation by fiat: off the networks adjacent to `g` it is empty, and on them it is
reflexive, symmetric and transitive by construction. -/
def KIso {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ)
    (i : V) (h : SimpleGraph V) (i' : V) (h' : SimpleGraph V) : Prop :=
  IsAdjacentNet g h ∧ IsAdjacentNet g h' ∧
    ∃ σ : kNbhd h k i ≃g kNbhd h' k i',
      (σ ⟨i, mem_ball_self h k i⟩ : V) = i' ∧ ∀ u : ball h k i, L (u : V) = L (σ u : V)

end ProcNetStab


