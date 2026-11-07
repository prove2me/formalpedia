-- Prove2me | Definitions.Def_MinBisectFPT_IsUnbreakableTD
-- name    : MinBisectFPT_IsUnbreakableTD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:22.131207+00:00
-- url     : https://prove2.me/theorems/46b1a9ae-793f-4161-8d08-fed380b2d605
-- title:
--   Edge-unbreakable sets and properties (D1)–(D3)
-- statement:
--   A set $\beta\subseteq V(H)$ is **$(q,k)$-edge-unbreakable** in $H$ if every $X\subseteq V(H)$ with $|\delta_H(X)|\le k$ satisfies $|X\cap\beta|\le q$ or $|\beta\setminus X|\le q$.
--
--   A rooted tree decomposition of $G$ has properties (D1)–(D3) if:
--
--   1. (D1) every adhesion has at most $2k$ vertices;
--   2. (D2) for every non-root node $t$, the component $\alpha(t)$ is nonempty, $G[\alpha(t)]$ is connected, and $N_G(\alpha(t))=\sigma(t)$;
--   3. (D3) every bag $\beta(t)$ is $(3k,k)$-edge-unbreakable in the subtree graph $G_t$.
--
--   (D3) is stated in $G_t$, not in $G$, and it is what the dynamic program of the mission uses.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), §1.1, pp.2–3

import Mathlib
import Definitions.Def_MinBisectFPT_RootedTD

open scoped Classical

namespace MinBisectFPT

/-- **Edge-unbreakable sets.** Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable
Decompositions*, STOC 2027 submission (manuscript sha256 8db80a52…), §1.1, p.2: "A set β ⊆ V(H) is
(q, k)-edge-unbreakable in a graph H if every X ⊆ V(H) with at most k edges of H leaving it satisfies
|X ∩ β| ≤ q or |β \ X| ≤ q."

**Formalization Note** `VH` is the vertex set `V(H)` inside the ambient type. -/
def IsEdgeUnbreakable {n : ℕ} (H : SimpleGraph (Fin n)) (VH β : Finset (Fin n)) (q k : ℕ) : Prop :=
  ∀ X : Finset (Fin n), X ⊆ VH → cutSize H X ≤ k → (X ∩ β).card ≤ q ∨ (β \ X).card ≤ q

/-- **Properties (D1)–(D3) of Theorem 1.3** (ibid., p.3). `N_G` and `G[α(t)]` in (D2) are in `G`; the
graph of (D3) is the subtree graph `G_t`. -/
def IsUnbreakableTD {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (k : ℕ) : Prop :=
  (∀ t, (T.adhesion t).card ≤ 2 * k) ∧
    (∀ t, T.parent t ≠ none →
      (T.component t).Nonempty ∧ (G.induce (T.component t : Set (Fin n))).Connected ∧
        nbr G (T.component t) = T.adhesion t) ∧
    ∀ t, IsEdgeUnbreakable (subtreeGraph G T t) (T.cone t) (T.bag t) (3 * k) k

end MinBisectFPT


