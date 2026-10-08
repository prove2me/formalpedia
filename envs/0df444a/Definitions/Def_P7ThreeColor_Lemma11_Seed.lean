-- Prove2me | Definitions.Def_P7ThreeColor_Lemma11_Seed
-- name    : P7ThreeColor_Lemma11_Seed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:39.935986+00:00
-- url     : https://prove2.me/theorems/ddd550ec-14a4-4bfc-8f3c-3f001fbe94e5
-- title:
--   §2, p. 6 — seeds of a graph with a palette
-- statement:
--   A **palette** of a graph $G$ assigns to every vertex $v$ a list $L(v) \subseteq \{1,2,3\}$.
--
--   Let $G$ be a graph with a palette $L$. A set $S \subseteq V(G)$ is a **seed** of $(G,L)$ if
--
--   1. $S$ is nonempty and 2-dominating (every vertex is at distance at most $2$ from $S$),
--   2. the subgraph $G[S]$ induced by $S$ is connected,
--   3. $|L(v)| = 1$ for every $v \in S$, and
--   4. $|L(v)| = 2$ for every $v \in N(S)$.
--
--   The palette is not required to be updated (a vertex of $N(S)$ may keep a color used by its neighbor in $S$).
--
--   Seeds are the starting configurations of the paper's list-coloring algorithm; Lemma 11 is stated for a seed $S$.
--
--   **Formalization Note** The colors $1,2,3$ of the paper are the elements $0,1,2$ of `Fin 3`, and a palette is a function `V → Finset (Fin 3)`. "Induces a connected subgraph" uses Mathlib's `Connected`, which includes nonemptiness; the nonemptiness printed in the paper is also kept as a separate field.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 4 (palette) and p. 6 (definition of a seed)

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic

namespace P7ThreeColor.Lemma11

/-- A **seed** of `(G, L)` (p. 6): a nonempty 2-dominating set `S` that induces a connected
subgraph, such that every vertex of `S` has a list of size 1 and every vertex of `N(S)` has a
list of size 2. A palette is `L : V → Finset (Fin 3)` (the paper's colors 1, 2, 3 are `0, 1, 2`).
The palette is not required to be updated. -/
structure IsSeed {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset (Fin 3)) (S : Finset V) : Prop where
  nonempty : S.Nonempty
  twoDominating : P7ThreeColor.Seed.IsTwoDominating G S
  connected : (G.induce (S : Set V)).Connected
  card_S : ∀ v ∈ S, (L v).card = 1
  card_N : ∀ v ∈ P7ThreeColor.Seed.nbhd G S, (L v).card = 2

end P7ThreeColor.Lemma11


