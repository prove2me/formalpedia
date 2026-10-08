-- Prove2me | Definitions.Def_P7ThreeColor_Lemma11_Setting
-- name    : P7ThreeColor_Lemma11_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:28.180285+00:00
-- url     : https://prove2.me/theorems/9d5bb901-bfc6-4b00-be9d-fa2c907a65b1
-- title:
--   Lemma 11 (hypotheses), p. 14, and §3.1, p. 15 — the sets X, Dᵢ and Nᵢ(x)
-- statement:
--   Let $G$ be a graph with a palette $L$ (lists $L(v) \subseteq \{1,2,3\}$) and let $S \subseteq V(G)$. Write $X$ for the set of vertices whose list has size $3$, i.e. $L(v) = \{1,2,3\}$.
--
--   **The hypotheses of Lemma 11.** We say that $(G, L, S)$ satisfies the hypotheses of Lemma 11 if
--
--   1. $G$ is connected and $P_7$-free;
--   2. $S$ is a seed of $(G,L)$;
--   3. if $v \in S$ and $w \in N(S)$ are adjacent, then $L(v) \cap L(w) = \emptyset$;
--   4. $X$ is a stable set;
--   5. $X$ is anticomplete to $V(G) \setminus (\overline{S} \cup X)$, where $\overline{S} = S \cup N(S)$: no vertex of $X$ is adjacent to a vertex outside $\overline{S} \cup X$;
--   6. no vertex $x \in X$ has a connected neighborhood: the subgraph $G[N(x)]$ is not connected.
--
--   **The sets of §3.1.** For $i \in \{1,2,3\}$ let
--   $$D_i = \{\, v \in N(S) : L(v) = \{1,2,3\} \setminus \{i\} \,\},$$
--   and for a vertex $x$ let $N_i(x) = N(x) \cap D_i$.
--
--   These hypotheses are the standing setting of the proof of Lemma 11 (Section 3.1: "Let $G$, $L$, $S$ and $X$ be as in the statement of Lemma 11"), the final step of the paper's algorithm. The conclusion of Lemma 11 (a decision procedure with running time $O(|V(G)|^9(|V(G)|+|E(G)|))$) is not part of this definition.
--
--   **Formalization Note** Colors $1,2,3$ are `0,1,2` in `Fin 3`; $\{1,2,3\} \setminus \{i\}$ is `Finset.univ.erase i`. The paper's sets $X_i$ and its fixed choice of vertices $n_j(x), n_k(x)$ are not defined; statements quantify over all admissible choices instead. A graph with no edges at a vertex $x$ has an empty neighborhood, which Mathlib's `Connected` treats as not connected.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 14, Lemma 11 (hypotheses) and §3.1; p. 15 (definitions of D_i and N_i(x))

import Mathlib
import Definitions.Def_P7ThreeColor_Lemma11_Seed

namespace P7ThreeColor.Lemma11

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `X`: the set of vertices whose list has size 3, i.e. `L(v) = {1,2,3}` (p. 14). -/
def X (L : V → Finset (Fin 3)) : Finset V :=
  Finset.univ.filter (fun v => (L v).card = 3)

/-- The hypotheses of Lemma 11 (p. 14), the standing setting of §3.1 ("Let `G`, `L`, `S` and `X`
be as in the statement of Lemma 11"):
`G` is connected and `P₇`-free; `S` is a seed of `(G, L)`; adjacent `v ∈ S`, `w ∈ N(S)` do not
share list entries; the set `X` of vertices with lists of size 3 is stable and anticomplete to
`V(G) \ (S̄ ∪ X)`; and no vertex of `X` has a connected neighborhood. -/
structure Lemma11Hyp (G : SimpleGraph V) (L : V → Finset (Fin 3)) (S : Finset V) : Prop where
  connected : G.Connected
  p7Free : P7ThreeColor.Seed.PFree 7 G
  seed : IsSeed G L S
  noShare : ∀ v ∈ S, ∀ w ∈ P7ThreeColor.Seed.nbhd G S, G.Adj v w → Disjoint (L v) (L w)
  X_stable : ∀ x ∈ X L, ∀ y ∈ X L, ¬ G.Adj x y
  X_anticomplete : ∀ x ∈ X L, ∀ z : V, z ∉ P7ThreeColor.Seed.closure G S → z ∉ X L → ¬ G.Adj x z
  X_nbhd_not_connected : ∀ x ∈ X L, ¬ (G.induce (G.neighborSet x)).Connected

/-- `D_i` (p. 15): the vertices `v ∈ N(S)` with `L(v) = {1,2,3} \ {i}`. -/
noncomputable def D (G : SimpleGraph V) (L : V → Finset (Fin 3)) (S : Finset V) (i : Fin 3) :
    Finset V :=
  (P7ThreeColor.Seed.nbhd G S).filter (fun v => L v = Finset.univ.erase i)

open Classical in
/-- `N_i(x) = N(x) ∩ D_i` (p. 15). -/
noncomputable def Ni (G : SimpleGraph V) (L : V → Finset (Fin 3)) (S : Finset V) (i : Fin 3)
    (x : V) : Finset V :=
  (D G L S i).filter (fun v => G.Adj x v)

end P7ThreeColor.Lemma11


