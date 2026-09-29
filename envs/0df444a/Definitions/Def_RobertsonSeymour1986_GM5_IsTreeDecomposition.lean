-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
-- name    : RobertsonSeymour1986_GM5_IsTreeDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:53:32.022776+00:00
-- url     : https://prove2.me/theorems/419af660-aa95-478f-b086-11c947097c68
-- title:
--   Tree-decomposition
-- statement:
--   A **tree-decomposition** $(T,\chi)$ of a graph $G$ is a finite tree $T$ together with a family $\chi=(X_t : t\in V(T))$ of subsets of $V(G)$ (the **bags**) such that
--
--   1. $\bigcup_{t\in V(T)} X_t = V(G)$;
--   2. for each edge $e$ of $G$ there is $t\in V(T)$ with both ends of $e$ in $X_t$;
--   3. for $t,t',t''\in V(T)$, if $t'$ lies on the path of $T$ between $t$ and $t''$, then $X_t\cap X_{t''}\subseteq X_{t'}$.
--
--   Condition 3 says that the bags containing any fixed vertex form a subtree of $T$.
--
--   **Formalization Note** The tree $T$ is a simple graph on a finite type, and it must be a tree: connected, acyclic and nonempty. Condition 3 quantifies over paths of $T$ from $t$ to $t''$ and over vertices $t'$ on them; in a tree this path is unique.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 1, pp. 92–93 (PDF pp. 1–2), definition of tree-decomposition (i)–(iii); DOI 10.1016/0095-8956(86)90030-4

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- `IsTreeDecomposition G t X`: the tree `t` (on the finite type `T`) with bags `X s ⊆ V(G)`
(`s ∈ V(T)`) is a tree-decomposition of `G`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 1, pp. 92–93 (PDF pp. 1–2), unnumbered: "A *tree-decomposition* (T, χ) of a graph G is a tree
T together with a family χ = (X_t : t ∈ V(T)) of subsets of V(G), such that
(i) ⋃(X_t : t ∈ V(T)) = V(G);
(ii) for each edge e of G there exists t ∈ V(T) such that e has both ends (or its end, in the case of
a loop) in X_t;
(iii) for t, t′, t″ ∈ V(T), if t′ lies on the path of T between t and t″, then X_t ∩ X_{t″} ⊆ X_{t′}."

**Formalization Note** `t.IsTree` (connected, acyclic, and nonempty). In (iii) "the path of T
between t and t″" is any `Walk.IsPath` from `t` to `t″` (in a tree it is unique), and "t′ lies on"
it is membership in its support. Loops do not occur in a `SimpleGraph`. -/
def IsTreeDecomposition {V T : Type} [DecidableEq V] (G : SimpleGraph V) (t : SimpleGraph T) (X : T → Finset V) :
    Prop :=
  t.IsTree ∧
  (∀ v : V, ∃ s : T, v ∈ X s) ∧
  (∀ x y : V, G.Adj x y → ∃ s : T, x ∈ X s ∧ y ∈ X s) ∧
  (∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s')

end RobertsonSeymour1986.GM5


