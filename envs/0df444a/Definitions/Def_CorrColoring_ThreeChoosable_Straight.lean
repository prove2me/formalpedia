-- Prove2me | Definitions.Def_CorrColoring_ThreeChoosable_Straight
-- name    : CorrColoring_ThreeChoosable_Straight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:01:32.763249+00:00
-- url     : https://prove2.me/theorems/e481bf2b-f1fe-4f88-96a5-971804c2dab3
-- title:
--   Straight and full edges; renaming colours at vertices
-- statement:
--   Let $C$ be a $k$-correspondence assignment for a graph $G$.
--
--   1. An edge $uv$ is **straight** in $C$ if every $(u,c_1)(v,c_2) \in E(C_{uv})$ satisfies $c_1 = c_2$.
--   2. An edge $uv$ is **full** in $C$ if $C_{uv}$ is a perfect matching, i.e. every colour at $u$ is matched to some colour at $v$.
--   3. A $k$-correspondence assignment $C'$ is obtained from $C$ by **renaming on the vertices of a set $X$** if there are permutations $\sigma_v$ of $[k]$, with $\sigma_v$ the identity for $v \notin X$, such that for all $u, v, c, d$
--
--   $$(u,c)(v,d) \in E(C'_{uv}) \iff (u, \sigma_u(c))(v, \sigma_v(d)) \in E(C_{uv}).$$
--
--   Renaming does not change which graphs are colourable; straightness is the normal form into which Lemma 7 of Dvořák and Postle brings an assignment.
--
--   **Formalization Note** Fullness is stated from the side of $u$; since $C_{uv}$ is a partial matching between two copies of the finite set $[k]$, it is then a perfect matching. The paper defines renaming for general lists by single steps (replace colour $c_1$ at $v$ by a colour $c_2$ not in the list) and calls two assignments equivalent if one is reached from the other by repeated renaming. For two $k$-correspondence assignments, where the list at every vertex begins and ends as $[k]$, a sequence of renamings at the vertices of $X$ has exactly the effect of a permutation of $[k]$ at each vertex of $X$ (intermediate steps may use colours outside $[k]$, which is how transpositions arise), and every such permutation arises this way; the definition above encodes that.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 10, §2 (straight, full); p. 4 (renaming, equivalent correspondence assignments)

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment

namespace CorrColoring.ThreeChoosable

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

/-- The edge `uv` is straight in `C`: every `(u, c)(v, d) ∈ E(C_{uv})` has `c = d`. -/
def Straight (C : KCorrAssignment G k) (u v : V) : Prop :=
  ∀ c d, C.M u c v d → c = d

/-- The edge `uv` is full in `C`: every colour at `u` is matched in `C_{uv}`; since `C_{uv}` is
a partial matching between two copies of `[k]`, this says `C_{uv}` is a perfect matching. -/
def Full (C : KCorrAssignment G k) (u v : V) : Prop :=
  ∀ c, ∃ d, C.M u c v d

/-- `C'` is obtained from `C` by renaming colours at vertices of `X`: there is a permutation
`σ v` of `[k]` at each vertex, the identity outside `X`, such that `(u, c)(v, d) ∈ E(C'_{uv})`
iff `(u, σ u c)(v, σ v d) ∈ E(C_{uv})`. -/
def IsRenamingOn (C C' : KCorrAssignment G k) (X : Set V) : Prop :=
  ∃ σ : V → Equiv.Perm (Fin k), (∀ v, v ∉ X → σ v = 1) ∧
    ∀ u c v d, C'.M u c v d ↔ C.M u (σ u c) v (σ v d)

end CorrColoring.ThreeChoosable


