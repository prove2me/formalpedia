-- Prove2me | Definitions.Def_TreewidthApprox_Partition_Setting
-- name    : TreewidthApprox_Partition_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:45.987777+00:00
-- url     : https://prove2.me/theorems/87767e50-d762-48ad-9c48-59ac91d5429e
-- title:
--   p. 321 — balanced S-separators (every component of G ∖ X holds at most |S|/2 vertices of S)
-- statement:
--   Let $G$ be a finite simple graph with vertex set $V$, and let $X,S\subseteq V$. Two vertices outside $X$ are connected in $G\setminus X$ when a walk in $G$ joins them without visiting any vertex of $X$. For $u\notin X$, write $C_X(u)$ for the vertex set of its component in $G\setminus X$.
--
--   The set $X$ is a **balanced $S$-separator** when
--
--   $$
--   \forall u\in V\setminus X,\qquad 2\,|C_X(u)\cap S|\le |S|.
--   $$
--
--   This predicate gives the counting language of Lemma 2.9.
--
--   **Formalization Note** The half bound is cleared of denominators over natural numbers. A balanced $S$-separator carries no size bound on $X$; the bound in Lemma 2.1 belongs to its existence claim. Every vertex of a connecting walk must avoid $X$. The walk relation, the component $C_X(u)$ (`avoidComp`) and the no-edge predicate between vertex sets (`NoEdge`, used in Lemma 2.9) are imported from the shared module `TreewidthApprox.Pushed.Setting`; this item defines only `IsBalancedSSep`.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), pp. 320–321, Notation and §2.1 definition of balanced S-separator; p. 328, Lemma 2.9 cross-part edge condition, https://doi.org/10.1137/130947374

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

namespace TreewidthApprox.Partition

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A (one-half)-balanced `S`-separator (p. 321): each component of `G \ X` contains
at most half of `S`. There is no bound on the size of `X`; the size bound in Lemma 2.1
belongs to that existence theorem and is absent from Lemma 2.9. -/
def IsBalancedSSep (G : SimpleGraph V) (S X : Finset V) : Prop :=
  ∀ u ∉ X, 2 * (TreewidthApprox.Pushed.avoidComp G X u ∩ S).card ≤ S.card

end TreewidthApprox.Partition


