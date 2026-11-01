-- Prove2me | Definitions.Def_AndOrSched_Acyclic
-- name    : AndOrSched_Acyclic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:26.117518+00:00
-- url     : https://prove2.me/theorems/0fd092f8-06f2-48a8-95ad-6cc3a5630e30
-- title:
--   Acyclic AND-precedences
-- statement:
--   The AND-precedence graph is **acyclic**: no job $a\in A$ is a proper transitive AND-predecessor of itself, and likewise in $B$.
--
--   Every result of the mission assumes it: a precedence graph is acyclic, and the paper's w.l.o.g. reductions (transitive closure of $E_\wedge$, removal of redundant OR-arcs) presuppose it.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.1, "The precedence constraints are given by a directed graph G = (N, E∧ ∪̇ E∨)"

import Mathlib
import Definitions.Def_AndOrSched_Instance
open scoped Classical NNReal

namespace AndOrSched

/-- The AND-precedence graph `E∧` is acyclic: no job is a proper transitive AND-predecessor of
itself (Happach, Schulz, arXiv:2001.07011v1, §1, p.1, "The precedence constraints are given by a directed graph").

**Formalization Note** A precedence graph is acyclic; the paper's w.l.o.g. "E∧ is transitively
closed" and "no redundant OR-precedence constraints" (p.4) presuppose it. Acyclicity is checked
separately on `A` and on `B`, since `E∧ ⊆ (A × A) ∪ (B × B)`. -/
def Acyclic (I : Instance) : Prop :=
  (∀ a, ¬ Relation.TransGen I.andA a a) ∧ ∀ b, ¬ Relation.TransGen I.andB b b

end AndOrSched


