-- Prove2me | Definitions.Def_AndOrSched_andRel
-- name    : AndOrSched_andRel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:17.270983+00:00
-- url     : https://prove2.me/theorems/d1b4409e-c7f1-49b9-b41f-84dc5c28526c
-- title:
--   The AND-precedence relation $E_\wedge$ on $N$
-- statement:
--   The AND-precedence relation on the whole job set: $(i,j)\in E_\wedge$ when $i,j\in A$ and $(i,j)$ is an AND-arc inside $A$, or $i,j\in B$ and $(i,j)$ is an AND-arc inside $B$. There are no AND-arcs between $A$ and $B$, since $E_\wedge\subseteq(A\times A)\cup(B\times B)$.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.1, "The arcs in E∧ ⊆ (A × A) ∪ (B × B)"

import Mathlib
import Definitions.Def_AndOrSched_Instance
open scoped Classical NNReal

namespace AndOrSched

/-- The AND-precedence relation `E∧` on the whole job set `N = A ⊕ B` (Happach, Schulz, arXiv:2001.07011v1, §1, p.1):
`andRel I i j` means `(i, j) ∈ E∧`, so `i` must complete before `j` starts. Since
`E∧ ⊆ (A × A) ∪ (B × B)`, there are no AND-arcs between `A` and `B`. -/
def andRel (I : Instance) : I.N → I.N → Prop
  | Sum.inl a, Sum.inl a' => I.andA a a'
  | Sum.inr b, Sum.inr b' => I.andB b b'
  | _, _ => False

end AndOrSched


