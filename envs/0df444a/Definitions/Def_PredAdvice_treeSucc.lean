-- Prove2me | Definitions.Def_PredAdvice_treeSucc
-- name    : PredAdvice_treeSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:56.332766+00:00
-- url     : https://prove2.me/theorems/7bd21b3f-0471-4462-8a0f-55308ad0d979
-- title:
--   Tree depth and the successor query of Appendix B
-- statement:
--   For a rooted tree $T$ (given by parents) and $v\in V(T)$, $\mathrm{depth}_T(v)$ is the number of parent steps from $v$ to the root, and the vertex at depth $i$ on the root–$v$ path is the ancestor $\mathrm{parent}^{\,\mathrm{depth}_T(v)-i}(v)$. The **successor query** returns, for vertices $w,v$:
--
--   1. the vertex at depth $i+1$ on the root–$v$ path, if $w$ is the vertex at some depth $i<\mathrm{depth}_T(v)$ of that path;
--   2. $\mathrm{NULL}$ otherwise.
--
--   The module also defines an **abstract rooted tree** (no graph involved): the root is in $V(T)$, parents of nonroot vertices stay in $V(T)$, and some depth function decreases by one along parents. Appendix B stores such trees so that this query and the parent query take constant time.
--
--   **Formalization Note** $\mathrm{NULL}$ is `none`. The depth is a minimum over parent iterates; on vertices of a tree it is the depth.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), App. B, p.29; proof of Theorem 1.1, p.24

import Mathlib
import Definitions.Def_PredAdvice_RootedTree

set_option autoImplicit false

namespace PredAdvice

/-- A rooted tree without reference to a graph (Kopelowitz, Korin, Roditty, *Using Small Advice to
Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), App. B,
p.29): the root lies in `V(T)`, every nonroot vertex of `V(T)` has its parent in `V(T)`, and some
depth function strictly decreases along parents, so that following parents from any vertex of
`V(T)` reaches the root. -/
def IsAbstractTree {V : Type*} (T : RootedTree V) : Prop :=
  T.root ∈ T.verts ∧ ∃ depth : V → ℕ, depth T.root = 0 ∧
    ∀ x ∈ T.verts, x ≠ T.root → T.parent x ∈ T.verts ∧ depth x = depth (T.parent x) + 1

/-- `depth_T(v)`: the number of parent steps from `v` to the root, `min {k | parent^[k] v = root}`.

**Formalization Note** On a vertex of `V(T)` of a tree (`IsAbstractTree`, `IsTowardTree` or
`IsAwayTree`) the set is nonempty and this is the depth; elsewhere the value is not used. -/
noncomputable def depthIn {V : Type*} (T : RootedTree V) (v : V) : ℕ :=
  sInf {k : ℕ | T.parent^[k] v = T.root}

/-- The vertex at depth `i` on the tree path from the root to `v`: `parent^[depth_T(v) − i] v`
(`i = 0` is the root, `i = depth_T(v)` is `v`). -/
noncomputable def pathVertex {V : Type*} (T : RootedTree V) (v : V) (i : ℕ) : V :=
  T.parent^[depthIn T v - i] v

open Classical in
/-- The successor query of App. B, p.29 (rule 1 of the proof of Theorem 1.1, p.24): the successor of
`w` on the path from the root to `v` in `T`. If `w` lies on that path strictly before `v`, at depth
`i < depth_T(v)`, the answer is the vertex at depth `i + 1`; otherwise the answer is `NULL`
(`none`). -/
noncomputable def treeSucc {V : Type*} (T : RootedTree V) (w v : V) : Option V :=
  if h : ∃ i, i < depthIn T v ∧ pathVertex T v i = w then
    some (pathVertex T v (Nat.find h + 1))
  else none

end PredAdvice


