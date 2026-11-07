-- Prove2me | Definitions.Def_PredAdvice_routeStep
-- name    : PredAdvice_routeStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:55.932721+00:00
-- url     : https://prove2.me/theorems/7c932f71-4c03-4dec-818a-172123f49987
-- title:
--   The forwarding step of the routing rules
-- statement:
--   Given a tree $T^-$ directed toward its root $x$, a tree $T^+$ directed away from its root $y$, the destination $v$ and the current vertex $w$, one **forwarding step** applies the rules in order:
--
--   1. if $w$ lies on the $y$–$v$ path in $T^+$ (before $v$), forward to the vertex immediately following $w$ on that path;
--   2. otherwise, if $w=x$ and $x\neq y$, forward to $y$;
--   3. otherwise forward to the parent of $w$ in $T^-$.
--
--   This is the execution step of the advice routing structure of Theorem 1.1: the advice names the two trees, and each query is one forwarding step.
--
--   **Formalization Note** The step reads only the two trees, $v$ and $w$, never the source of the route or a history, which is the statelessness required by the model.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), proof of Theorem 1.1, p.24

import Mathlib
import Definitions.Def_PredAdvice_treeSucc

set_option autoImplicit false

namespace PredAdvice

/-- One forwarding step of the routing rules (Kopelowitz, Korin, Roditty, *Using Small Advice to
Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), proof of
Theorem 1.1, p.24), at the current vertex `w`, for destination `v`, with the trees `T⁻` (directed
toward its root `x`) and `T⁺` (directed away from its root `y`):

1. if `w` lies on the `y–v` path in `T⁺` (strictly before `v`), forward to the vertex immediately
   following `w` on that path (`treeSucc`);
2. otherwise, if `w = x` and `x ≠ y`, forward to `y`;
3. otherwise forward to the parent of `w` in `T⁻`.

**Formalization Note** The step reads only the two trees, the destination and the current
vertex, never the source of the route or any history: this is the statelessness of the model. -/
noncomputable def routeStep {V : Type*} [DecidableEq V] (Tm Tp : RootedTree V) (v w : V) : V :=
  match treeSucc Tp w v with
  | some c => c
  | none => if w = Tm.root ∧ Tm.root ≠ Tp.root then Tp.root else Tm.parent w

end PredAdvice


