-- Prove2me | Definitions.Def_MVBlossoms_IsProp
-- name    : MVBlossoms_IsProp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:42:29.178056+00:00
-- url     : https://prove2.me/theorems/481bfebd-2f2c-490a-a27c-22c10c674b1c
-- title:
--   Prop
-- statement:
--   An edge $(u,v)$ is a **prop** if $u$ is a predecessor of $v$ or $v$ is a predecessor of $u$, i.e. it is the last edge of a min level path to one of its endpoints.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 10, p.2018

import Mathlib
import Definitions.Def_MVBlossoms_IsPred

namespace MVBlossoms

/-- **Prop.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 10, p.2018: the edge `(u, v)` is a prop when it is the last
edge of a min level path to one of its endpoints, i.e. `u` is a predecessor of `v` or `v` is a
predecessor of `u`.

**Formalization Note.** Being a prop is a property of the undirected edge, so the predicate is
symmetric. -/
def IsProp {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (u v : V) : Prop :=
  IsPred M u v ∨ IsPred M v u

end MVBlossoms


