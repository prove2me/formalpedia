-- Prove2me | Definitions.Def_MVBlossoms_IsBridge
-- name    : MVBlossoms_IsBridge
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:43:30.202917+00:00
-- url     : https://prove2.me/theorems/cf2b9168-fbbb-4d49-8205-df07d40a159a
-- title:
--   Bridge
-- statement:
--   An edge of $G$ (matched or unmatched) is a **bridge** if it is not a prop. A bridge $(u,v)$ is **of tenacity $t$** if $\mathrm{tenacity}(u,v)=t$.
--
--   Bridges are where the even and odd shortest alternating paths of a blossom meet; Statement 1 of Theorem 3 locates one on every max level path.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 10, p.2018

import Mathlib
import Definitions.Def_MVBlossoms_IsProp

namespace MVBlossoms

/-- **Bridge.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 10, p.2018: "An edge that is not a prop will be defined to
be a bridge."

**Formalization Note.** `IsBridge M u v`: `(u, v)` is an edge of `G` (matched or unmatched) and is
not a prop. It is symmetric in `u, v`. A bridge "of tenacity t" is one with
`edgeTenacity M u v = t`. -/
def IsBridge {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (u v : V) : Prop :=
  G.Adj u v ∧ ¬ IsProp M u v

end MVBlossoms


