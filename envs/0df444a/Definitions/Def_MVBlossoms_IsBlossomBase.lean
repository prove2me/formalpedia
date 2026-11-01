-- Prove2me | Definitions.Def_MVBlossoms_IsBlossomBase
-- name    : MVBlossoms_IsBlossomBase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:44:47.039587+00:00
-- url     : https://prove2.me/theorems/6b98ffce-bb1a-44ef-8949-2d7af7bc8554
-- title:
--   Base of a blossom of tenacity $t$
-- statement:
--   The blossom of tenacity $t$ with base $b$ is defined for $b$ basal at stage $t$ with $\mathrm{tenacity}(b)>t$ (Definition 31). The predicate states exactly these two conditions; the blossoms of tenacity $t$ are the sets $B_{b,t}$ for such $b$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 31, p.2037

import Mathlib
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_IsBasalAt

namespace MVBlossoms

/-- **Base of a blossom of tenacity t.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 31, p.2037: "Let b be a
basal vertex with tenacity(b) > t. ... Then, the blossom of tenacity t and base b is the set
B_{b,t}"; Definition 22 (p.2031) for t = t_m.

`IsBlossomBase M b t`: `b` is basal at stage `t` and `tenacity(b) > t`. "The blossoms of tenacity
t" are the sets `blossom M b t` for exactly these `b`. -/
def IsBlossomBase {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) (b : V) (t : ℕ) : Prop :=
  IsBasalAt M b t ∧ (t : ℕ∞) < tenacity M b

end MVBlossoms


