-- Prove2me | Definitions.Def_MVBlossoms_Tset
-- name    : MVBlossoms_Tset
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:43:21.861279+00:00
-- url     : https://prove2.me/theorems/d8051bd2-07a3-462e-89b7-560a5bdf233d
-- title:
--   The set $T_{b,t}$
-- statement:
--   For a vertex $b$ and a number $t$,
--
--   $$
--   T_{b,t}=\{v\in V : \mathrm{tenacity}(v)=t,\ \mathrm{base}(v)=b\},
--   $$
--
--   the vertices of tenacity exactly $t$ whose base is $b$. For $t=t_m$ it is the blossom $B_{b,t_m}$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 31, p.2037

import Mathlib
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_IsBase

namespace MVBlossoms

/-- **The set `T_{b,t}`.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 31, p.2037: "T_{b,t} = {v ∈ U_t | base(v) =
b}", where U_t = {u ∈ V | tenacity(u) = t} (Theorem 3, p.2034); for t = t_m this is the blossom
of Definition 22 (p.2031). -/
def Tset {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) (b : V) (s : ℕ) : Set V :=
  {v | tenacity M v = (s : ℕ∞) ∧ IsBase M v b}

end MVBlossoms


