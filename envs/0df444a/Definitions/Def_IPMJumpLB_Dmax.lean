-- Prove2me | Definitions.Def_IPMJumpLB_Dmax
-- name    : IPMJumpLB_Dmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:18.099456+00:00
-- url     : https://prove2.me/theorems/77140263-47ae-4e18-91e9-06cae45864ac
-- title:
--   Largest gap contribution $D_{\max}(s, f) = \max_e s_e f_e$
-- statement:
--   For a potential vector $x$ with slacks $s = c - Bx$ and a flow $f$,
--   $$
--   D_{\max}(s, f) = \max_{e \in E} s_e f_e
--   $$
--   is the largest contribution of a single arc to the duality gap. The centrality condition of an $\eta$-iterate reads $D_{\max}(s, f) \le D(s, f)/\eta$.
--
--   **Formalization Note** Written as the supremum $\sup_e s_e f_e$ over the arc type. On a finite nonempty arc type this is the maximum; every theorem of the mission that uses it concerns an instance with at least one arc.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 2, p.3 (below (1))

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack

namespace IPMJumpLB

/-- The largest arc contribution to the duality gap, `D_max(s, f) = max_e s_e f_e`
(Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §2, p.3, below (1)).

**Formalization Note** Written as the supremum `⨆ e, s_e f_e`. On a finite nonempty arc type this
is the maximum (the range is finite, hence bounded above); every statement of the mission that uses
it is about an instance with at least one arc. -/
noncomputable def Dmax {V E : Type*} (I : FlowInstance V E) (x : V → ℝ) (f : E → ℝ) : ℝ :=
  ⨆ e, slack I x e * f e

end IPMJumpLB


