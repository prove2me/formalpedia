-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_lpValue537
-- name    : CombOpt_TJoin_Graph_lpValue537
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:30.214514+00:00
-- url     : https://prove2.me/theorems/890980af-3c12-4d84-8fc5-c844c1594a24
-- title:
--   Optimal value of the LP (5.37)
-- statement:
--   The **optimal value of (5.37)** is $\inf\{\sum_{e\in E}c_ex_e:\ x \text{ feasible for } (5.37)\}$.
--
--   **Formalization Note** Taken in the extended reals: $+\infty$ if (5.37) is infeasible; otherwise the feasible region is a nonempty polytope inside $[0,1]^E$ and the value is the attained real optimum.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, (5.37), p. 180 (PDF p. 188)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsFeasible537

namespace CombOpt.TJoin

/-- **Optimal value of the linear program (5.37).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 180 (PDF p. 188), (5.37).

The infimum in `EReal` of `∑_e c_e x_e` over the feasible solutions of (5.37).

**Formalization Note.** The feasible region lies in the box `[0,1]^E`, so the infimum is `⊤` when
(5.37) is infeasible and otherwise the attained, real optimal value. -/
noncomputable def Graph.lpValue537 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (T : Finset V) (c : E → ℝ) : EReal :=
  ⨅ (x : E → ℝ) (_ : G.IsFeasible537 T x), ((∑ e, c e * x e : ℝ) : EReal)

end CombOpt.TJoin


