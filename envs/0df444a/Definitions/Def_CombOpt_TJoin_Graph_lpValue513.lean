-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_lpValue513
-- name    : CombOpt_TJoin_Graph_lpValue513
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:02.270771+00:00
-- url     : https://prove2.me/theorems/be3a6ebc-5522-4b27-b325-756138ae3846
-- title:
--   Optimal value of the LP (5.13)
-- statement:
--   The **optimal value of (5.13)** is $\inf\{\sum_{e\in E}c_ex_e:\ x \text{ feasible for (5.13)–(5.16)}\}$.
--
--   **Formalization Note** Taken in the extended reals: $+\infty$ if infeasible, $-\infty$ if unbounded below, otherwise the attained optimum.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.3, (5.13), p. 148 (PDF p. 156)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsFeasible513

namespace CombOpt.TJoin

/-- **Optimal value of the linear program (5.13).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.3, p. 148 (PDF p. 156), (5.13)–(5.16).

The infimum in `EReal` of `∑_e c_e x_e` over the feasible solutions of (5.13)–(5.16).

**Formalization Note.** `⊤` when infeasible, `⊥` when unbounded below; otherwise the attained
optimal value. -/
noncomputable def Graph.lpValue513 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (c : E → ℝ) : EReal :=
  ⨅ (x : E → ℝ) (_ : G.IsFeasible513 x), ((∑ e, c e * x e : ℝ) : EReal)

end CombOpt.TJoin


