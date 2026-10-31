-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_lpValue533
-- name    : CombOpt_TJoin_Graph_lpValue533
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:26.4051+00:00
-- url     : https://prove2.me/theorems/15c95ff3-0032-4f17-8755-065e36d43a40
-- title:
--   Optimal value of the LP (5.33)
-- statement:
--   The **optimal value of (5.33)** is $\inf\{\sum_{e\in E}c_ex_e:\ x \text{ feasible for } (5.33)\}$.
--
--   **Formalization Note** Taken in the extended reals: $+\infty$ if (5.33) is infeasible, $-\infty$ if it is unbounded below, and otherwise the attained optimum of the linear program.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, (5.33), p. 178 (PDF p. 186)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsFeasible533

namespace CombOpt.TJoin

/-- **Optimal value of the linear program (5.33).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 178 (PDF p. 186), (5.33): "Minimize ∑(c_e x_e : e ∈ E) subject to x(D) ≥ 1, for
all T-cuts D; x_e ≥ 0, for all e ∈ E."

The infimum in `EReal` of `∑_e c_e x_e` over the feasible solutions of (5.33).

**Formalization Note.** `⊤` when (5.33) is infeasible, `⊥` when it is unbounded below; otherwise
the infimum is the (attained) optimal value of the linear program. -/
noncomputable def Graph.lpValue533 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (T : Finset V) (c : E → ℝ) : EReal :=
  ⨅ (x : E → ℝ) (_ : G.IsFeasible533 T x), ((∑ e, c e * x e : ℝ) : EReal)

end CombOpt.TJoin


