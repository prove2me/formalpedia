-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_oneTreeLPValue
-- name    : CombOpt_HeldKarp_Graph_oneTreeLPValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:41.855952+00:00
-- url     : https://prove2.me/theorems/26d94b81-c917-4c4f-baef-6272c776418d
-- title:
--   Optimal value of the 1-tree linear program (7.7)
-- statement:
--   The optimal value of (7.7) is $\min\{c^Tx : x \text{ feasible for (7.7)}\}$.
--
--   **Formalization Note** Computed as an infimum in `EReal`: attained when (7.7) is feasible, $+\infty$ when it is infeasible.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, (7.7), p. 260 (PDF p. 268)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_OneTreeLPFeasible

namespace CombOpt.HeldKarp

/-- **The optimal value of the 1-tree linear program (7.7).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, (7.7),
p. 260 (PDF p. 268): "min {c^T x : x satisfies (7.4), (7.5), (7.6), and x(δ(v_1)) = 2}".

`G.oneTreeLPValue c v₁` is the infimum of `Σ_e c_e x_e` over all `x` with
`G.OneTreeLPFeasible v₁ x`.

**Formalization Note.** The value lies in `EReal`; the feasible set is a polytope, so the infimum is
the attained minimum when it is nonempty, and `⊤` when it is empty. -/
noncomputable def Graph.oneTreeLPValue {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Graph V E) (c : E → ℝ) (v₁ : V) : EReal :=
  ⨅ (x : E → ℝ) (_ : G.OneTreeLPFeasible v₁ x), ((∑ e, c e * x e : ℝ) : EReal)

end CombOpt.HeldKarp


