-- Prove2me | Definitions.Def_IPMJumpLB_IsEtaIterate
-- name    : IPMJumpLB_IsEtaIterate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:13.02538+00:00
-- url     : https://prove2.me/theorems/952aa1ce-f4f5-4c61-862c-639820821fc8
-- title:
--   $\eta$-iterate (Definition 2.1)
-- statement:
--   Fix a parameter $\eta$. An **$\eta$-iterate** of a min-cost flow instance is a strictly feasible primal-dual point $(x, s, f)$: $B^\top f = d$, $f > 0$ and $s = c - Bx > 0$, satisfying the **centrality condition**
--   $$
--   \sum_{e \in E} s_e f_e \ \ge\ \eta \max_{e' \in E} s_{e'} f_{e'} . \tag{1}
--   $$
--   The condition prevents the duality gap from concentrating on a few arcs. The central path of the standard log barrier consists of $m$-iterates, and Lewis-weight and volumetric central paths of $(n-1)$-iterates.
--
--   **Formalization Note** The iterate is the pair $(x, f)$; the slack vector is computed as $s = c - Bx$, so the clause "$s = c - Bx$" holds by construction. Condition (1) is written as $\eta\, s_e f_e \le \langle s, f\rangle$ for every arc $e$, which is equivalent on a nonempty arc set and avoids a maximum. The paper fixes the parameter in the range $1 \le \eta \le m$; that range is not part of the predicate (it constrains the parameter, not the point), and the parameter used in Theorem 4.1 lies in it.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Definition 2.1, Eq. (1), p.3

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack
import Definitions.Def_IPMJumpLB_IsFlowFeasible
import Definitions.Def_IPMJumpLB_gap

namespace IPMJumpLB

/-- Definition 2.1 (η-iterate) (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), p.3): a strictly feasible primal-dual point, i.e.
`B⊤f = d`, `f > 0` and `s = c − Bx > 0`, satisfying the centrality condition (1)
`∑_e s_e f_e ≥ η max_e' s_e' f_e'`.

**Formalization Note** The iterate is the pair `(x, f)`; the slack vector is computed as
`s = c − Bx` (`slack`), so the condition `s = c − Bx` of the triple holds by construction.
Condition (1) is written in the equivalent multiplied form `∀ e, η s_e f_e ≤ ⟨s, f⟩`, which avoids
a maximum. The range `1 ≤ η ≤ m` that the paper fixes for the parameter is not part of the
predicate: it is a range for the parameter, not a property of the point. -/
def IsEtaIterate {V E : Type*} [Fintype E] [DecidableEq V] (I : FlowInstance V E) (η : ℝ)
    (x : V → ℝ) (f : E → ℝ) : Prop :=
  IsFlowFeasible I f ∧ (∀ e, 0 < f e) ∧ (∀ e, 0 < slack I x e) ∧
    ∀ e, η * (slack I x e * f e) ≤ gap I x f

end IPMJumpLB


