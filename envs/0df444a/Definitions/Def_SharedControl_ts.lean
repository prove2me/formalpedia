-- Prove2me | Definitions.Def_SharedControl_ts
-- name    : SharedControl_ts
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:52.628195+00:00
-- url     : https://prove2.me/theorems/a341bb7e-9704-43ff-96ba-159538a9600b
-- title:
--   The equilibrium transfer $t_s$ under shared control
-- statement:
--   The **equilibrium transfer** under shared control is the smallest nonnegative transfer satisfying Inequality (1):
--
--   $$
--   t_s \;=\; \inf\,\{\, t \ge 0 : E[s_g + t \mid m_g \ge t] \ge 0 \,\}.
--   $$
--
--   The parties select the equilibrium with the lowest transfer because it has the most good proposals offered and accepted. The surplus of shared control (3) depends on the model only through $\Pr[m_g \ge t_s]$.
--
--   **Formalization Note** The infimum is Lean's `sInf` on $\mathbb R$, which is $0$ on an empty set; the feasible set is bounded below by $0$, and under the standing assumptions it is nonempty and its infimum is attained (the milestone on $t_s$ states this), so $t_s$ is the least feasible transfer.
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §2.1, p.4

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Feasible

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §2.1, p.4 (PDF p.5): the equilibrium transfer under shared
control. "Thus, let ts be the smallest nonnegative transfer that satisfies Inequality (1)."

**Formalization Note.** `ts` is the infimum (`sInf` in `ℝ`) of the set of feasible transfers
(`SharedControl.Feasible`). In Lean `sInf` of an empty or unbounded-below set is `0`; the set is
bounded below by `0`, and under `SharedControl.Standing` it is nonempty and the infimum is
attained, i.e. `ts` is the least feasible transfer, as the paper says (milestone
`SharedControl.ts_isLeast`). -/
noncomputable def ts {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) : ℝ :=
  sInf {t | Feasible M t}

end SharedControl


