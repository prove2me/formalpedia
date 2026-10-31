-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_lowerValue
-- name    : ContPatrol_MetricGraph_lowerValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:27.823728+00:00
-- url     : https://prove2.me/theorems/768f8ee3-2f46-4ac6-aedb-c0df3a3eec99
-- title:
--   Lower and upper value of the game $(Q,\alpha)$
-- statement:
--   The **lower value** is the supremum of the interception probabilities $r$ that some mixed patrol guarantees; the **upper value** is the infimum of the $r$ to which some mixed attack holds every patrol. The game has value $V$ when both equal $V$.
--
--   The paper's statements about $V$ are statements about these two numbers: $V\ge v$ means lower value $\ge v$, $V\le v$ means upper value $\le v$.
--
--   **Formalization Note** The existence of the value (Garrec 2019) is not assumed. Both sets are nonempty and bounded (by $0$ and $1$), so the supremum and the infimum are genuine.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, p.6

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_PatrolGuarantee

namespace ContPatrol

namespace MetricGraph

open MeasureTheory

variable {V E : Type}

/-- **The lower value of the continuous patrolling game (Q, α).**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, p.6:
"The value of the game, denoted V, is the interception probability, with best play on both
sides."

`G.lowerValue α` is the supremum of the interception probabilities that a mixed patrol can
guarantee against every attack.

**Formalization Note.** The paper's `V` is used through the pair (lower value, upper value):
"V = v" is `lowerValue = v ∧ upperValue = v`, "V ≥ v" is `v ≤ lowerValue`, and "V ≤ v" is
`upperValue ≤ v`. Existence of the value (Garrec 2019) is not assumed. The set is nonempty
(`r = 0`) and bounded above by `1` on a network (which has a point), so the supremum is a genuine
one. -/
noncomputable def lowerValue (G : MetricGraph V E) (α : ℝ) : ℝ :=
  sSup {r | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (S : Ω → ℝ → G.Point),
    G.PatrolGuarantee α P S r}

/-- **The upper value of the continuous patrolling game (Q, α)**: the infimum of the
interception probabilities to which a mixed attack can hold every patrol.
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, p.6.

**Formalization Note.** The set is nonempty (`r = 1`) and bounded below by `0` (constant paths
are patrols), so the infimum is a genuine one. -/
noncomputable def upperValue (G : MetricGraph V E) (α : ℝ) : ℝ :=
  sInf {r | ∃ ν : Measure (G.Point × ℝ), G.AttackGuarantee α ν r}

end MetricGraph

end ContPatrol


