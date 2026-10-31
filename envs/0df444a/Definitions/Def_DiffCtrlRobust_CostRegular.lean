-- Prove2me | Definitions.Def_DiffCtrlRobust_CostRegular
-- name    : DiffCtrlRobust_CostRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:53.679367+00:00
-- url     : https://prove2.me/theorems/717c4d50-9357-4263-bd51-51dd92f2828f
-- title:
--   Regularity of a running cost: (A4) and (A5)(iii)
-- statement:
--   A running cost $c:\mathbb R^d\times\mathbb U\to\mathbb R$ is regular with bound $M>0$ if $\|c\|_\infty\le M$, $c$ is jointly continuous in $(x,\zeta)$, and on every ball $\mathcal B_R$ it is Lipschitz in its first argument with a constant that does not depend on $\zeta\in\mathbb U$.
--
--   This is the common content of (A4) for the true cost and of (A5)(iii) for the approximating costs.
--
--   **Formalization Note** The sign of the cost is not part of this definition; (A4) adds $c\ge0$ as a separate hypothesis. The Lipschitz constant on each ball is existentially quantified, so it may vary from model to model.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2.1, p.6, (A4), and §2.2, p.8, (A5)(iii)

import Definitions.Def_EthierKurtz_SDEState

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The regularity of a running cost in (A4) and (A5)(iii) (arXiv:2205.05894v2, §2.1, p.6, and
§2.2, p.8): bounded by the positive constant `M`, jointly continuous, and locally Lipschitz in its
first argument uniformly in `ζ ∈ U`.

**Formalization Note.** The sign of the cost is not part of this predicate: (A4) adds `c ≥ 0`
where it is used. The Lipschitz constant on each ball is existential, not a parameter, since it
may differ from model to model. -/
structure CostRegular {d : ℕ} {U : Type*} [TopologicalSpace U] (M : ℝ)
    (c : SDEState d → U → ℝ) : Prop where
  /-- `M` is positive. -/
  pos : 0 < M
  /-- `‖c‖∞ ≤ M`. -/
  bounded : ∀ x ζ, |c x ζ| ≤ M
  /-- `c` is jointly continuous. -/
  continuous_cost : Continuous (fun p : SDEState d × U => c p.1 p.2)
  /-- `c` is locally Lipschitz in `x`, uniformly in `ζ`. -/
  locallyLipschitz : ∀ R, 0 < R → ∃ L : ℝ, ∀ x ∈ Metric.ball (0 : SDEState d) R,
    ∀ y ∈ Metric.ball (0 : SDEState d) R, ∀ ζ, |c x ζ - c y ζ| ≤ L * ‖x - y‖

end DiffCtrlRobust


