-- Prove2me | Definitions.Def_DiffCtrlRobust_admissiblePast
-- name    : DiffCtrlRobust_admissiblePast
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:55.811623+00:00
-- url     : https://prove2.me/theorems/9d077f12-e933-4165-9a35-fe847e2bbd91
-- title:
--   The filtration $\mathfrak F_s$ of an admissible control
-- statement:
--   For a $\mathrm V$-valued process $U$, the filtration used in the non-anticipativity condition is
--
--   $$
--   \mathfrak F_s:=\text{the completion of }\sigma(X_0,U_r,W_r:r\le s)\text{ relative to }(\mathfrak F,\mathbb P).
--   $$
--
--   **Formalization Note** As in `EthierKurtz.completedBrownianPast`, the null sets of $\mathbb P$ are joined explicitly, so the ambient probability space need not be complete.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, p.5

import Definitions.Def_EthierKurtz_SDEState

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- `𝔉_s := the completion of σ(X_0, U_r, W_r : r ≤ s) relative to (𝔉, ℙ)`
(arXiv:2205.05894v2, §2, p.5).

**Formalization Note.** The argument `u` is the `V`-valued control process and `ξ` the initial
state. As in `EthierKurtz.completedBrownianPast`, the null sets are joined explicitly, so `P`
itself need not be complete. -/
abbrev admissiblePast {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Type*} [MeasurableSpace U]
    (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d) (u : ℝ≥0 → Ω → ProbabilityMeasure U)
    (ξ : Ω → SDEState d) (s : ℝ≥0) : MeasurableSpace Ω :=
  (⨆ r : Set.Iic s, MeasurableSpace.comap (u r.val) inferInstance ⊔
      MeasurableSpace.comap (W r.val) inferInstance) ⊔
    MeasurableSpace.comap ξ inferInstance ⊔
    MeasurableSpace.generateFrom {A | ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ A ⊆ N}

end DiffCtrlRobust


