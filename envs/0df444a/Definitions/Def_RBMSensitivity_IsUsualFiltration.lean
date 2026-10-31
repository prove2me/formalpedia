-- Prove2me | Definitions.Def_RBMSensitivity_IsUsualFiltration
-- name    : RBMSensitivity_IsUsualFiltration
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:22.155374+00:00
-- url     : https://prove2.me/theorems/88cebd89-f6a8-496e-bfc0-c5a7f5760eaf
-- title:
--   The usual conditions on a filtered probability space
-- statement:
--   A filtered probability space $(\Omega,\mathcal F,\{\mathcal F_t\},\mathbb P)$ satisfies the **usual conditions** if the filtration is right continuous, $\mathcal F_t=\bigcap_{s>t}\mathcal F_s$, and $\mathcal F_0$ contains every $\mathbb P$-null set.
--
--   The paper fixes such a space once and for all, so this is a hypothesis of every probabilistic statement of the mission.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §1.4, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The usual conditions on `(Ω, F, {F_t}, P)`: arXiv:1907.00472v2, §1.4, p.4, "a filtered
probability space (Ω, F, {F_t}, P) satisfying the usual conditions".

The filtration is right continuous, and `F_0` contains every `P`-null set.

**Formalization Note.** `P N` is the outer measure on an arbitrary set `N`, so the second clause
also says that `F_0`, hence `F`, is `P`-complete. Mathlib at this revision has no usual-conditions
predicate. -/
def IsUsualFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  𝓕.IsRightContinuous ∧ ∀ N : Set Ω, P N = 0 → MeasurableSet[𝓕 0] N

end RBMSensitivity


