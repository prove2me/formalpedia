-- Prove2me | Definitions.Def_RelaxedIndexability_RelaxedIndexable
-- name    : RelaxedIndexability_RelaxedIndexable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:53.033329+00:00
-- url     : https://prove2.me/theorems/f01b3105-f9c5-4aea-89cf-bd2793936236
-- title:
--   Relaxed indexability (Definition 2)
-- statement:
--   An arm satisfies **relaxed indexability** (with respect to the threshold policy, discount factor $\beta$) if for every belief $\omega$ in the probability simplex there is a **unique** subsidy $m$ such that, with $\omega$ made a point in the threshold, taking the active and the passive action at $\omega$ and following the threshold policy afterwards achieve the same performance:
--   $$
--   \hat V_{\beta,m}(\omega; u=1) = \hat V_{\beta,m}(\omega; u=0).
--   $$
--   A restless bandit with arms $1, \dots, N$ satisfies relaxed indexability if every arm does.
--
--   Under relaxed indexability, the unique such subsidy is the **approximated Whittle index** $\hat W(\omega)$ of the belief $\omega$.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Definition 2, p.22; (37), p.21

import Mathlib
import Definitions.Def_RelaxedIndexability_Arm
import Definitions.Def_RelaxedIndexability_thresholdValue

namespace RelaxedIndexability

/-- **Relaxed indexability of one arm** (Liu, arXiv:2107.11939v4, Definition 2, p.22, with (37),
p.21): for every belief `ω` in the simplex there is a unique subsidy `m` such that, with `ω` made a
point in the threshold, taking the active and the passive action at `ω` and following the threshold
policy afterwards achieve the same performance. -/
def Arm.RelaxedIndexable (β : ℝ) (A : Arm) : Prop :=
  ∀ ω ∈ stdSimplex ℝ (Fin A.K), ∃! m : ℝ,
    thresholdActionValue β A.P A.B ω m true ω = thresholdActionValue β A.P A.B ω m false ω

/-- **Relaxed indexability of a restless bandit** with arms `arms : Fin N → Arm` and discount
factor `β` (Liu, arXiv:2107.11939v4, Definition 2, p.22): every arm satisfies relaxed
indexability, i.e. the unique-indifference-subsidy condition holds for each arm state. -/
def RelaxedIndexable (β : ℝ) {N : ℕ} (arms : Fin N → Arm) : Prop :=
  ∀ n, (arms n).RelaxedIndexable β

end RelaxedIndexability


