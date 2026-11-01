-- Prove2me | Definitions.Def_RedundancyHT_IsCriticalSubset
-- name    : RedundancyHT_IsCriticalSubset
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:33.554182+00:00
-- url     : https://prove2.me/theorems/f2270ea1-d395-4084-b4cf-c19ec015f9a9
-- title:
--   The critical subset $\mathcal T^*$: the unique maximizer of the capacity ratio
-- statement:
--   A set $\mathcal T^*$ of job types is the **critical subset** if it is non-empty and
--   $$\rho_{\mathcal T}<\rho_{\mathcal T^*}\qquad\text{for every non-empty }\mathcal T\neq\mathcal T^*.$$
--   This combines Definition 1 with Assumption 3, which requires the maximizer to be unique. It identifies the job types whose servers saturate first as $\lambda$ increases.
--
--   **Formalization Note** The hypothesis is the first sentence of Assumption 3. The clause following "i.e." in the paper is not equivalent to that sentence: for $N=3$, $S_i=\{i\}$ and $p_1/\mu_1=p_2/\mu_2>p_3/\mu_3$ the maximizer is not unique, while the critical point lies on an edge of the capacity region, not at a vertex.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Definition 1, p.9, and Assumption 3, p.12

import Definitions.Def_RedundancyHT_capacityRatio

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The critical subset, Definition 1 under Assumption 3** (arXiv:2005.14566v5, pp.9, 12): `𝒯` is
non-empty and every other non-empty set of job types has a strictly smaller capacity ratio.

**Formalization Note.** This is the first sentence of Assumption 3 ("the subset 𝒯* that maximizes
the capacity ratio ρ_𝒯 is unique"). The clause after "i.e." is not equivalent to it. -/
def IsCriticalSubset {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) : Prop :=
  T.Nonempty ∧ ∀ T' : Finset (Fin n), T'.Nonempty → T' ≠ T → capacityRatio D T' < capacityRatio D T

end RedundancyHT


