-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_IMc
-- name    : BauerleRiederMDP_LPDuality_IMc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:22.242644+00:00
-- url     : https://prove2.me/theorems/24710891-01b4-4fce-8119-9dd3b5d6ef80
-- title:
--   The set $I\!M_c$ of uniformly continuous $b$-bounded functions
-- statement:
--   Let $b:E\to\mathbb R_+$ be a bounding function on a state space $E$ with a uniform structure, and let $\mathbb B_b$ be the set of measurable $v:E\to\mathbb R$ with $\|v\|_b=\sup_x |v(x)|/b(x)<\infty$. Define
--   $$
--   I\!M_c:=\{v\in\mathbb B_b \mid v \text{ is uniformly continuous on } E\}.
--   $$
--
--   The state space discretization of §7.5.3 assumes the Structure Assumption (SA) for this set: $\mathcal T$ maps $I\!M_c$ into itself, every $v\in I\!M_c$ has a maximizer, and the limit value function lies in $I\!M_c$.
--
--   **Formalization Note** $\mathbb B_b$ is the platform set `MDPFinance.LPDuality.IBb b` of measurable $v$ with $|v|\le c\,b$ for some $c\ge 0$, which is $\|v\|_b<\infty$ when $b\ge 1$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.5.3, p.221 (PDF 232), IM_c := {v ∈ IB_b | v is uniformly continuous on E}

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- `IM_c := {v ∈ IB_b | v is uniformly continuous on E}` (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §7.5.3, p.221, PDF 232), the set for which the
Structure Assumption (SA) is assumed in the state space discretization.

**Formalization Note** `IB_b` is the platform set `MDPFinance.LPDuality.IBb b` of measurable
`v : E → ℝ` with `|v| ≤ c·b` for some constant `c ≥ 0`, which is `‖v‖_b < ∞` when `b ≥ 1`. The
state space carries a uniform structure (in this mission: a subset of a real normed space). -/
def IMc {E : Type*} [MeasurableSpace E] [UniformSpace E] (b : E → ℝ) : Set (E → ℝ) :=
  {v | v ∈ IBb b ∧ UniformContinuous v}

end BauerleRiederMDP.LPDuality


