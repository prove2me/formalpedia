-- Prove2me | Definitions.Def_MetricMinTest_Supplement_IsSuperharmonic
-- name    : MetricMinTest_Supplement_IsSuperharmonic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:37:32.466214+00:00
-- url     : https://prove2.me/theorems/0ca4fc00-15fb-47ce-a0f7-28c0a97a5149
-- title:
--   Superharmonic mean constraint (K.1)
-- statement:
--   An instance (one law on $[-1,1]$ per vertex) satisfies the **superharmonic constraint** (K.1) if
--   $$\mu_v\ge\sum_{w\in V^\circ}\Gamma_{vw}\,\mu_w\qquad(v\in I),$$
--   for every interior vertex $v$. These instances form the class of Theorem K.3, which replaces pairwise Lipschitz constraints.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), (K.1), p.33

import Mathlib
import Definitions.Def_MetricMinTest_Instance_mean

namespace MetricMinTest.Supplement

/-- **Superharmonic mean constraint (K.1).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (K.1), p.33: "assume µ_v ≥ ∑_{w∈V°} Γ_vw µ_w
(v ∈ I)", `I` the interior (complement of the boundary `bd`). Every vertex has a law on
`[−1, 1]` (`Instance V`). -/
def IsSuperharmonic {V : Type} [Fintype V] (Γ : Matrix V V ℝ) (bd : Finset V) (P : Instance V) :
    Prop :=
  ∀ v, v ∉ bd → ∑ w, Γ v w * P.mean w ≤ P.mean v

end MetricMinTest.Supplement


