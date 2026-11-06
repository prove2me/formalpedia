-- Prove2me | Definitions.Def_MetricMinTest_distProfile
-- name    : MetricMinTest_distProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:11.119227+00:00
-- url     : https://prove2.me/theorems/cf84f421-5423-4274-98ce-11f94be5515a
-- title:
--   Distance profile $s_d=\max_j s_j$
-- statement:
--   The distance profile of the metric is $s_d=\max_j s_j$. Theorem 6.1 shows $H_d(\gamma)\le F_d(\gamma)\le s_dH_d(\gamma)$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 6.1, p.14

import Mathlib
import Definitions.Def_MetricMinTest_centerProfile

namespace MetricMinTest

/-- **Distance profile `s_d = maxⱼ sⱼ`** (Theorem 6.1). Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 6.1, p.14.

**Formalization Note.** A real supremum over the finite index type, which is the maximum when the
index type is nonempty. -/
noncomputable def distProfile {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) : ℝ :=
  ⨆ j, centerProfile d γ j

end MetricMinTest


