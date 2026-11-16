-- Prove2me | Definitions.Def_MetricMinTest_Supplement_regionCost
-- name    : MetricMinTest_Supplement_regionCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:30:47.75894+00:00
-- url     : https://prove2.me/theorems/bbbb48f9-dbb5-4b42-b54c-ce4cb7e32935
-- title:
--   Regional cost $c(Z,r)=H_{Z,r}(1+\ln\rho_{Z,r})$
-- statement:
--   For a nonempty set $Z$ of targets and a radius $r\in[0,\gamma)$, the **regional cost** of the screening region $S(Z,r)=\bigcup_{z\in Z}B(z,r)$ is
--   $$c(Z,r)=H_{Z,r}\,(1+\ln\rho_{Z,r}),$$
--   with the region workload $H_{Z,r}$ and ratio $\rho_{Z,r}=|Z|(\gamma-r)^{-2}/H_{Z,r}$ of Definition 7.1. It is the cost coefficient of region $(Z,r)$ in the mixed workload (7.1).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §7, p.16

import Mathlib
import Definitions.Def_MetricMinTest_regionRatio

namespace MetricMinTest.Supplement

/-- **Regional cost `c(Z, r) = H_{Z,r}(1 + ln ρ_{Z,r})`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §7, p.16 ("put
c(Z, r) = H_{Z,r}(1 + ln ρ_{Z,r})"), with the published `regionWorkload` and `regionRatio`. -/
noncomputable def regionCost {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) (Z : Finset ι)
    (r : ℝ) : ℝ :=
  regionWorkload d γ Z r * (1 + Real.log (regionRatio d γ Z r))

end MetricMinTest.Supplement


