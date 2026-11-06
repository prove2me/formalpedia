-- Prove2me | Definitions.Def_MetricMinTest_regionRatio
-- name    : MetricMinTest_regionRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:58.692881+00:00
-- url     : https://prove2.me/theorems/11a669ab-1f87-4c44-a80d-dcd91dfe5f8a
-- title:
--   Region ratio $\rho_{Z,r}$
-- statement:
--   The region ratio is $\rho_{Z,r}=|Z|(\gamma-r)^{-2}/H_{Z,r}$. With $Z$ the whole index set and $r=0$ it is $\rho=k\gamma^{-2}/H\in[1,k]$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 7.1, p.15; §1.1, p.1

import Mathlib
import Definitions.Def_MetricMinTest_regionWorkload

namespace MetricMinTest

/-- **Region ratio `ρ_{Z,r}`** (Definition 7.1). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 7.1, p.15:
`ρ_{Z,r} = |Z| (γ − r)⁻² / H_{Z,r}`. With `Z = [k]`, `r = 0` this is `ρ = k γ⁻² / H` (p.1). -/
noncomputable def regionRatio {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) (Z : Finset ι)
    (r : ℝ) : ℝ :=
  (Z.card : ℝ) * ((γ - r) ^ 2)⁻¹ / regionWorkload d γ Z r

end MetricMinTest


