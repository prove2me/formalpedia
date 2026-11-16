-- Prove2me | Definitions.Def_CondGeoVerif_Supplement_critA
-- name    : CondGeoVerif_Supplement_critA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:08:50.392198+00:00
-- url     : https://prove2.me/theorems/b3ee02d4-bbfd-4b7f-a19f-bc8c1c1367ad
-- title:
--   Gaussian density $\phi$, upper tail $\bar\Phi$, and the critical constants $A=\sqrt{2\log 2}$, $\eta_c=\bar\Phi(A)$, $a_c=2\Phi(A)-1$
-- statement:
--   Let $\phi(x)=e^{-x^2/2}/\sqrt{2\pi}$ be the standard Gaussian density, $\Phi$ the standard Gaussian distribution function and $\bar\Phi=1-\Phi$ its upper tail. The **critical Gaussian constants** of the paper are
--   $$A=\sqrt{2\log 2},\qquad \eta_c=\bar\Phi(A),\qquad a_c=2\Phi(A)-1=1-2\eta_c .$$
--   The constant $A$ is characterized by $\phi(A)=\phi(0)/2$; $\eta_c$ is the critical noise rate and $a_c$ the critical signal of the halfspace and slab results (Appendices D–F, H).
--
--   **Formalization Note** $\Phi$ and its real inverse on $(0,1)$ are the published `Cohen2019.Robust.Phi` and `Cohen2019.Robust.PhiInvReal`; the inverse is only evaluated on $(0,1)$ in this supplement. $\log$ is the natural logarithm.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), App. D, p.37 (PDF p.40); §5, p.11; (E.1), p.43; §F.3, p.49

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

set_option autoImplicit false

namespace CondGeoVerif.Supplement

noncomputable section

open MeasureTheory ProbabilityTheory Cohen2019.Robust
open scoped Matrix

/-- The standard Gaussian density `ϕ(x) = e^{−x²/2}/√(2π)` (T. Y. Chen, *The Conditional Geometry
of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, App. D, p.37 = PDF p.40:
"Let ϕ and Φ denote the standard Gaussian density and distribution function"). -/
noncomputable def phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The standard Gaussian upper tail `Φ̄(x) = 1 − Φ(x)` (Chen, Oct. 2026, App. D, p.37: "write
Φ̄ = 1 − Φ"). `Φ` is the published `Cohen2019.Robust.Phi = cdf (gaussianReal 0 1)`. -/
noncomputable def Phibar (x : ℝ) : ℝ := 1 - Phi x

/-- **The critical Gaussian constants** (Chen, Oct. 2026, App. D, p.37 = PDF p.40; §5, p.11; App. E,
(E.1), p.43; App. F, p.49): `A = √(2 log 2)`, the critical noise rate `η_c = Φ̄(A)` and the critical
signal `a_c = 2Φ(A) − 1 = 1 − 2η_c`. `ϕ(A) = ϕ(0)/2` characterizes `A`.

**Formalization Note** `log` is the natural logarithm. `Φ` is the published Gaussian cdf
`Cohen2019.Robust.Phi`; its real inverse `Cohen2019.Robust.PhiInvReal` (an infimum, exact on
`(0, 1)`) is used for `Φ⁻¹` throughout the supplement and is only evaluated on `(0, 1)`. -/
noncomputable def critA : ℝ := Real.sqrt (2 * Real.log 2)

/-- The critical noise rate `η_c = Φ̄(A)`, `A = √(2 log 2)` (Chen, Oct. 2026, §5, p.11; App. F.3,
p.49: "η_c = Φ̄(√(2 log 2))"). -/
noncomputable def etaC : ℝ := Phibar critA

/-- The critical signal `a_c = 2Φ(A) − 1` (Chen, Oct. 2026, App. D, p.37; App. E, p.43). -/
noncomputable def aC : ℝ := 2 * Phi critA - 1

end

end CondGeoVerif.Supplement


