-- Prove2me | Definitions.Def_OWFLocalDesc_succSampler
-- name    : OWFLocalDesc_succSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:49:28.398704+00:00
-- url     : https://prove2.me/theorems/da3d594b-a0e6-45db-a7a7-93e4adb6d1fa
-- title:
--   Success probability on a PAC-style sampler
-- statement:
--   For a PAC-style sampler $D$, schedules $t,m$, thresholds $\theta_1,\theta_2$, a tolerance $d$ and a PPT $B$,
--   $$\Pr_{(x,y)\sim D_n,\,B}\Big[\mathrm{pSC}^{t(n)}_{\theta_1}(x,y)-d\le B(1^n,x,y)\le \mathrm{pSC}^{t(n)}_{\theta_2}(x,y)+d\Big],$$
--   for datasets of $m(n)$ points of length $n$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 5.1, p.24

import Mathlib
import Definitions.Def_OWFLocalDesc_intervalSucc
import Definitions.Def_OWFLocalDesc_datasetMass
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Success on a PAC-style sampler.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Theorem 5.1, p.24:
`Pr_{(x,y)∼D_n, B}[pSC^{t(n)}_{θ₁}(x,y) − d ≤ B(1ⁿ,x,y) ≤ pSC^{t(n)}_{θ₂}(x,y) + d]` for datasets of
`m(n)` points drawn from `D_n`. -/
noncomputable def succSampler (U : Decoder) (D : PACSampler) (t m : ℕ → ℕ) (θ₁ θ₂ : ℝ) (d : ℕ)
    (B : PPT) (n : ℕ) : ℝ :=
  ∑ x : Fin (m n) → Fin n → Bool, ∑ y : Fin (m n) → Bool,
    datasetMass D x y * intervalSucc U (t n) θ₁ θ₂ d B x y

end OWFLocalDesc


