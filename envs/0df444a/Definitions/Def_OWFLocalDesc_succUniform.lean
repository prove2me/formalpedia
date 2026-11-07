-- Prove2me | Definitions.Def_OWFLocalDesc_succUniform
-- name    : OWFLocalDesc_succUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:49:09.491796+00:00
-- url     : https://prove2.me/theorems/ab1f8f79-1483-4d4a-a507-cefd2ca48605
-- title:
--   Success probability on uniform data $D_{0,n}$
-- statement:
--   Let $D_{0,n}$ draw $m(n)$ independent uniform $n$-bit points and $m(n)$ independent uniform label bits. For schedules $t,m$, thresholds $\theta_1,\theta_2$, a tolerance $d$ and a PPT $B$,
--   $$\mathrm{succ}^{0}_n(B)=\Pr_{(X,Y)\sim D_{0,n},\,B}\Big[\mathrm{pSC}^{t(n)}_{\theta_1}(X,Y)-d\le B(1^n,X,Y)\le \mathrm{pSC}^{t(n)}_{\theta_2}(X,Y)+d\Big].$$
--
--   A repeated point can receive conflicting labels; then no certificate is valid, every quantile is infinite, and the heuristic succeeds only by outputting $\infty$. Such datasets are kept in the distribution.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §4.2, p.19

import Mathlib
import Definitions.Def_OWFLocalDesc_intervalSucc
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Success on uniform data `D_{0,n}`.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), §4.2, p.19: "Let
D_{0,n} draw m(n) independent uniform n-bit points and m(n) independent uniform label bits. A
repeated point can receive conflicting labels; then no certificate is valid, every quantile is
infinite, and a heuristic is permitted to output ∞."

`succUniform U t m θ₁ θ₂ d B n` is
`Pr_{(X,Y)∼D_{0,n}, B}[pSC^{t(n)}_{θ₁}(X,Y) − d ≤ B(1ⁿ,X,Y) ≤ pSC^{t(n)}_{θ₂}(X,Y) + d]`.

**Formalization Note.** Repeated points are kept (no conditioning on distinct points). -/
noncomputable def succUniform (U : Decoder) (t m : ℕ → ℕ) (θ₁ θ₂ : ℝ) (d : ℕ) (B : PPT)
    (n : ℕ) : ℝ :=
  (∑ x : Fin (m n) → Fin n → Bool, ∑ y : Fin (m n) → Bool,
      intervalSucc U (t n) θ₁ θ₂ d B x y) / (2 : ℝ) ^ (m n * n + m n)

end OWFLocalDesc


