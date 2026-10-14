-- Prove2me | Definitions.Def_AuditWhistle_Intensity_Reaction
-- name    : AuditWhistle_Intensity_Reaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:26.255521+00:00
-- url     : https://prove2.me/theorems/d46ed8a7-f29e-4c14-917a-1367bb1f5dac
-- title:
--   Appendix, proof of Proposition 2, (25), (26), (28), pp. 31–33 — reaction functions e₁(a), e₀(a, τ), the gap function V, and the thresholds r₂, a₂
-- statement:
--   Fix a model with parameters $p,\beta,R,\gamma,D,k$ and write $r=R/\gamma$, $d=D/k$, as in the proof of Proposition 2. For audit quality $a$ and intensity $\tau$ define the enforcer's reaction functions (25)–(26)
--   $$e_1(a)=\min\Big\{1,\;r\,\frac{(1-p)(1-a)\beta}{(1-p)(1-a)\beta+p(1-\beta)}\Big\},\qquad e_0(a,\tau)=r\,\frac{(1-p)(1-a)(1-\beta\tau)}{(1-p)(1-a)(1-\beta\tau)+p\,[1-(1-\beta)\tau]},$$
--   the gap function (28)
--   $$V(a)=a-(1-p)\,d\,[\beta\tau e_1(a)+(1-\beta\tau)e_0(a,\tau)],$$
--   its version on the branch $e_1=1$,
--   $$V_1(a)=a-(1-p)\,d\,[\beta\tau+(1-\beta\tau)e_0(a,\tau)],$$
--   and the thresholds of p. 33
--   $$r_2=\frac{p+\beta-2p\beta}{(1-p)\beta},\qquad a_2=\frac{\beta+\beta p(r-2)+p-\beta r}{\beta(p-1)(r-1)}.$$
--
--   The equilibrium audit quality is the root of $V$ in $(0,1)$; these functions are the objects of the proof of Proposition 2.
--
--   **Formalization Note** $e_1$ does not depend on $\tau$, because $\tau$ cancels in $\Pr(B\mid g,W_1)$. $V$ and $V_1$ take $\tau$ as their first argument after the model and $a$ as the second.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), pp. 31–33, Appendix, proof of Proposition 2, (25), (26), (28)

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting

namespace AuditWhistle.Intensity

/-- The enforcer's reaction `e₁(a)` after a tip, (25) with `r = R/γ` (τ has cancelled). -/
noncomputable def e1Of (M : Model) (a : ℝ) : ℝ :=
  min 1 (M.R / M.γ * ((1 - M.p) * (1 - a) * M.β /
    ((1 - M.p) * (1 - a) * M.β + M.p * (1 - M.β))))

/-- The enforcer's reaction `e₀(a, τ)` after silence, (26) with `r = R/γ`. -/
noncomputable def e0Of (M : Model) (τ a : ℝ) : ℝ :=
  M.R / M.γ * ((1 - M.p) * (1 - a) * (1 - M.β * τ) /
    ((1 - M.p) * (1 - a) * (1 - M.β * τ) + M.p * (1 - (1 - M.β) * τ)))

/-- The gap function `V(a)` of (28), with `d = D/k`. -/
noncomputable def V (M : Model) (τ a : ℝ) : ℝ :=
  a - (1 - M.p) * (M.D / M.k) * (M.β * τ * e1Of M a + (1 - M.β * τ) * e0Of M τ a)

/-- `V` on the branch `e₁ = 1` (p. 33). -/
noncomputable def V1 (M : Model) (τ a : ℝ) : ℝ :=
  a - (1 - M.p) * (M.D / M.k) * (M.β * τ + (1 - M.β * τ) * e0Of M τ a)

/-- The threshold `r₂` of p. 33. -/
noncomputable def r2 (p β : ℝ) : ℝ := (p + β - 2 * p * β) / ((1 - p) * β)

/-- The threshold `a₂` of p. 33. -/
noncomputable def a2 (p β r : ℝ) : ℝ :=
  (β + β * p * (r - 2) + p - β * r) / (β * (p - 1) * (r - 1))

end AuditWhistle.Intensity


