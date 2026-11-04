-- Prove2me | Definitions.Def_ChurnServiceMode_optPolicy
-- name    : ChurnServiceMode_optPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:50.390193+00:00
-- url     : https://prove2.me/theorems/5988670a-256b-4775-aa2e-f47658db2d15
-- title:
--   Thresholds $\theta_b$, $\theta_G$ (Lemmas 2–3, corrected (11)) and the policy of Theorem 1
-- statement:
--   Write $\hat q=(q-\mu_R)/\sigma_R$ and $\hat\theta=(\theta-\mu_R)/\sigma_R$.
--
--   1. The **Lemma 2 equation** is
--   $$\frac{\mu_R\sqrt\pi(\mu_S-\theta)}{\sigma_R}\,e^{\hat\theta^2}\bigl(1-\operatorname{erf}(\hat\theta)\bigr)+\mu_S=0 .$$
--   $\theta_b=+\infty$ if $\mu_R\le\mu_S$; if $\mu_R>\mu_S$, $\theta_b$ is a root of this equation in $(\mu_S,\infty)$.
--
--   2. The **corrected display (11)** is
--   $$e^{\hat q^2}\frac{\sqrt\pi(\theta-\mu_R)(q-\mu_R)}{\sigma_R^2}\bigl(\operatorname{erf}(\hat\theta)-\operatorname{erf}(\hat q)\bigr)+e^{\hat q^2-\hat\theta^2}\hat q-\hat\theta-\frac{\mu_S\sigma_R}{2(\mu_S-\mu_R)(q-\mu_S)}=0,$$
--   and display (12), exactly as printed, is
--   $$2e^{\hat q^2-\hat\theta^2}\Bigl(1+\frac{(\theta-\mu_S)(\theta-\mu_R)}{\sigma_R^2}\Bigr)+e^{\hat q^2}\sqrt\pi\,k(\theta)\bigl(\operatorname{erf}(\hat q)-\operatorname{erf}(\hat\theta)\bigr)+k(\theta)\frac{\sigma_R}{q-\mu_R}-\frac{\mu_S\bigl(\sigma_R^2+(\mu_S-\mu_R)(\theta-\mu_S)\bigr)}{(\mu_S-\mu_R)(q-\mu_R)(q-\mu_S)}=0,$$
--   with $k(\theta)=\frac{\mu_S+2\mu_R-3\theta}{\sigma_R}+\frac{2(\theta-\mu_R)^2(\mu_S-\theta)}{\sigma_R^3}$. $\theta_G=-\infty$ if $\mu_R\ge\mu_S$; if $\mu_R<\mu_S$, $\theta_G$ is an element of
--   $$\bigl(\Theta^{\rm big}_G\cap(\mu_S-\tfrac{\sigma_R^2}{\mu_S-\mu_R},\mu_S)\bigr)\cup\bigl(\Theta^{\rm small}_G\cap[\mu_S,q)\bigr),$$
--   $\Theta^{\rm big}_G$ and $\Theta^{\rm small}_G$ being the root sets of (12) and of the corrected (11).
--
--   3. The **policy of Theorem 1** is Safe on $[q,\theta_b]$, Risky on $(\theta_G,q)$, and the superior mode (Risky if $\mu_R>\mu_S$, Safe if $\mu_R<\mu_S$) elsewhere.
--
--   These thresholds and this policy are the content of the mission's goal.
--
--   **Formalization Note** $\theta_b,\theta_G$ are extended reals (`EReal`), so that $\pm\infty$ are representable; the comparisons of the policy are in `EReal`. Display (11) is used with the sign of the erf difference corrected, as in $F_{\rm small}$ of the proof of Lemma 3 (p.24): as printed, Lemma 3 fails (two elements at $(\mu_S,\mu_R,\sigma_R,q)=(5,1,3,6)$). When $\mu_R=\mu_S$ the "elsewhere" set is empty (footnote 11) and the Lean choice there is never used.
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 2, p.9; Lemma 3 with displays (11)–(12), pp.9–10 (and F_small, p.24); Theorem 1 and footnote 11, p.10

import Mathlib
import Definitions.Def_ChurnServiceMode_Params

open PSOutsourcing.PartialObs (erf)

namespace ChurnServiceMode

/-- Left-hand side of the equation of **Lemma 2** (p.9):
`μR √π (μS − θ)/σR · exp((θ − μR)²/σR²) · (1 − erf((θ − μR)/σR)) + μS`. -/
noncomputable def lemma2Fn (p : Params) (θ : ℝ) : ℝ :=
  p.μR * Real.sqrt Real.pi * (p.μS - θ) / p.σR * Real.exp ((θ - p.μR) ^ 2 / p.σR ^ 2)
    * (1 - erf ((θ - p.μR) / p.σR)) + p.μS

/-- Left-hand side of display **(11)** of Lemma 3 (p.9), **corrected** (Correction C1): the erf
difference is `erf((θ − μR)/σR) − erf((q − μR)/σR)`, as in `F_small` of the proof of Lemma 3
(p.24), not the printed `erf((q − μR)/σR) − erf((θ − μR)/σR)`:

`exp((q−μR)²/σR²) · √π(θ−μR)(q−μR)/σR² · (erf((θ−μR)/σR) − erf((q−μR)/σR))
 + exp(((q−μR)² − (θ−μR)²)/σR²) · (q−μR)/σR − (θ−μR)/σR − μS σR/(2(μS−μR)(q−μS))`.

**Formalization Note.** Only used when `μR < μS < q`, where the last denominator is nonzero. -/
noncomputable def smallFn (p : Params) (θ : ℝ) : ℝ :=
  Real.exp ((p.q - p.μR) ^ 2 / p.σR ^ 2) * (Real.sqrt Real.pi * (θ - p.μR) * (p.q - p.μR) / p.σR ^ 2)
      * (erf ((θ - p.μR) / p.σR) - erf ((p.q - p.μR) / p.σR))
    + Real.exp (((p.q - p.μR) ^ 2 - (θ - p.μR) ^ 2) / p.σR ^ 2) * ((p.q - p.μR) / p.σR)
    - (θ - p.μR) / p.σR
    - p.μS * p.σR / (2 * (p.μS - p.μR) * (p.q - p.μS))

/-- Left-hand side of display **(12)** of Lemma 3 (p.9), exactly as printed:

`2 exp(((q−μR)² − (θ−μR)²)/σR²) (1 + (θ−μS)(θ−μR)/σR²)
 + exp((q−μR)²/σR²) √π ((μS+2μR−3θ)/σR + 2(θ−μR)²(μS−θ)/σR³) (erf((q−μR)/σR) − erf((θ−μR)/σR))
 + ((μS+2μR−3θ)/σR + 2(θ−μR)²(μS−θ)/σR³) σR/(q−μR)
 − μS(σR² + (μS−μR)(θ−μS)) / ((μS−μR)(q−μR)(q−μS))`.

**Formalization Note.** Only used when `μR < μS < q`, where every denominator is nonzero. -/
noncomputable def bigFn (p : Params) (θ : ℝ) : ℝ :=
  let k := (p.μS + 2 * p.μR - 3 * θ) / p.σR + 2 * (θ - p.μR) ^ 2 * (p.μS - θ) / p.σR ^ 3
  2 * Real.exp (((p.q - p.μR) ^ 2 - (θ - p.μR) ^ 2) / p.σR ^ 2)
      * (1 + (θ - p.μS) * (θ - p.μR) / p.σR ^ 2)
    + Real.exp ((p.q - p.μR) ^ 2 / p.σR ^ 2) * Real.sqrt Real.pi * k
      * (erf ((p.q - p.μR) / p.σR) - erf ((θ - p.μR) / p.σR))
    + k * (p.σR / (p.q - p.μR))
    - p.μS * (p.σR ^ 2 + (p.μS - p.μR) * (θ - p.μS))
      / ((p.μS - p.μR) * (p.q - p.μR) * (p.q - p.μS))

/-- `θb` **is the threshold of Lemma 2** (p.9): `θb = +∞` if `μR ≤ μS`; if `μR > μS`, `θb` is a
real root of `lemma2Fn` in `(μS, ∞)` (Lemma 2 says there is exactly one).

**Formalization Note.** `θb : EReal` so that `θb = +∞` is representable. -/
def IsThetaB (p : Params) (θb : EReal) : Prop :=
  (p.μR ≤ p.μS ∧ θb = ⊤) ∨
    (p.μS < p.μR ∧ ∃ θ : ℝ, θb = (θ : EReal) ∧ p.μS < θ ∧ lemma2Fn p θ = 0)

/-- `θG` **is the threshold of Lemma 3** (pp.9–10): `θG = −∞` if `μR ≥ μS`; if `μR < μS`, `θG` is
an element of `(Θ^big_G ∩ (μS − σR²/(μS−μR), μS)) ∪ (Θ^small_G ∩ [μS, q))`, where `Θ^big_G` is the
root set of (12) and `Θ^small_G` the root set of the corrected (11) (Lemma 3 says there is exactly
one such element).

**Formalization Note.** `θG : EReal` so that `θG = −∞` is representable. `Θ^small_G` uses the
corrected display (11), `smallFn` (Correction C1). -/
def IsThetaG (p : Params) (θG : EReal) : Prop :=
  (p.μS ≤ p.μR ∧ θG = ⊥) ∨
    (p.μR < p.μS ∧ ∃ θ : ℝ, θG = (θ : EReal) ∧
      ((θ ∈ Set.Ioo (p.μS - p.σR ^ 2 / (p.μS - p.μR)) p.μS ∧ bigFn p θ = 0) ∨
        (θ ∈ Set.Ico p.μS p.q ∧ smallFn p θ = 0)))

/-- **The policy of Theorem 1** (p.10): Safe on `[q, θb]`, Risky on `(θG, q)`, and the superior of
the two modes elsewhere (Risky if `μR > μS`, Safe if `μR < μS`).

**Formalization Note.** The comparisons with `θb, θG` are in `EReal`. When `μR = μS` the
"elsewhere" set is empty (footnote 11: `θG = −∞`, `θb = +∞`), so the choice made there
(Safe) is never used. -/
noncomputable def optPolicy (p : Params) (θb θG : EReal) (x : ℝ) : Mode :=
  if p.q ≤ x ∧ (x : EReal) ≤ θb then Mode.S
  else if θG < (x : EReal) ∧ x < p.q then Mode.R
  else if p.μS < p.μR then Mode.R else Mode.S

end ChurnServiceMode


