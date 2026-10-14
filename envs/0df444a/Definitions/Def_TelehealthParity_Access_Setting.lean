-- Prove2me | Definitions.Def_TelehealthParity_Access_Setting
-- name    : TelehealthParity_Access_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:29.886465+00:00
-- url     : https://prove2.me/theorems/0e896b3f-3066-46f0-b905-b4119fb97dff
-- title:
--   §3–§5.1, pp. 7–17 — parameters, κ(q), θ^T, θ^O, θ̄, θ*, the equilibrium proportions, A and F
-- statement:
--   This definition fixes the large-market model of Çakıcı and Mills: one healthcare provider, a population of strategic patients, and the closed-form equilibrium proportions on which every result of the mission is stated.
--
--   **Parameters.** A patient whose acute-care episode is resolved receives the value $V$. Waiting costs $h$ per unit of sojourn time; the co-payments are $c_O$ for an office visit and $c_T$ for a telehealth visit, and an office visit carries an expected inconvenience cost $\tau$. Episodes arrive at rate $\lambda$. The provider serves at total rate $\mu$ and devotes the fraction $\theta\in[0,1]$ of its capacity, the *telehealth commitment*, to telehealth. With probability $q$ a telehealth visit requires a duplicate office visit. An office visit earns the provider the expected revenue $R$; a telehealth visit earns the reimbursement $r$ plus $qR$ for the expected duplicate visit.
--
--   **Standing assumptions** (those not involving $q$): $V,c_T,c_O,\tau,h,\mu,\lambda>0$, $R\ge 0$, and
--   $$V>\frac{h}{\mu}+c_O+\tau \quad (2),\qquad\qquad c_T<c_O+\tau \quad (3).$$
--
--   **Closed forms.** For a duplicate-visit probability $q$,
--   $$\kappa(q)=\frac{h/\mu}{V-c_T-q(c_O+\tau)},\qquad \theta^T=\frac{h}{\mu}\cdot\frac{1}{(1-q)V-c_T},\qquad \theta^O=\frac{1}{1+q}+\frac{h}{(1+q)\mu}\left(\frac{q}{(1-q)V-c_T}-\frac{1}{V-c_O-\tau}\right),$$
--   $$\bar\theta=\frac12\left(1+\kappa(q)(1-q)+\sqrt{\bigl(1-\kappa(q)(1-q)\bigr)^2-4q\kappa(q)}\right),\qquad \theta^*=\frac{1-\kappa(q)(1-q)\sqrt q}{1+q}.$$
--
--   **Equilibrium proportions.** The proportions $\pi^O(\theta)$ (office) and $\pi^T(\theta)$ (telehealth) of arriving patients are, region by region (Figure 3 of the paper):
--
--   1. on $\theta\le\theta^T$ (balk/office, BO): $\pi^O=\dfrac{(1-\theta)\mu}{\lambda}-\dfrac{h}{(V-c_O-\tau)\lambda}$, $\pi^T=0$ (eq. (15));
--   2. on $\theta^T<\theta<\theta^O$ (balk/office/telehealth, BOT): $\pi^O=\dfrac{\mu}{\lambda}-\dfrac{(1+q)\theta\mu}{\lambda}+\dfrac{h}{\lambda}\left(\dfrac{q}{(1-q)V-c_T}-\dfrac{1}{V-c_O-\tau}\right)$ and $\pi^T=\dfrac{\theta\mu}{\lambda}-\dfrac{h}{\lambda}\cdot\dfrac{1}{(1-q)V-c_T}$ (eqs. (9)–(10));
--   3. on $\theta^O\le\theta<\bar\theta$ (balk/telehealth, BT): $\pi^O=0$ and $\pi^T=\dfrac{\mu}{\lambda}\left[\dfrac{1-\theta(1-q)}{2q}-\kappa(q)-\sqrt{\kappa(q)^2+\left(\dfrac{1-\theta(1+q)}{2q}\right)^2}\,\right]$ (eq. (18));
--   4. on $\theta\ge\bar\theta$ (all balk, B): $\pi^O=\pi^T=0$.
--
--   The balking proportion is $\pi^B=1-\pi^O-\pi^T$. The patient access rate and the provider's revenue rate are
--   $$A(\theta)=\bigl(\pi^O(\theta)+\pi^T(\theta)\bigr)\lambda \quad (22),\qquad F(r,\theta)=\bigl(R\pi^O(\theta)+(r+Rq)\pi^T(\theta)\bigr)\lambda \quad (23).$$
--
--   **Large market and admissible $q$.** The provider is in the *large-market setting* at $q$ when some patients balk for every commitment: $A(\theta)<\lambda$ for all $\theta\in[0,1]$. A duplicate-visit probability $q$ is *admissible* when
--   1. $0<q<1$;
--   2. assumption (6) holds: $0<\kappa(q)\le 1/(1+\sqrt q)^2$;
--   3. $(1-q)V-c_T>0$;
--   4. $\dfrac{h}{\mu}\left(\dfrac{1}{(1-q)V-c_T}+\dfrac{1}{V-c_O-\tau}\right)<1$ (the condition of Lemma 2, under which $0<\theta^T<\theta^O<1$);
--   5. the large-market setting holds at $q$.
--
--   These objects carry the whole analysis of the paper's §4.1 and §5.1: the equilibrium characterization, the shape of $A$ and $F$ in $\theta$, and the duplicate-visit thresholds of Propositions 3–5.
--
--   **Formalization Note** The parameters form a structure `Params` with the arrival rate named `lam` (`λ` is a Lean keyword); $q$, $r$ and $\theta$ are separate arguments. $\theta^*$ is the closed form (24), not an argmax, and no threshold in $q$ is defined here. The four regions are assigned exactly as in the paper: $[0,\theta^T]$, $(\theta^T,\theta^O)$, $[\theta^O,\bar\theta)$, $[\bar\theta,1]$. The large-market setting is stated verbally on p. 12 ("for every θ at least some patients balk"); it is encoded as $\pi^B(\theta)>0$ for the closed-form proportions. Hypothesis 3 of admissibility is not printed in the paper; the proof of Lemma 2 presumes it ("θ^T and θ^O are well defined and nonnegative as long as q < 1"), and without it Lemma 2 fails. Every denominator above is positive for admissible $q$ under (2), so Lean's convention $x/0=0$ is never reached; the discriminant under the root in $\bar\theta$ is nonnegative by (6) (Lemma 3).
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), pp. 7–17, §3 (display (1), p. 9; (2), p. 11; (3), p. 12), §4.1 ((6), p. 13; (8)–(12), p. 14; (14)–(15), p. 14; (17)–(19), p. 15), §5.1 ((22)–(24), pp. 16–17)

import Mathlib

namespace TelehealthParity.Access

/-- The model parameters of Çakıcı–Mills §3 (pp. 8–11): the patient's value `V` of a resolved
episode, the co-payments `cT` (telehealth) and `cO` (office), the office inconvenience cost `τ`,
the holding cost `h` per unit of sojourn time, the provider's service rate `μ`, the arrival rate
`lam` of episodes (the paper's `λ`, a Lean keyword), and the expected revenue `R` of an office visit.
The duplicate-visit probability `q`, the telehealth commitment `θ` and the telehealth
reimbursement `r` are separate arguments, because the paper varies them. -/
structure Params where
  V : ℝ
  cT : ℝ
  cO : ℝ
  τ : ℝ
  h : ℝ
  μ : ℝ
  lam : ℝ
  R : ℝ

/-- The standing assumptions of §3–§4 that do not involve `q`: positivity of `V, h, cO, cT, τ, μ, λ`
(pp. 8–10), `R ≥ 0` (p. 11), assumption (2) `V > h/μ + cO + τ` (p. 11) and assumption (3)
`cT < cO + τ` (p. 12). -/
def Params.Standing (p : Params) : Prop :=
  0 < p.V ∧ 0 < p.cT ∧ 0 < p.cO ∧ 0 < p.τ ∧ 0 < p.h ∧ 0 < p.μ ∧ 0 < p.lam ∧ 0 ≤ p.R ∧
    p.h / p.μ + p.cO + p.τ < p.V ∧ p.cT < p.cO + p.τ

/-- `κ(q) = (h/μ) / (V − cT − q(cO + τ))`, p. 13. -/
noncomputable def kappa (p : Params) (q : ℝ) : ℝ :=
  (p.h / p.μ) / (p.V - p.cT - q * (p.cO + p.τ))

/-- `θ^T = (h/μ) · 1/((1 − q)V − cT)`, eq. (11), p. 14. -/
noncomputable def thetaT (p : Params) (q : ℝ) : ℝ :=
  p.h / p.μ * (1 / ((1 - q) * p.V - p.cT))

/-- `θ^O = 1/(1 + q) + h/((1 + q)μ) · (q/((1 − q)V − cT) − 1/(V − cO − τ))`, eq. (12), p. 14. -/
noncomputable def thetaO (p : Params) (q : ℝ) : ℝ :=
  1 / (1 + q) + p.h / ((1 + q) * p.μ) * (q / ((1 - q) * p.V - p.cT) - 1 / (p.V - p.cO - p.τ))

/-- `θ̄ = ½ (1 + κ(q)(1 − q) + √((1 − κ(q)(1 − q))² − 4qκ(q)))`, eq. (19), p. 15. -/
noncomputable def thetaBar (p : Params) (q : ℝ) : ℝ :=
  (1 + kappa p q * (1 - q) +
      Real.sqrt ((1 - kappa p q * (1 - q)) ^ 2 - 4 * q * kappa p q)) / 2

/-- `θ* = (1 − κ(q)(1 − q)√q) / (1 + q)`, eq. (24), p. 17: the closed form, not an argmax. -/
noncomputable def thetaStar (p : Params) (q : ℝ) : ℝ :=
  (1 - kappa p q * (1 - q) * Real.sqrt q) / (1 + q)

/-- The large-market equilibrium joining proportions `(π^O(θ), π^T(θ))` of §4.1, by region
(Figure 3, p. 13):
* `θ ≤ θ^T` (BO): `π^O` of eq. (15), `π^T = 0`;
* `θ^T < θ < θ^O` (BOT): eqs. (9) and (10);
* `θ^O ≤ θ < θ̄` (BT): `π^O = 0`, `π^T` of eq. (18);
* `θ̄ ≤ θ` (B): `(0, 0)`.
The balking proportion is `π^B = 1 − π^O − π^T` ((8), (14), (17)). -/
noncomputable def eqProp (p : Params) (q θ : ℝ) : ℝ × ℝ :=
  if θ ≤ thetaT p q then
    ((1 - θ) * p.μ / p.lam - p.h / ((p.V - p.cO - p.τ) * p.lam), 0)
  else if θ < thetaO p q then
    (p.μ / p.lam - (1 + q) * θ * p.μ / p.lam +
        p.h / p.lam * (q / ((1 - q) * p.V - p.cT) - 1 / (p.V - p.cO - p.τ)),
      θ * p.μ / p.lam - p.h / p.lam * (1 / ((1 - q) * p.V - p.cT)))
  else if θ < thetaBar p q then
    (0, p.μ / p.lam * ((1 - θ * (1 - q)) / (2 * q) - kappa p q -
        Real.sqrt (kappa p q ^ 2 + ((1 - θ * (1 + q)) / (2 * q)) ^ 2)))
  else (0, 0)

/-- The patient access rate `A(θ) = (π^O(θ) + π^T(θ))λ`, eq. (22), p. 16. -/
noncomputable def access (p : Params) (q θ : ℝ) : ℝ :=
  ((eqProp p q θ).1 + (eqProp p q θ).2) * p.lam

/-- The provider's revenue rate `F(r, θ) = (Rπ^O(θ) + (r + Rq)π^T(θ))λ`, eq. (23), p. 16. -/
noncomputable def revenue (p : Params) (q r θ : ℝ) : ℝ :=
  (p.R * (eqProp p q θ).1 + (r + p.R * q) * (eqProp p q θ).2) * p.lam

/-- The large-market setting (p. 12: "for every θ at least some patients balk"): the balking
proportion `π^B(θ) = 1 − π^O(θ) − π^T(θ)` is positive for every `θ ∈ [0, 1]`, i.e. `A(θ) < λ`. -/
def LargeMarket (p : Params) (q : ℝ) : Prop :=
  ∀ θ ∈ Set.Icc (0 : ℝ) 1, access p q θ < p.lam

/-- The assumptions of §4.1–§5.1 at the duplicate-visit probability `q`: `0 < q < 1`;
assumption (6) `0 < κ(q) ≤ 1/(1 + √q)²` (p. 13); `(1 − q)V − cT > 0` (presumed by the proof of
Lemma 2, disclosed); Lemma 2's ordering condition `(h/μ)(1/((1 − q)V − cT) + 1/(V − cO − τ)) < 1`
(p. 14, the region structure of Figure 3); and the large-market setting. -/
def Admissible (p : Params) (q : ℝ) : Prop :=
  0 < q ∧ q < 1 ∧ 0 < kappa p q ∧ kappa p q ≤ 1 / (1 + Real.sqrt q) ^ 2 ∧
    0 < (1 - q) * p.V - p.cT ∧
    p.h / p.μ * (1 / ((1 - q) * p.V - p.cT) + 1 / (p.V - p.cO - p.τ)) < 1 ∧
    LargeMarket p q

end TelehealthParity.Access


