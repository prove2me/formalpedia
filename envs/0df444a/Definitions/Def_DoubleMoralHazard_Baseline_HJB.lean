-- Prove2me | Definitions.Def_DoubleMoralHazard_Baseline_HJB
-- name    : DoubleMoralHazard_Baseline_HJB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:22.688662+00:00
-- url     : https://prove2.me/theorems/a84eb50d-80e2-46e5-b378-caaf064a33ae
-- title:
--   (2.9), (2.11) corrected, (2.13), pp. 15–17, and (B.7), p. 49 — solution classes of the value-function equations and the drift Φ
-- statement:
--   Fix the parameters of the baseline model. For a function $F:\mathbb R\to\mathbb R$ (the principal's value as a function of the agent's promised utility $w$) define three solution notions, one per scenario. In each, $F$ is continuous on $[0,\infty)$, is extended beyond the tenure threshold $\bar w^i$ with slope $-1$,
--   $$F(w)=F(\bar w^i)-(w-\bar w^i)\qquad (w\ge\bar w^i),$$
--   is differentiable at every $w\in[0,\bar w^i)$ (from the right at $w=0$), satisfies $F(0)=0$, and satisfies the scenario's equation on $[0,\bar w^i)$:
--
--   1. Scenario 1, equation (2.9):
--   $$rF(w)=r\bar V+\mu p\,[F(w+R^u)-F(w)]+r(w-\bar w^1)F'(w);$$
--   2. Scenario 2, equation (2.11) in corrected form:
--   $$rF(w)=r\bar V+\mu p\,[F(w+R^u)-F(w)]+\mu(1-p)\,[F(w+\beta^o)-F(w)]+r(w-\bar w^2)F'(w);$$
--   3. Scenario 3, equation (2.13):
--   $$0=r\bar V+\mu\,[F(w+\beta)-F(w)]-rF(w)+r(w-\bar w^3)F'(w).$$
--
--   The file also defines the drift (B.7) of the verification argument: for promised utility $w$ and jump sizes $H^u,H^o$,
--   $$\Phi=\mu pR^u+\mu(1-p)R^o+F'(w)\,[rw-\mu pH^u-\mu(1-p)H^o]-rF(w)+(F(w+H^u)-F(w))\mu p+(F(w+H^o)-F(w))\mu(1-p)-c.$$
--   These are the equations whose solutions $F_1,F_2,F_3$ (Lemma 4) are the principal's value functions under the optimal contracts.
--
--   **Formalization Note** The printed (2.11) carries an extra $-rF(w)$ on its right-hand side; substituting $H^u=R^u$, $H^o=\beta^o$ into the HJB equation (2.7) and using $\mu pR^u+\mu(1-p)\beta^o=c=r\bar w^2$ gives the equation above, which is the one the proofs use. The linear extension beyond $\bar w^i$ is part of each solution notion because the equations evaluate $F$ at $w+R^u$, $w+\beta^o$, $w+\beta$, which exceed $\bar w^i$ near the threshold; the paper states the extension in Proposition 2. $F'$ is the derivative relative to $[0,\infty)$ (`derivWithin F (Ici 0)`), and differentiability is required before the equation is imposed, so a junk derivative value is never what the equation constrains. Values of $F$ at negative arguments are unconstrained.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), pp. 14–17, (2.7), (2.9), (2.11), (2.13); p. 20, Proposition 2 (extension); p. 49, (B.7)

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params

namespace DoubleMoralHazard.Baseline

open Set

/-- `F` solves the value-function equation (2.9) of Scenario 1 (p. 15) with `F(0) = 0`:
* `F` is continuous on `[0, ∞)`;
* beyond the tenure threshold `F` is extended linearly with slope `-1`,
  `F(w) = F(w̄¹) - (w - w̄¹)` for `w ≥ w̄¹` (Proposition 2, p. 20);
* at every `w ∈ [0, w̄¹)` the function is differentiable (one-sided at `0`) and
  `r F(w) = r V̄ + µ p [F(w + Rᵘ) - F(w)] + r (w - w̄¹) F'(w)`;
* `F(0) = 0`. -/
def IsSol1 (P : Params) (F : ℝ → ℝ) : Prop :=
  ContinuousOn F (Ici 0) ∧
  (∀ w, P.wbar1 ≤ w → F w = F P.wbar1 - (w - P.wbar1)) ∧
  (∀ w ∈ Ico 0 P.wbar1, DifferentiableWithinAt ℝ F (Ici 0) w ∧
    P.r * F w = P.r * P.Vbar + P.mu * P.p * (F (w + P.Ru) - F w)
      + P.r * (w - P.wbar1) * derivWithin F (Ici 0) w) ∧
  F 0 = 0

/-- `F` solves the value-function equation of Scenario 2 (p. 16) with `F(0) = 0`, in the corrected
form `r F(w) = r V̄ + µ p [F(w + Rᵘ) - F(w)] + µ (1 - p) [F(w + βᵒ) - F(w)] + r (w - w̄²) F'(w)`.
The printed (2.11) carries a stray `- r F(w)` on the right-hand side; the equation here is the
one obtained from the HJB equation (2.7) with `Hᵘ = Rᵘ`, `Hᵒ = βᵒ`, and the one used in the proofs.
Same regularity, extension beyond `w̄²` and boundary condition as `IsSol1`. -/
def IsSol2 (P : Params) (F : ℝ → ℝ) : Prop :=
  ContinuousOn F (Ici 0) ∧
  (∀ w, P.wbar2 ≤ w → F w = F P.wbar2 - (w - P.wbar2)) ∧
  (∀ w ∈ Ico 0 P.wbar2, DifferentiableWithinAt ℝ F (Ici 0) w ∧
    P.r * F w = P.r * P.Vbar + P.mu * P.p * (F (w + P.Ru) - F w)
      + P.mu * (1 - P.p) * (F (w + P.betaO) - F w)
      + P.r * (w - P.wbar2) * derivWithin F (Ici 0) w) ∧
  F 0 = 0

/-- `F` solves the value-function equation (2.13) of Scenario 3 (p. 17) with `F(0) = 0`:
`0 = r V̄ + µ [F(w + β) - F(w)] - r F(w) + r (w - w̄³) F'(w)` on `[0, w̄³)`.
Same regularity, extension beyond `w̄³` and boundary condition as `IsSol1`. -/
def IsSol3 (P : Params) (F : ℝ → ℝ) : Prop :=
  ContinuousOn F (Ici 0) ∧
  (∀ w, P.wbar3 ≤ w → F w = F P.wbar3 - (w - P.wbar3)) ∧
  (∀ w ∈ Ico 0 P.wbar3, DifferentiableWithinAt ℝ F (Ici 0) w ∧
    0 = P.r * P.Vbar + P.mu * (F (w + P.beta) - F w) - P.r * F w
      + P.r * (w - P.wbar3) * derivWithin F (Ici 0) w) ∧
  F 0 = 0

/-- The drift `Φ` of (B.7), p. 49, evaluated at promised utility `w` and jump sizes
`Hᵘ = Hu`, `Hᵒ = Ho`, with `F'` the derivative of `F` relative to `[0, ∞)`:
`Φ = µpRᵘ + µ(1-p)Rᵒ + F'(w)[r w - µ p Hᵘ - µ (1-p) Hᵒ] - r F(w)
     + (F(w + Hᵘ) - F(w)) µ p + (F(w + Hᵒ) - F(w)) µ (1 - p) - c`. -/
noncomputable def Phi (P : Params) (F : ℝ → ℝ) (w Hu Ho : ℝ) : ℝ :=
  P.mu * P.p * P.Ru + P.mu * (1 - P.p) * P.Ro
    + derivWithin F (Ici 0) w * (P.r * w - P.mu * P.p * Hu - P.mu * (1 - P.p) * Ho)
    - P.r * F w
    + (F (w + Hu) - F w) * (P.mu * P.p)
    + (F (w + Ho) - F w) * (P.mu * (1 - P.p))
    - P.c

end DoubleMoralHazard.Baseline


