-- Prove2me | Definitions.Def_RenewForward_PriceImpact_ClosedForms
-- name    : RenewForward_PriceImpact_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:58.782897+00:00
-- url     : https://prove2.me/theorems/c5bd33bd-102d-4dee-b037-c29a92e3392a
-- title:
--   Theorem 1 (13)–(16) and the proof of Proposition 2 — the closed forms ω, ν, a_f, b_f, f*, E[p_s], p_f and the quartic s_ps with coefficients α0, α1, α2, α4
-- statement:
--   The closed-form expressions of Theorem 1 and of the proof of Proposition 2, as real functions of the parameters $a, c, p_R, \lambda, N_R$, of six real numbers $\mu_\theta, \sigma_\theta^2, \tau_\theta, \mu_\xi, \sigma_\xi^2, \tau_\xi$ (for a given market, its moments), and of the wind capacity $k_W$. With $E[q_0] = a - c + \mu_\theta - \mu_\xi k_W$ and $E[p_0] = a + 2c + \mu_\theta - \mu_\xi k_W$:
--   $$\omega = 9E[q_0] + 2\lambda\big(2E[q_0](\sigma_\theta^2 + k_W^2\sigma_\xi^2) + (\tau_\theta - k_W^3\tau_\xi)\big) + \frac{9\lambda}{N_R}\big((E[p_0] + \mu_\theta - 3p_R)\sigma_\theta^2 + \mu_\theta k_W^2 \sigma_\xi^2 + \tau_\theta\big),$$
--   $$\nu = 45 + 8\lambda(\sigma_\theta^2 + k_W^2\sigma_\xi^2) + \frac{27\lambda}{N_R}(2\sigma_\theta^2 + k_W^2\sigma_\xi^2),$$
--   $$a_f = \frac{E[p_0]}{3} + \frac{\lambda}{9N_R}\big((E[p_0] + \mu_\theta - 3p_R)\sigma_\theta^2 + \mu_\theta k_W^2\sigma_\xi^2 + \tau_\theta\big), \qquad b_f = \frac13 + \frac{\lambda}{9N_R}(2\sigma_\theta^2 + k_W^2\sigma_\xi^2).$$
--   Further $f^* = \omega/\nu$, the closed-form expected spot price $E[p_0]/3 - 2\omega/(3\nu)$, and the closed-form forward price $a_f - 2b_f\omega/\nu$.
--
--   The quartic of the proof of Proposition 2 is $s_{p_s}(k_W) = \alpha_0 + \alpha_1 k_W + \alpha_2 k_W^2 + \alpha_4 k_W^4$ ($\alpha_3 = 0$) with
--   $$\alpha_0 = -27\mu_\xi\big(216\lambda^2(\sigma_\theta^2)^2 + 3N_R^2(45 + 8\lambda\sigma_\theta^2) + 2\lambda N_R\sigma_\theta^2(171 + 16\lambda\sigma_\theta^2)\big),$$
--   $$\begin{aligned}\alpha_1 = -12\lambda\sigma_\xi^2\big(&162\mu_\theta N_R + 108\mu_\theta N_R^2 + 36\lambda\mu_\theta N_R\sigma_\theta^2 + 729\lambda p_R\sigma_\theta^2 + 216\lambda N_R p_R\sigma_\theta^2 \\ &- 9c(12N_R^2 - 27N_R + 54\lambda\sigma_\theta^2 + 28\lambda N_R\sigma_\theta^2) + 9a(12N_R^2 - 27N_R - 27\lambda\sigma_\theta^2 + 4\lambda N_R\sigma_\theta^2) \\ &- \lambda\tau_\theta(243 + 126N_R + 16N_R^2)\big),\end{aligned}$$
--   $$\alpha_2 = 18\lambda\big(18\mu_\xi N_R(2N_R - 27)\sigma_\xi^2 - 3\lambda\mu_\xi(189 + 20N_R)\sigma_\theta^2\sigma_\xi^2 + 90N_R^2\tau_\xi + 4\lambda N_R(27 + 4N_R)\sigma_\theta^2\tau_\xi\big),$$
--   $$\alpha_4 = 3\lambda^2(27 + 8N_R)\sigma_\xi^2(4N_R\tau_\xi - 27\mu_\xi\sigma_\xi^2).$$
--
--   These expressions are used only in the conclusions of the milestones (Theorem 1 and the steps of the proof of Proposition 2), never in the definition of the equilibrium.
--
--   **Formalization Note.** $E[q_0]$ and $E[p_0]$ are written out by linearity. In $\alpha_1$ the term $-\lambda\tau_\theta(243 + 126N_R + 16N_R^2)$ is placed inside the factor $-12\lambda\sigma_\xi^2(\cdots)$; the page prints it outside, with an unmatched parenthesis, and only the inside placement agrees with the derivative of the closed form (checked symbolically). The moments of a given $(\theta, \xi)$ are packaged by `momentsOf`, with central third moments.
-- source:
--   Peura & Bunn, Renewable power and electricity prices: The impact of forward markets, author-accepted manuscript, LBS Research Online eprint 1432 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3710), p. 14, Theorem 1 (11)–(16); p. 37, proof of Proposition 2

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting

namespace RenewForward.PriceImpact

open MeasureTheory ProbabilityTheory

/-- Six real numbers standing for the moments `µ_θ, σ²_θ, τ_θ, µ_ξ, σ²_ξ, τ_ξ`. The closed forms below are
plain real expressions in these numbers; `momentsOf` plugs in the moments of a given pair `(θ, ξ)`. -/
structure Moments where
  muT : ℝ
  s2T : ℝ
  tauT : ℝ
  muX : ℝ
  s2X : ℝ
  tauX : ℝ

/-- The moments of `(θ, ξ)` under `P` (the third moments are central). -/
noncomputable def momentsOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ ξ : Ω → ℝ) : Moments :=
  ⟨muTheta P θ, sig2Theta P θ, tauTheta P θ, muXi P ξ, sig2Xi P ξ, tauXi P ξ⟩

/-- `E[q0] = a − c + µ_θ − µ_ξ k_W`, written out. -/
def meanQ0 (M : Params) (m : Moments) (kW : ℝ) : ℝ := M.a - M.c + m.muT - m.muX * kW

/-- `E[p0] = a + 2c + µ_θ − µ_ξ k_W`, written out. -/
def meanP0 (M : Params) (m : Moments) (kW : ℝ) : ℝ := M.a + 2 * M.c + m.muT - m.muX * kW

/-- `ω`, display (13). -/
noncomputable def omegaFwd (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  9 * meanQ0 M m kW
    + 2 * M.lam * (2 * meanQ0 M m kW * (m.s2T + kW ^ 2 * m.s2X) + (m.tauT - kW ^ 3 * m.tauX))
    + 9 * M.lam / M.NR *
      ((meanP0 M m kW + m.muT - 3 * M.pR) * m.s2T + m.muT * kW ^ 2 * m.s2X + m.tauT)

/-- `ν`, display (14). -/
noncomputable def nuFwd (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  45 + 8 * M.lam * (m.s2T + kW ^ 2 * m.s2X) + 27 * M.lam / M.NR * (2 * m.s2T + kW ^ 2 * m.s2X)

/-- `a_f`, display (15). -/
noncomputable def aF (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  meanP0 M m kW / 3
    + M.lam / (9 * M.NR) *
      ((meanP0 M m kW + m.muT - 3 * M.pR) * m.s2T + m.muT * kW ^ 2 * m.s2X + m.tauT)

/-- `b_f`, display (16). -/
noncomputable def bF (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  1 / 3 + M.lam / (9 * M.NR) * (2 * m.s2T + kW ^ 2 * m.s2X)

/-- The closed-form forward position of each producer, (11): `f*_Pi = ω/ν`. -/
noncomputable def fStar (M : Params) (m : Moments) (kW : ℝ) : ℝ := omegaFwd M m kW / nuFwd M m kW

/-- The closed-form expected spot price of (12): `E[p0]/3 − 2ω/(3ν)`, as a function of `k_W`. -/
noncomputable def expSpotClosed (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  meanP0 M m kW / 3 - 2 * omegaFwd M m kW / (3 * nuFwd M m kW)

/-- The closed-form forward price of (12): `a_f − 2 b_f ω/ν`, as a function of `k_W`. -/
noncomputable def fwdPriceClosed (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  aF M m kW - 2 * bF M m kW * omegaFwd M m kW / nuFwd M m kW

/-- `α0` (proof of Proposition 2, p. 37). -/
def alpha0 (M : Params) (m : Moments) : ℝ :=
  -27 * m.muX * (216 * M.lam ^ 2 * m.s2T ^ 2 + 3 * (M.NR : ℝ) ^ 2 * (45 + 8 * M.lam * m.s2T)
    + 2 * M.lam * M.NR * m.s2T * (171 + 16 * M.lam * m.s2T))

/-- `α1` (proof of Proposition 2, p. 37), with the printed slip corrected: the term
`− λ τ_θ (243 + 126 N_R + 16 N_R²)` lies inside the factor `−12 λ σ²_ξ (…)`. -/
def alpha1 (M : Params) (m : Moments) : ℝ :=
  -12 * M.lam * m.s2X * (162 * m.muT * M.NR + 108 * m.muT * (M.NR : ℝ) ^ 2
    + 36 * M.lam * m.muT * M.NR * m.s2T + 729 * M.lam * M.pR * m.s2T
    + 216 * M.lam * M.NR * M.pR * m.s2T
    - 9 * M.c * (12 * (M.NR : ℝ) ^ 2 - 27 * M.NR + 54 * M.lam * m.s2T + 28 * M.lam * M.NR * m.s2T)
    + 9 * M.a * (12 * (M.NR : ℝ) ^ 2 - 27 * M.NR - 27 * M.lam * m.s2T + 4 * M.lam * M.NR * m.s2T)
    - M.lam * m.tauT * (243 + 126 * M.NR + 16 * (M.NR : ℝ) ^ 2))

/-- `α2` (proof of Proposition 2, p. 37). -/
def alpha2 (M : Params) (m : Moments) : ℝ :=
  18 * M.lam * (18 * m.muX * M.NR * (2 * M.NR - 27) * m.s2X
    - 3 * M.lam * m.muX * (189 + 20 * M.NR) * m.s2T * m.s2X
    + 90 * (M.NR : ℝ) ^ 2 * m.tauX + 4 * M.lam * M.NR * (27 + 4 * M.NR) * m.s2T * m.tauX)

/-- `α4` (proof of Proposition 2, p. 37). (`α3 = 0`.) -/
def alpha4 (M : Params) (m : Moments) : ℝ :=
  3 * M.lam ^ 2 * (27 + 8 * M.NR) * m.s2X * (4 * M.NR * m.tauX - 27 * m.muX * m.s2X)

/-- The quartic `s_ps(k_W) = α0 + α1 k_W + α2 k_W² + α3 k_W³ + α4 k_W⁴` with `α3 = 0`. -/
def spsPoly (M : Params) (m : Moments) (kW : ℝ) : ℝ :=
  alpha0 M m + alpha1 M m * kW + alpha2 M m * kW ^ 2 + alpha4 M m * kW ^ 4

end RenewForward.PriceImpact


