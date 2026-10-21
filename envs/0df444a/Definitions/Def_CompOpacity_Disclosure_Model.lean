-- Prove2me | Definitions.Def_CompOpacity_Disclosure_Model
-- name    : CompOpacity_Disclosure_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:55.703297+00:00
-- url     : https://prove2.me/theorems/392f49e1-bd67-4df6-91a5-3151e70a580a
-- title:
--   §2.1, (1)–(4), (9), (25)–(28), (52)–(53), pp. 6–10, 32, 37 — two-FI disclosure game: Gaussian signals, linear investor equilibrium, FI payoff, disclosure equilibrium, L
-- statement:
--   The model of Zhang, *Competition and Opacity in the Financial System* (§2.1).
--
--   Two financial institutions (FIs) $i \in \{1,2\}$ raise funds from a continuum of risk-neutral investors. FI $i$'s project has fundamentals $\theta_i \sim N(\bar\theta, 1/q)$, independent across $i$, with $\bar\theta > 0$ and prior precision $q > 0$, and return
--   $$R_i = 2(\theta_i + aK_i),$$
--   where $K_i$ is the aggregate investment in FI $i$ and $a \in [0, \tfrac12]$ is the FI's exposure to rollover risk. Before learning $\theta_i$, FI $i$ commits to the precision $m_i \ge 0$ of a public report $z_i = \theta_i + \varepsilon_i$, $\varepsilon_i \sim N(0, 1/m_i)$, at cost $\tfrac{c_m}{2} m_i^2$. Each investor $j$ also observes private signals $x_{ij} = \theta_i + \eta_{ij}$ of precision $n > 0$.
--
--   The objects defined are:
--   1. the posterior mean $E_j[\theta_i] = \dfrac{m_i z_i + n x_{ij} + q\bar\theta}{m_i + n + q}$ of (27)–(28);
--   2. linear strategies $k_{ij} = \beta_i x_{ij} + \gamma_i z_i - b(\lambda_i x_{-ij} + \omega_i z_{-i}) + h_i$ of (17)/(25), where $b \in [0,1]$ is the intensity of competition;
--   3. investor $j$'s expectation of the aggregate investment, (27), and the **linear equilibrium** condition: for all signal realizations and both FIs,
--   $$k_{ij} = E_j[\theta_i] + aE_j[K_i] - b\big(E_j[\theta_{-i}] + aE_j[K_{-i}]\big),$$
--   which is the investment rule (4), $k_{ij} = E_j[R_i/2] - bE_j[R_{-i}/2]$, in the form (28);
--   4. the aggregate investment $K_i = \beta_i\theta_i + \gamma_i z_i - b(\omega_i z_{-i} + \lambda_i\theta_{-i}) + h_i$ of (26);
--   5. the joint Gaussian law of $(\theta_1,\theta_2,\varepsilon_1,\varepsilon_2)$;
--   6. FI $i$'s payoff (9) net of its disclosure cost,
--   $$\Pi_i = E\Big[\frac{R_i}{2}K_i - \frac12 K_i^2\Big] - \frac{c_m}{2}m_i^2,$$
--   evaluated at a linear equilibrium of the investors' game;
--   7. a **disclosure equilibrium**: precisions $m_1, m_2 \ge 0$ such that each $m_i$ maximizes $\Pi_i$ over all $m_i' \ge 0$ given $m_{-i}$;
--   8. the quartic $L(x) = A_0 + A_1x + A_2x^2 + A_3x^3 + A_4x^4$ of (52)–(53), with $A_0 = a^2$, $A_1 = 3a^2(2-3a)$, $A_2 = -3a(2-3a)[1-5(1-a)a]$, $A_3 = -a[12 + a(-82 + a(206 + a(-226 + 91a)))]$, $A_4 = -(1-a)a(1-2a)[6 - a(30 - a(52 - 31a))]$;
--   9. the gross marginal payoffs, the first terms of (33) and (44):
--   $$\frac{m + q - (1-a)(1-4a)n}{2(1-a)^2[q+m+(1-a)n]^3}, \qquad \frac{m + q - (1-2a)n}{2(1-2a)[q+m+(1-2a)n]^3}.$$
--
--   These definitions carry every statement of the mission: the investor equilibrium (Lemma 1, Proposition 3), the FIs' marginal payoffs ((33), (44)), the disclosure equilibria (Proposition 2, (46)–(47)) and the comparison of Proposition 4.
--
--   **Formalization Note** FIs are indexed by `Fin 2` (the paper's FI 1 is `0`) and the other FI of `i` is `i.rev`. The paper's $E_j$ is taken to be the posterior-mean formula (27)–(28), which is the Gaussian conditional expectation; in the terms about FI $-i$ the investor's signal is $x_{-ij}$ (the page prints $x_{ij}$ in (25), (27), (28), while (17), (26) and the information set use $x_{-ij}$). Mathlib's `gaussianReal μ v` takes the variance, so precision $q$ is variance $q^{-1}$; at $m_i = 0$ the noise law is the point mass at $0$. The payoff uses a linear equilibrium chosen by `Classical.epsilon`; at $b = 0$ the coefficients $\lambda_i, \omega_i$ are not determined but are multiplied by $b = 0$ and do not enter the payoff. Uniqueness among non-linear investor strategies (footnote 10) is not modelled.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), pp. 6–10, 32, 33, 36, 37, §2.1, (1)–(4), (9), (25)–(28), (33), (44), (52)–(53)

import Mathlib

namespace CompOpacity.Disclosure

open MeasureTheory ProbabilityTheory

/-! Zhang, *Competition and Opacity in the Financial System*, SSRN 3428683 (2019-09-07 posting),
§2.1 (pp. 6–10) and Appendix II (pp. 32–37).

Two financial institutions (FIs), indexed by `Fin 2` (the paper's FI 1 is `0`, FI 2 is `1`); the
other FI of `i` is `i.rev`. Parameters: rollover-risk exposure `a`, competition intensity `b`, prior
precision `q`, private-signal precision `n`, prior mean `thetaBar`, disclosure cost `cm`, and the
disclosure precisions `m : Fin 2 → ℝ`. -/

/-- Investor `j`'s posterior mean of `θᵢ` given the public signal `zᵢ` (precision `mᵢ`) and the
private signal `xᵢⱼ` (precision `n`) under the prior `N(θ̄, 1/q)`, as printed in (27)–(28):
`(mᵢ zᵢ + n xᵢⱼ + q θ̄)/(mᵢ + n + q)`. -/
noncomputable def postMean (q n thetaBar mi zi xi : ℝ) : ℝ :=
  (mi * zi + n * xi + q * thetaBar) / (mi + n + q)

/-- A linear investment strategy (25)/(17): coefficients `βᵢ, γᵢ, λᵢ, ωᵢ, hᵢ` for each FI `i`. -/
structure LinStrat where
  beta : Fin 2 → ℝ
  gamma : Fin 2 → ℝ
  lam : Fin 2 → ℝ
  omega : Fin 2 → ℝ
  h : Fin 2 → ℝ

instance : Inhabited LinStrat := ⟨⟨0, 0, 0, 0, 0⟩⟩

/-- Investor `j`'s investment in FI `i` under the linear strategy `s` (17)/(25):
`kᵢⱼ = βᵢ xᵢⱼ + γᵢ zᵢ − b(λᵢ x₋ᵢⱼ + ωᵢ z₋ᵢ) + hᵢ`, where `z x : Fin 2 → ℝ` are the public signals
and investor `j`'s private signals. (The printed (25) has `xᵢⱼ` in the `λᵢ` term; (17) has `x₋ᵢⱼ`.) -/
def invest (s : LinStrat) (b : ℝ) (i : Fin 2) (z x : Fin 2 → ℝ) : ℝ :=
  s.beta i * x i + s.gamma i * z i - b * (s.lam i * x i.rev + s.omega i * z i.rev) + s.h i

/-- Investor `j`'s expectation of the aggregate investment `Kᵢ` (27), with `Eⱼ[θₖ]` the posterior
mean `postMean` of FI `k` computed from investor `j`'s own signal `x k` about FI `k` (the printed
(27) has `xᵢⱼ` in the `θ₋ᵢ` posterior; the information set `Iⱼ` and (17) give `x₋ᵢⱼ`). -/
noncomputable def expK (s : LinStrat) (b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (i : Fin 2)
    (z x : Fin 2 → ℝ) : ℝ :=
  s.beta i * postMean q n thetaBar (m i) (z i) (x i) + s.gamma i * z i
    - b * (s.lam i * postMean q n thetaBar (m i.rev) (z i.rev) (x i.rev) + s.omega i * z i.rev)
    + s.h i

/-- `s` is a linear equilibrium of the investors' game: for every realization of the public
signals `z` and of an investor's private signals `x`, and for each FI `i`, the investment rule (4)
`kᵢⱼ = Eⱼ[Rᵢ/2] − b Eⱼ[R₋ᵢ/2]` holds in the form (28),
`kᵢⱼ = Eⱼ[θᵢ] + a Eⱼ[Kᵢ] − b(Eⱼ[θ₋ᵢ] + a Eⱼ[K₋ᵢ])`. -/
def IsLinEq (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (s : LinStrat) : Prop :=
  ∀ (z x : Fin 2 → ℝ) (i : Fin 2),
    invest s b i z x =
      postMean q n thetaBar (m i) (z i) (x i) + a * expK s b q n thetaBar m i z x
        - b * (postMean q n thetaBar (m i.rev) (z i.rev) (x i.rev)
          + a * expK s b q n thetaBar m i.rev z x)

/-- The aggregate investment in FI `i` (26), given the fundamentals `θ` and the public signals `z`
(the private noises average out: `∫₀¹ xᵢⱼ dj = θᵢ`):
`Kᵢ = βᵢ θᵢ + γᵢ zᵢ − b(ωᵢ z₋ᵢ + λᵢ θ₋ᵢ) + hᵢ`. -/
def aggK (s : LinStrat) (b : ℝ) (i : Fin 2) (θ z : Fin 2 → ℝ) : ℝ :=
  s.beta i * θ i + s.gamma i * z i - b * (s.omega i * z i.rev + s.lam i * θ i.rev) + s.h i

/-- The joint law of `ω = (θ, ε)`: `θ₁, θ₂ ~ N(θ̄, 1/q)` and `εᵢ ~ N(0, 1/mᵢ)`, all four
independent. Mathlib's `gaussianReal μ v` takes the variance `v`; at `mᵢ = 0` the noise law is the
Dirac mass at `0` (Lean's `0⁻¹ = 0`). The public signal is `z = θ + ε` (2). -/
noncomputable def modelLaw (q thetaBar : ℝ) (m : Fin 2 → ℝ) :
    Measure ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  (Measure.pi fun _ : Fin 2 => gaussianReal thetaBar (q⁻¹).toNNReal).prod
    (Measure.pi fun i => gaussianReal 0 ((m i)⁻¹).toNNReal)

/-- FI `i`'s payoff (9) net of the disclosure cost (p. 8), when investors play the linear
strategy `s`: `Πᵢ = E[(Rᵢ/2) Kᵢ − Kᵢ²/2] − (c_m/2) mᵢ²`, with `Rᵢ/2 = θᵢ + a Kᵢ` by (1). -/
noncomputable def fiPayoff (a b q thetaBar cm : ℝ) (m : Fin 2 → ℝ) (s : LinStrat) (i : Fin 2) :
    ℝ :=
  (∫ ω, ((ω.1 i + a * aggK s b i ω.1 (ω.1 + ω.2)) * aggK s b i ω.1 (ω.1 + ω.2)
      - aggK s b i ω.1 (ω.1 + ω.2) ^ 2 / 2) ∂(modelLaw q thetaBar m))
    - cm / 2 * m i ^ 2

/-- FI `i`'s payoff when investors play a linear equilibrium for the precisions `m` (chosen by
`Classical.epsilon`; Lemma 1 and Proposition 3 show it exists, and it is unique in every
coefficient that enters the payoff). -/
noncomputable def eqPayoff (a b q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  fiPayoff a b q thetaBar cm m (Classical.epsilon (IsLinEq a b q n thetaBar m)) i

/-- A disclosure equilibrium: each FI's precision `mᵢ ≥ 0` maximizes its equilibrium payoff over
all precisions `t ≥ 0`, given the other FI's precision. -/
def IsDisclosureEq (a b q n thetaBar cm : ℝ) (m : Fin 2 → ℝ) : Prop :=
  ∀ i : Fin 2, 0 ≤ m i ∧
    ∀ t : ℝ, 0 ≤ t →
      eqPayoff a b q n thetaBar cm (Function.update m i t) i ≤ eqPayoff a b q n thetaBar cm m i

/-- The quartic `L(x) = A₀ + A₁x + A₂x² + A₃x³ + A₄x⁴` of (52)–(53). -/
noncomputable def Lpoly (a x : ℝ) : ℝ :=
  a ^ 2 + 3 * a ^ 2 * (2 - 3 * a) * x
    + (-3 * a * (2 - 3 * a) * (1 - 5 * (1 - a) * a)) * x ^ 2
    + (-a * (12 + a * (-82 + a * (206 + a * (-226 + 91 * a))))) * x ^ 3
    + (-(1 - a) * a * (1 - 2 * a) * (6 - a * (30 - a * (52 - 31 * a)))) * x ^ 4

/-- The gross marginal payoff without competition, first term of (33):
`(t + q − (1 − a)(1 − 4a)n) / (2(1 − a)²[q + t + (1 − a)n]³)`. -/
noncomputable def margNC (a q n t : ℝ) : ℝ :=
  (t + q - (1 - a) * (1 - 4 * a) * n) / (2 * (1 - a) ^ 2 * (q + t + (1 - a) * n) ^ 3)

/-- The gross marginal payoff at `b = 1`, first term of (44):
`(t + q − (1 − 2a)n) / (2(1 − 2a)[q + t + (1 − 2a)n]³)`. -/
noncomputable def margStar (a q n t : ℝ) : ℝ :=
  (t + q - (1 - 2 * a) * n) / (2 * (1 - 2 * a) * (q + t + (1 - 2 * a) * n) ^ 3)

end CompOpacity.Disclosure


