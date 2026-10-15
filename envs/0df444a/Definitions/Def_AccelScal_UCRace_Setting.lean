-- Prove2me | Definitions.Def_AccelScal_UCRace_Setting
-- name    : AccelScal_UCRace_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:27.427306+00:00
-- url     : https://prove2.me/theorems/540f3764-9039-4096-bc1f-bac7a0c8a58e
-- title:
--   §§2–3.1, (2), (7), (8), (9) — two-firm unconstrained R&D race setting
-- statement:
--   Each firm $i\in\{1,2\}$ has technology parameters $(A_i,\beta_i,\eta_i,\gamma_i)$ and chooses a fixed investment intensity $R_i$. Its expected discovery payoff and discovery rate are
--
--   $$
--   u_i(R_i)=A_iR_i^{\beta_i},\qquad \lambda_i(R_i)=\eta_iR_i^{\gamma_i}.
--   $$
--
--   The standing conditions are $A_i,\eta_i>0$, $0\le\beta_i,\gamma_i<1$, $\beta_i+\gamma_i<1$, and $A_i\eta_i>1$. Each firm's feasible intensities lie in $[1,\bar R_i]$, where $\bar R_i=(A_i\eta_i)^{1/(1-\beta_i-\gamma_i)}$. The firms may have different parameters. They pay their respective rate until the first discovery; the firm discovering first receives $u_i(R_i)$, discounted at $r>0$. Payoffs are expectations under the independent exponential race law. A best-response set contains every own feasible intensity maximizing this expected payoff at the rival's fixed intensity. A pure Nash equilibrium is a pair of mutual best responses. The setting also names the closed form $V_1=(u_1\lambda_1-R_1)/(r+\lambda_1+\lambda_2)$ separately for use in Appendix A.6.
--
--   These definitions give the stochastic race and its strategy sets a common interface for the two milestones and Proposition 3.
--
--   **Formalization Note** $A_i\eta_i>1$ makes the stated investment range nondegenerate and is the disclosed condition that investment takes place. The random discovery payoff is replaced by its mean, as in the paper's calculations. The payoff itself remains the expectation in (8); $V_1$ is a separate closed-form expression. Firm 2 wins when the second discovery-time coordinate is smaller.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, pp. 4–8, (2), (7)–(9)

import Mathlib
import Definitions.Def_AccelScal_UCRace_ExponentialRace
import Definitions.Def_AccelScal_UCMonopoly_Setting

noncomputable section

open MeasureTheory

namespace AccelScal.UCRace

structure Tech where
  A : ℝ
  β : ℝ
  η : ℝ
  γ : ℝ

def Tech.Standing (T : Tech) : Prop :=
  0 < T.A ∧ 0 < T.η ∧ 0 ≤ T.β ∧ T.β < 1 ∧
    0 ≤ T.γ ∧ T.γ < 1 ∧ T.β + T.γ < 1 ∧ 1 < T.A * T.η

def Tech.u (T : Tech) (R : ℝ) : ℝ := T.A * R ^ T.β

def Tech.lam (T : Tech) (R : ℝ) : ℝ := T.η * R ^ T.γ

def Tech.Rbar (T : Tech) : ℝ :=
  (T.A * T.η) ^ (1 / (1 - (T.β + T.γ)))

/-- Firm 1 receives its mean payoff if its discovery time is first, and pays until
the first discovery. -/
def payoff1 (T1 T2 : Tech) (r R1 R2 : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,
    (Real.exp (-r * p.1) * T1.u R1 * (if p.1 < p.2 then 1 else 0)
      - R1 * ∫ t in (0)..(min p.1 p.2), Real.exp (-r * t))
      ∂exponentialRace (T1.lam R1) (T2.lam R2)

/-- Firm 2 wins when the second coordinate is the earlier discovery time. -/
def payoff2 (T1 T2 : Tech) (r R1 R2 : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,
    (Real.exp (-r * p.2) * T2.u R2 * (if p.2 < p.1 then 1 else 0)
      - R2 * ∫ t in (0)..(min p.1 p.2), Real.exp (-r * t))
      ∂exponentialRace (T1.lam R1) (T2.lam R2)

def BR1 (T1 T2 : Tech) (r R2 : ℝ) : Set ℝ :=
  {R1 | R1 ∈ Set.Icc 1 T1.Rbar ∧
    ∀ R1' ∈ Set.Icc 1 T1.Rbar, payoff1 T1 T2 r R1' R2 ≤ payoff1 T1 T2 r R1 R2}

def BR2 (T1 T2 : Tech) (r R1 : ℝ) : Set ℝ :=
  {R2 | R2 ∈ Set.Icc 1 T2.Rbar ∧
    ∀ R2' ∈ Set.Icc 1 T2.Rbar, payoff2 T1 T2 r R1 R2' ≤ payoff2 T1 T2 r R1 R2}

def IsNash (T1 T2 : Tech) (r R1 R2 : ℝ) : Prop :=
  R1 ∈ BR1 T1 T2 r R2 ∧ R2 ∈ BR2 T1 T2 r R1

def V1 (T1 T2 : Tech) (r R1 R2 : ℝ) : ℝ :=
  (T1.u R1 * T1.lam R1 - R1) / (r + T1.lam R1 + T2.lam R2)

end AccelScal.UCRace


