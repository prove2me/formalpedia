-- Prove2me | Definitions.Def_NewsBundling_Unilateral_Setting
-- name    : NewsBundling_Unilateral_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:11.790006+00:00
-- url     : https://prove2.me/theorems/968de74c-bcbc-4f16-b2d0-2da34f8c5269
-- title:
--   §3–§4.2, Table 1, pp. 7–12 — unilateral content-bundling game
-- statement:
--   A newspaper first chooses news quality $q\in[0,1]$, a platform then chooses the share $\lambda\in[0,\Lambda]$ of news in its feed, and a representative consumer finally allocates one unit of time between the newspaper and the platform. If $T_1$ is time at the newspaper, then $T_0=1-T_1$, $x_N=T_1+\lambda T_0$ is news consumption, and $x_U=(1-\lambda)T_0$ is user-generated content. Consumer utility is
--
--   $$U(x_U,x_N)=x_U+(1+q)x_N-\frac{x_N^2}{2}.$$
--
--   The platform earns $R_0=(1-\lambda+\lambda\phi_0)T_0$. The newspaper earns $R_1=\beta T_1+\phi_1\lambda T_0$ and pays quality cost $cq^2/2$. A strategy profile specifies consumer time for every $(q,\lambda)$, a platform share for every $q$, and the newspaper's quality. It is a subgame-perfect equilibrium when each stage chooses a best response at every feasible history. Publisher profit and consumer surplus are evaluated at the equilibrium outcome; the latter is the consumer's utility there. The no-bundling benchmark is the same game with $\Lambda=0$.
--
--   The standing ranges are $0<\phi_0,\phi_1<1$, $\phi_1<\beta$, $2\beta<c$, and $0<\Lambda<1/2$. The auxiliary expressions used in the paper's quality comparison are
--
--   $$q_L=\frac{\phi_1}{c},\qquad q_H=\frac{\beta-\Lambda\phi_1}{c(1-\Lambda)},\qquad c^\dagger=\frac{\beta+\phi_1(1-2\Lambda)}{2\Lambda(1-\Lambda)}.$$
--
--   These definitions provide the game on which Proposition 1 and its supporting lemmas operate; the negotiated-bundling game behind Proposition 5 compares its outcome with this game's equilibrium quality. The quality candidates are formulas for branch optima; they do not define equilibrium quality.
--
--   **Formalization Note** Quality and attention lie in $[0,1]$. Consumer and platform best responses are required after every feasible history. The benchmark is obtained by evaluating the equilibrium predicate at $\Lambda=0$. The standing ranges are those of Table 1 (p. 10); the text of p. 9 writes $\phi_0\le 1$, and the strict bound of Table 1 is used here. The standing ranges are a separate predicate, so a game with $\phi_0=1$ (as in §6) uses the same equilibrium predicate without them. The total real division functions in $q_L$, $q_H$, and $c^\dagger$ are used only in theorem statements whose assumptions make their denominators nonzero.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), pp. 7–10, §3, (1), Table 1; pp. 11–12, §4.2

import Mathlib

namespace NewsBundling.Unilateral

/-- Table 1, p. 10: the standing parameter restrictions. -/
def StandingAssumptions (β φ0 φ1 c Λ : ℝ) : Prop :=
  (0 < φ0 ∧ φ0 < 1) ∧ (0 < φ1 ∧ φ1 < 1) ∧ φ1 < β ∧ 2 * β < c ∧
    (0 < Λ ∧ Λ < 1 / 2)

/-- Equation (1), p. 8: utility from UGC and news. -/
noncomputable def utility (q xU xN : ℝ) : ℝ := xU + (1 + q) * xN - xN ^ 2 / 2

/-- Consumer utility when T₁ is spent at the publisher and 1-T₁ at the platform. -/
noncomputable def consumerPayoff (q lam T1 : ℝ) : ℝ :=
  utility q ((1 - lam) * (1 - T1)) (T1 + lam * (1 - T1))

/-- The last-stage consumer's best-response condition at every feasible attention split. -/
def IsConsumerBR (q lam T1 : ℝ) : Prop :=
  T1 ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ T ∈ Set.Icc (0 : ℝ) 1, consumerPayoff q lam T ≤ consumerPayoff q lam T1

/-- Section 3, p. 9: platform revenue R₀. -/
def platformRevenue (φ0 lam T1 : ℝ) : ℝ :=
  (1 - lam + lam * φ0) * (1 - T1)

/-- Section 3, p. 9: publisher revenue R₁. -/
def publisherRevenue (β φ1 lam T1 : ℝ) : ℝ :=
  β * T1 + φ1 * lam * (1 - T1)

/-- Complete contingent strategies in the publisher-platform-consumer sequential game. -/
structure Profile where
  consumer : ℝ → ℝ → ℝ
  platform : ℝ → ℝ
  quality : ℝ

/-- Section 3, p. 9: publisher revenue less the cost cq²/2. -/
noncomputable def publisherProfit (β φ1 c : ℝ) (σ : Profile) (q : ℝ) : ℝ :=
  publisherRevenue β φ1 (σ.platform q) (σ.consumer q (σ.platform q)) - c * q ^ 2 / 2

/-- Subgame perfection: consumers and the platform optimize after every feasible history,
then the publisher chooses quality on [0,1]. -/
def IsSPE (β φ0 φ1 c Λ : ℝ) (σ : Profile) : Prop :=
  (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
      IsConsumerBR q lam (σ.consumer q lam)) ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1,
      σ.platform q ∈ Set.Icc (0 : ℝ) Λ ∧
        ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
          platformRevenue φ0 lam (σ.consumer q lam) ≤
            platformRevenue φ0 (σ.platform q) (σ.consumer q (σ.platform q))) ∧
  σ.quality ∈ Set.Icc (0 : ℝ) 1 ∧
  ∀ q ∈ Set.Icc (0 : ℝ) 1,
    publisherProfit β φ1 c σ q ≤ publisherProfit β φ1 c σ σ.quality

/-- Publisher profit at the equilibrium outcome. -/
noncomputable def eqProfit (β φ1 c : ℝ) (σ : Profile) : ℝ :=
  publisherProfit β φ1 c σ σ.quality

/-- Consumer utility at the equilibrium outcome. -/
noncomputable def consumerSurplus (σ : Profile) : ℝ :=
  consumerPayoff σ.quality (σ.platform σ.quality)
    (σ.consumer σ.quality (σ.platform σ.quality))

/-- Section 4.2, p. 12: low-quality candidate q_L(c). -/
noncomputable def qL (φ1 c : ℝ) : ℝ := φ1 / c

/-- Section 4.2, p. 12: high-quality candidate q_H(c). -/
noncomputable def qH (β φ1 c Λ : ℝ) : ℝ :=
  (β - Λ * φ1) / (c * (1 - Λ))

/-- Section 4.2, p. 12: the quality-cost threshold c†. -/
noncomputable def cdagger (β φ1 Λ : ℝ) : ℝ :=
  (β + φ1 * (1 - 2 * Λ)) / (2 * Λ * (1 - Λ))

/-- Section 4.2, p. 12: low-quality branch of publisher profit. -/
noncomputable def pi1L (φ1 q c : ℝ) : ℝ := φ1 * q - c * q ^ 2 / 2

/-- Section 4.2, p. 12: high-quality branch of publisher profit. -/
noncomputable def pi1H (β φ1 Λ q c : ℝ) : ℝ :=
  φ1 * Λ * (1 - q) / (1 - Λ) + β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2

end NewsBundling.Unilateral


