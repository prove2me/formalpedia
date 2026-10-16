-- Prove2me | Definitions.Def_NewsBundling_Negotiated_Setting
-- name    : NewsBundling_Negotiated_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:22.854092+00:00
-- url     : https://prove2.me/theorems/775cbb0e-1e07-4f72-ab17-a6460bf21dbb
-- title:
--   §6, pp. 18–20 — negotiated content-bundling game: Nash product, strategy profiles, equilibrium, q₁ and q₂
-- statement:
--   This file imports the shared baseline game and defines the negotiated game of §6 of de Cornière and Sarvary.
--
--   **The baseline game (§3–§4.2).** A publisher (newspaper) chooses a news quality $q\in[0,1]$ at cost $cq^2/2$. A social platform then chooses the share $\lambda\in[0,\Lambda]$ of news it shows on its own site. A consumer with one unit of time spends $T_1$ on the publisher's site and $T_0=1-T_1$ on the platform, so that she consumes $x_N=T_1+\lambda T_0$ units of news and $x_U=(1-\lambda)T_0$ units of user-generated content, with utility (1)
--
--   $$U(x_U,x_N)=x_U+(1+q)x_N-\frac{x_N^2}{2}.$$
--
--   The platform's revenue is $R_0=(1-\lambda+\lambda\varphi_0)T_0$ and the publisher's revenue is $R_1=\beta T_1+\varphi_1\lambda T_0$; the publisher's profit is $R_1-cq^2/2$. The standing assumptions (Table 1) are
--
--   $$\varphi_0,\varphi_1\in(0,1),\qquad \beta>\varphi_1,\qquad c>2\beta,\qquad \Lambda\in(0,1/2).$$
--
--   A strategy profile lists the consumer's time $T_1(q,\lambda)$ at every history, the platform's share $\lambda(q)$ at every quality, and the publisher's quality. It is a **subgame-perfect equilibrium** (SPE) when the consumer best-responds at every $q\in[0,1]$ and every $\lambda\in[0,\Lambda]$, the platform maximizes $R_0$ over $[0,\Lambda]$ at every $q\in[0,1]$, and the publisher's quality maximizes its profit over $[0,1]$. The benchmark without content bundling is the same game with $\Lambda=0$. The closed forms of §4.2 are
--
--   $$q_L(c)=\frac{\varphi_1}{c},\qquad q_H(c)=\frac{\beta-\Lambda\varphi_1}{c(1-\Lambda)},\qquad c^\dagger=\frac{\beta+\varphi_1(1-2\Lambda)}{2\Lambda(1-\Lambda)}.$$
--
--   **The negotiated game (§6).** The publisher chooses $q$; publisher and platform then agree, by Nash bargaining with equal power, on a lump-sum payment $F$ to the publisher; the platform chooses $\lambda\le\Lambda$ and keeps all advertising revenue (so $\varphi_0=1$, $\varphi_1=0$, footnote 16); the consumer allocates her time. The assumptions of §6 are
--
--   $$\tfrac13<\beta\le1,\qquad c>2\beta,\qquad \Lambda\in(0,1/2).$$
--
--   Given $q$ and the direct time $T_1$ that results from the platform's choice, the Nash product is
--
--   $$\bigl(\beta T_1+F-\beta q\bigr)\bigl((1-T_1)-F-(1-q)\bigr),$$
--
--   where $\beta T_1+F$ and $T_0-F$ are the payoffs under agreement and $\beta q$, $1-q$ the outside options printed on p. 19. A profile $(T_1(\cdot,\cdot),\lambda(\cdot),F(\cdot),q)$ is a **negotiated SPE** when the consumer best-responds at every $(q,\lambda)$; at every $q\in[0,1]$ the platform maximizes $T_0$ over $[0,\Lambda]$ and, when indifferent, chooses the smallest maximizer; at every $q\in[0,1]$ the fee maximizes the Nash product over all real $F$; and the publisher's quality maximizes $\beta T_1+F-cq^2/2$ over $[0,1]$. Finally
--
--   $$q_1(c)=\frac{1+\beta}{2c},\qquad q_2(c)=\frac{\beta(2-\Lambda)-\Lambda}{2(1-\Lambda)c}.$$
--
--   **Formalization Note** The baseline game is imported from the frozen shared module `NewsBundling.Unilateral.Setting`. Quality ranges over $[0,1]$ because demand for news equals $q$ and the paper notes the profit expression is valid only for $q\le1$. The negotiated platform revenue is `platformRevenue 1`, i.e. $R_0$ at $\varphi_0=1$, which equals $T_0$. The variable `lam` stands for $\lambda$.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), pp. 7–10, §3, (1), Table 1; pp. 10–12, §4.1–§4.2; pp. 18–20, §6, (3), (5), footnote 16

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Negotiated

/-! ## The baseline (unilateral) game of §3–§4.2 is imported from
`NewsBundling.Unilateral.Setting`. -/

/-! ## The negotiated game of §6 (pp. 18–20), with φ0 = 1 and φ1 = 0 (footnote 16). -/

/-- §6, pp. 18–19: 1/3 < β ≤ 1, together with c > 2β and Λ ∈ (0, 1/2) from Table 1. -/
def NegAssumptions (β c Λ : ℝ) : Prop :=
  (1 / 3 < β ∧ β ≤ 1) ∧ 2 * β < c ∧ (0 < Λ ∧ Λ < 1 / 2)

/-- Strategies of the four-stage negotiated game: `consumer q lam` is the direct time T₁,
`platform q` is the news share λ, `fee q` is the lump-sum payment F agreed at quality q,
and `quality` is the publisher's choice. -/
structure NegProfile where
  consumer : ℝ → ℝ → ℝ
  platform : ℝ → ℝ
  fee : ℝ → ℝ
  quality : ℝ

/-- (3), (5), p. 19–20: the Nash product with equal bargaining power. With agreement the
publisher gets βT₁ + F and the platform T₀ − F = (1 − T₁) − F; the outside options are
βq and 1 − q. -/
def nashProduct (β q T1 F : ℝ) : ℝ :=
  (β * T1 + F - β * q) * ((1 - T1) - F - (1 - q))

/-- Stage 1 payoff of the publisher: direct revenue βT₁ plus the fee, less cq²/2. -/
noncomputable def negPublisherProfit (β c : ℝ) (σ : NegProfile) (q : ℝ) : ℝ :=
  β * σ.consumer q (σ.platform q) + σ.fee q - c * q ^ 2 / 2

/-- Subgame-perfect equilibrium of the negotiated game: consumer best responses at every
(q, λ); the platform maximizes R₀ = T₀ (φ₀ = 1) at every q, choosing the smallest maximizer;
the fee maximizes the Nash product over all F ∈ ℝ at every q; the publisher's quality is
optimal on [0, 1]. -/
def IsNegotiatedSPE (β c Λ : ℝ) (σ : NegProfile) : Prop :=
  (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
      NewsBundling.Unilateral.IsConsumerBR q lam (σ.consumer q lam)) ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1,
      σ.platform q ∈ Set.Icc (0 : ℝ) Λ ∧
        (∀ lam ∈ Set.Icc (0 : ℝ) Λ,
          NewsBundling.Unilateral.platformRevenue 1 lam (σ.consumer q lam) ≤
            NewsBundling.Unilateral.platformRevenue 1 (σ.platform q) (σ.consumer q (σ.platform q))) ∧
        (∀ lam ∈ Set.Icc (0 : ℝ) Λ,
          NewsBundling.Unilateral.platformRevenue 1 lam (σ.consumer q lam) =
              NewsBundling.Unilateral.platformRevenue 1 (σ.platform q) (σ.consumer q (σ.platform q)) →
            σ.platform q ≤ lam)) ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ F : ℝ,
      nashProduct β q (σ.consumer q (σ.platform q)) F ≤
        nashProduct β q (σ.consumer q (σ.platform q)) (σ.fee q)) ∧
  σ.quality ∈ Set.Icc (0 : ℝ) 1 ∧
  ∀ q ∈ Set.Icc (0 : ℝ) 1, negPublisherProfit β c σ q ≤ negPublisherProfit β c σ σ.quality

/-- p. 20: q₁(c) = argmax_q F₁(q) − cq²/2 = (1 + β)/(2c). -/
noncomputable def q1 (β c : ℝ) : ℝ := (1 + β) / (2 * c)

/-- p. 20: q₂(c) = argmax_q F₂(q) + β(q − Λ)/(1 − Λ) − cq²/2 = (β(2 − Λ) − Λ)/(2(1 − Λ)c). -/
noncomputable def q2 (β c Λ : ℝ) : ℝ := (β * (2 - Λ) - Λ) / (2 * (1 - Λ) * c)

end NewsBundling.Negotiated


