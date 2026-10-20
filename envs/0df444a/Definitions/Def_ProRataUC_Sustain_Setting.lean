-- Prove2me | Definitions.Def_ProRataUC_Sustain_Setting
-- name    : ProRataUC_Sustain_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:15:47.587992+00:00
-- url     : https://prove2.me/theorems/651c5e21-1ce7-4235-8da0-a25c312d55f8
-- title:
--   §2–§3.2, pp. 8–17 — two-type streaming platform: setting, Assumption 1, solo revenue (1), pro-rata and user-centric payments, sustainability, β^pr (10), β^uc (11), regions W, Z, Y, X
-- statement:
--   This file sets up the model of a subscription streaming platform with two user types, following §2–§3.2 of Alaei, Makhdoumi, Malekian and Pekeč.
--
--   **Setting and standing assumptions (pp. 8–9).** A finite set $\mathcal M$ of artists and two user types $i\in\{1,2\}$ are given. Type $i$ users consume content at usage rate $\lambda_i$, have population mass $q_i$, and want artist $j$ with probability $\pi_{ij}$ per use. The standing assumptions are
--   $$\lambda_2>\lambda_1>0,\qquad q=(q_1,q_2)\in(0,1)^2,\quad q_1+q_2=1,\qquad \pi_{ij}\ge0,\quad \sum_{j\in\mathcal M}\pi_{ij}=1\ (i=1,2).$$
--   **Assumption 1** (p. 16) is the separate condition $\lambda_1\ge\lambda_2q_2$.
--
--   **Going solo (p. 10).** If artist $j$ sells her content directly at price $r$, type $i$ users buy exactly when $\lambda_i\pi_{ij}\ge r$, so the demand is
--   $$d(j,r)=\begin{cases}0,&\lambda_1\pi_{1j}<r\text{ and }\lambda_2\pi_{2j}<r,\\ q_1,&\lambda_1\pi_{1j}\ge r\text{ and }\lambda_2\pi_{2j}<r,\\ q_2,&\lambda_1\pi_{1j}<r\text{ and }\lambda_2\pi_{2j}\ge r,\\ 1,&\lambda_1\pi_{1j}\ge r\text{ and }\lambda_2\pi_{2j}\ge r,\end{cases}$$
--   and her solo revenue is $R_j=\max_r r\,d(j,r)$, equation (1), taken here as the supremum over all real prices $r$ (the function is bounded above by $\max(\lambda_1\pi_{1j},\lambda_2\pi_{2j})$).
--
--   **The platform with all artists.** With every artist on the platform and both types subscribing, the fee is the largest one both types accept, $\mathrm{Fee}=\min(\lambda_1\sum_j\pi_{1j},\ \lambda_2\sum_j\pi_{2j})$, and the revenue is $\mathrm{Rev}=\mathrm{Fee}\,(q_1+q_2)$. With payout rate $\beta$, the **pro-rata** payment (Definition 1) and the **user-centric** payment (Definition 2) to artist $j$ are
--   $$p^{\mathrm{pr}}_j(\beta)=\beta\,\mathrm{Rev}\,\frac{q_1\lambda_1\pi_{1j}+q_2\lambda_2\pi_{2j}}{q_1\lambda_1\sum_k\pi_{1k}+q_2\lambda_2\sum_k\pi_{2k}},\qquad p^{\mathrm{uc}}_j(\beta)=\beta\sum_{i=1}^2 q_i\,\mathrm{Fee}\,\frac{\lambda_i\pi_{ij}}{\sum_k\lambda_i\pi_{ik}}.$$
--
--   **Sustainability (p. 17).** The platform is *sustainable* with the pro-rata (resp. user-centric) rule if some payout rate $\beta\in[0,1]$ pays every artist at least her solo revenue: $R_j\le p^{\mathrm{pr}}_j(\beta)$ (resp. $R_j\le p^{\mathrm{uc}}_j(\beta)$) for all $j$.
--
--   **Minimal payout rates (10)–(11), p. 16:**
--   $$\beta^{\mathrm{pr}}=\frac{q_1\lambda_1+q_2\lambda_2}{\lambda_1}\max_{j\in\mathcal M}\frac{R_j}{q_1\lambda_1\pi_{1j}+q_2\lambda_2\pi_{2j}},\qquad \beta^{\mathrm{uc}}=\frac1{\lambda_1}\max_{j\in\mathcal M}\frac{R_j}{q_1\pi_{1j}+q_2\pi_{2j}}.$$
--
--   **Regions (p. 14)**, by the ratio $\pi_{2j}/\pi_{1j}$:
--   $$W:\ [0,\tfrac{q_1\lambda_1}{\lambda_2}),\quad Z:\ [\tfrac{q_1\lambda_1}{\lambda_2},\tfrac{\lambda_1}{\lambda_2}),\quad Y:\ [\tfrac{\lambda_1}{\lambda_2},\tfrac{\lambda_1}{\lambda_2q_2}),\quad X:\ [\tfrac{\lambda_1}{\lambda_2q_2},\infty).$$
--
--   These objects are the vocabulary of the paper's sustainability analysis (Lemma 1, equations (10)–(11), Lemmas 6–7 and Theorem 1).
--
--   **Formalization Note** The setting is a structure `Setting M` with real fields `lam1 lam2 q1 q2` and functions `pi1 pi2 : M → ℝ`, over a type `M` of artists with `[Fintype M]`. The solo revenue is the real supremum `⨆ r : ℝ, r * demand s j r` of the four-case demand, not a closed form. `fee` and `rev` fix the paper's situation $J=\mathcal M$, $S=\{1,2\}$ and keep the sums $\sum_j\pi_{ij}$ as printed; that they equal $\lambda_1$ under the standing assumptions is not built in. Sustainability is the existence of a payout rate $\beta\in[0,1]$, not the condition $\beta^{\mathrm{pr}}\le1$. `betaPR`/`betaUC` use `Finset.univ.sup'` and so need `[Nonempty M]`. The ratio $\pi_{2j}/\pi_{1j}$ is real division, which Lean sets to $0$ when $\pi_{1j}=0$; every theorem using the regions assumes $\pi_{1j}>0$.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), pp. 8–17: §2 (setting, p. 8–9), §2.3 d(j,r) and (1) (p. 10), §2.4.2 Definitions 1–2 (pp. 12–13), §3.1 regions W, Z, Y, X (p. 14), §3.2 Assumption 1, (10), (11) (p. 16), sustainability (p. 17)

import Mathlib

namespace ProRataUC.Sustain

/-- The setting `(λ, q, Π)` of §2 (pp. 8–9): artists indexed by a type `M`, two user types with
usage rates `lam1`, `lam2` and masses `q1`, `q2`, and the listening probabilities `pi1 j`, `pi2 j`
of type 1 and type 2 users for artist `j`. -/
structure Setting (M : Type*) where
  lam1 : ℝ
  lam2 : ℝ
  q1 : ℝ
  q2 : ℝ
  pi1 : M → ℝ
  pi2 : M → ℝ

variable {M : Type*}

/-- Standing assumptions, p. 9: `λ2 > λ1 > 0`, `q ∈ (0,1)²`, `q1 + q2 = 1`, and each row
`π_i·` of `Π` a probability vector over the artists. -/
def Setting.Standing [Fintype M] (s : Setting M) : Prop :=
  0 < s.lam1 ∧ s.lam1 < s.lam2 ∧ 0 < s.q1 ∧ s.q1 < 1 ∧ 0 < s.q2 ∧ s.q2 < 1 ∧ s.q1 + s.q2 = 1 ∧
    (∀ j, 0 ≤ s.pi1 j) ∧ (∀ j, 0 ≤ s.pi2 j) ∧ ∑ j, s.pi1 j = 1 ∧ ∑ j, s.pi2 j = 1

/-- Assumption 1, p. 16: `λ1 ≥ λ2 q2`. -/
def Assumption1 (s : Setting M) : Prop := s.lam2 * s.q2 ≤ s.lam1

/-- The solo demand `d(j,r)` of artist `j` at price `r`, p. 10, in the four printed cases. -/
noncomputable def demand (s : Setting M) (j : M) (r : ℝ) : ℝ :=
  if s.lam1 * s.pi1 j < r ∧ s.lam2 * s.pi2 j < r then 0
  else if r ≤ s.lam1 * s.pi1 j ∧ s.lam2 * s.pi2 j < r then s.q1
  else if s.lam1 * s.pi1 j < r ∧ r ≤ s.lam2 * s.pi2 j then s.q2
  else 1

/-- The solo revenue `R_j = max_r r d(j,r)`, (1), p. 10, as the supremum over all real prices.
The family is bounded above by `max (λ1 π1j) (λ2 π2j)` under the standing assumptions, so this is
a genuine supremum. -/
noncomputable def soloRevenue (s : Setting M) (j : M) : ℝ := ⨆ r : ℝ, r * demand s j r

/-- The subscription fee `Fee(M)` with all artists on the platform and both user types
subscribing: the largest fee both types accept, `min_i λ_i Σ_j π_ij` (§2.2, p. 9). -/
noncomputable def fee [Fintype M] (s : Setting M) : ℝ :=
  min (s.lam1 * ∑ j, s.pi1 j) (s.lam2 * ∑ j, s.pi2 j)

/-- The platform revenue `Rev = Fee(M) Σ_{i∈S} q_i` with `S = {1,2}` (§2.4.2, p. 12). -/
noncomputable def rev [Fintype M] (s : Setting M) : ℝ := fee s * (s.q1 + s.q2)

/-- Definition 1 (pro-rata payment), p. 12, with `J = M` and `S = {1,2}`. -/
noncomputable def proRataPay [Fintype M] (s : Setting M) (β : ℝ) (j : M) : ℝ :=
  β * rev s * (s.q1 * s.lam1 * s.pi1 j + s.q2 * s.lam2 * s.pi2 j) /
    (s.q1 * s.lam1 * ∑ k, s.pi1 k + s.q2 * s.lam2 * ∑ k, s.pi2 k)

/-- Definition 2 (user-centric payment, first form), pp. 12–13, with `J = M` and `S = {1,2}`. -/
noncomputable def userCentricPay [Fintype M] (s : Setting M) (β : ℝ) (j : M) : ℝ :=
  β * (s.q1 * fee s * (s.lam1 * s.pi1 j / ∑ k, s.lam1 * s.pi1 k) +
       s.q2 * fee s * (s.lam2 * s.pi2 j / ∑ k, s.lam2 * s.pi2 k))

/-- p. 17: the platform is sustainable with the pro-rata rule when some payout rate
`β ∈ [0,1]` pays every artist at least her solo revenue. -/
def SustainablePR [Fintype M] (s : Setting M) : Prop :=
  ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧ ∀ j, soloRevenue s j ≤ proRataPay s β j

/-- p. 17: the platform is sustainable with the user-centric rule when some payout rate
`β ∈ [0,1]` pays every artist at least her solo revenue. -/
def SustainableUC [Fintype M] (s : Setting M) : Prop :=
  ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧ ∀ j, soloRevenue s j ≤ userCentricPay s β j

/-- `β^pr`, (10), p. 16 (first line). -/
noncomputable def betaPR [Fintype M] [Nonempty M] (s : Setting M) : ℝ :=
  (s.q1 * s.lam1 + s.q2 * s.lam2) / s.lam1 *
    Finset.univ.sup' Finset.univ_nonempty
      (fun j => soloRevenue s j / (s.q1 * s.lam1 * s.pi1 j + s.q2 * s.lam2 * s.pi2 j))

/-- `β^uc`, (11), p. 16 (first line). -/
noncomputable def betaUC [Fintype M] [Nonempty M] (s : Setting M) : ℝ :=
  1 / s.lam1 *
    Finset.univ.sup' Finset.univ_nonempty
      (fun j => soloRevenue s j / (s.q1 * s.pi1 j + s.q2 * s.pi2 j))

/-- The region `W`, p. 14: `π2j/π1j ∈ [0, q1λ1/λ2)`. -/
def regionW (s : Setting M) : Set M :=
  {j | s.pi2 j / s.pi1 j ∈ Set.Ico 0 (s.q1 * s.lam1 / s.lam2)}

/-- The region `Z`, p. 14: `π2j/π1j ∈ [q1λ1/λ2, λ1/λ2)`. -/
def regionZ (s : Setting M) : Set M :=
  {j | s.pi2 j / s.pi1 j ∈ Set.Ico (s.q1 * s.lam1 / s.lam2) (s.lam1 / s.lam2)}

/-- The region `Y`, p. 14: `π2j/π1j ∈ [λ1/λ2, λ1/(λ2q2))`. -/
def regionY (s : Setting M) : Set M :=
  {j | s.pi2 j / s.pi1 j ∈ Set.Ico (s.lam1 / s.lam2) (s.lam1 / (s.lam2 * s.q2))}

/-- The region `X`, p. 14: `π2j/π1j ∈ [λ1/(λ2q2), ∞)`. -/
def regionX (s : Setting M) : Set M :=
  {j | s.pi2 j / s.pi1 j ∈ Set.Ici (s.lam1 / (s.lam2 * s.q2))}

end ProRataUC.Sustain


