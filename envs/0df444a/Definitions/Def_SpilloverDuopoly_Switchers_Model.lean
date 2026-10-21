-- Prove2me | Definitions.Def_SpilloverDuopoly_Switchers_Model
-- name    : SpilloverDuopoly_Switchers_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:46.365675+00:00
-- url     : https://prove2.me/theorems/f13ea669-e8d0-4e46-a986-24b8de63e06e
-- title:
--   §2, §4, §5.1, pp. 6–21 — two-period experience-goods duopoly in reduced form: first-period share rule, two-period profits from repeat and switching consumers, symmetric equilibrium
-- statement:
--   Two firms $A$ and $B$ each sell one non-durable experience good. Both have marginal cost $c\ge 0$, and firms and consumers share a discount factor $\delta\in[0,1]$. A unit mass of ex-ante identical consumers buys in each of two periods. This definition records the first-period price game that remains once the second period has been solved.
--
--   **Data.** Besides $c$ and $\delta$, the model has the following data.
--
--   1. A tie share $\lambda\in[0,1]$: firm $A$'s first-period market share when consumers are indifferent between the two goods. Firm $B$ then gets $1-\lambda$.
--   2. The per-unit second-period profits $\pi^{R*}$ and $\pi^{S*}$. A firm earns $\pi^{R*}$ per unit of its own first-period buyers (repeat consumers) and $\pi^{S*}$ per unit of the rival's first-period buyers (switching consumers). Neither depends on first-period market shares.
--   3. The gross present value $V$ to a consumer of buying either good in the first period, so that buying at price $p$ yields surplus $CS(p)=V-p$.
--   4. The present value $u_0$ of not buying in the first period.
--
--   **Shares.** At first-period prices $(p_A,p_B)$, firm $A$'s share is
--
--   $$
--   \lambda_A(p_A,p_B)=\begin{cases}1 & \text{if } CS(p_A)>CS(p_B)\text{ and } CS(p_A)\ge u_0,\\ \lambda & \text{if } CS(p_A)=CS(p_B)\ge u_0,\\ 0 & \text{otherwise,}\end{cases}
--   $$
--
--   and $\lambda_B(p_A,p_B)$ is defined symmetrically, with $1-\lambda$ on a tie.
--
--   **Profits.** Firm $i$'s two-period profit is
--
--   $$
--   \Pi_i(p_A,p_B)=\lambda_i\,(p_i-c)+\delta\bigl(\lambda_i\,\pi^{R*}+\lambda_{-i}\,\pi^{S*}\bigr).
--   $$
--
--   **Equilibrium.** A price $p$ is a *symmetric equilibrium* when $(p,p)$ is a pure-strategy Nash equilibrium of this game with real prices. That is, $\Pi_A(p',p)\le\Pi_A(p,p)$ and $\Pi_B(p,p')\le\Pi_B(p,p)$ for every $p'\in\mathbb R$.
--
--   The definition also fixes the candidate price $p^*=c-\delta(\pi^{R*}-\pi^{S*})$, and the standing assumptions $c\ge0$, $0\le\delta\le1$, $0\le\lambda\le1$.
--
--   These objects are the common model for Theorem 1 of the paper and for the steps of its proof.
--
--   **Formalization Note** The paper's second-period subgame, with its correlation parameter $\rho\in[-1,1]$ and its niche, semi-niche and mass-market equilibria, enters Theorem 1 only through $\pi^{R*}$ and $\pi^{S*}$. These are therefore free real parameters, and there is no $\rho$ in the Lean. On p. 15 the outside value is $0$, and with the delay option of pp. 15–16 it is $\delta(\mu-S^*)$; the model allows any real $u_0$. Prices are unrestricted reals. The equilibrium condition is the platform's published two-player pure Nash predicate `CrossLicensing.ExPost.IsNE`, with both strategy sets equal to $\mathbb R$.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), pp. 6–21 (PDF 8–23), §2, eq. (5), §4 (consumer surplus and share rule, p. 15), §5.1

import Mathlib
import Definitions.Def_CrossLicensing_ExPost_Game

namespace SpilloverDuopoly.Switchers

/-- Reduced-form data of the two-period experience-goods duopoly (§2, §4, §5.1).
The second-period subgame enters only through the per-unit profits `piR` (from the firm's own
first-period buyers, the repeat consumers) and `piS` (from the rival's first-period buyers, the
switchers), which do not depend on first-period market shares (p. 10). -/
structure Params where
  /-- `c`: common marginal cost (p. 6). -/
  c : ℝ
  /-- `δ`: common discount factor of firms and consumers (p. 6). -/
  delta : ℝ
  /-- `λ`: firm A's first-period share when the two surpluses tie; firm B gets `1 - λ` (p. 15). -/
  lam : ℝ
  /-- `π^{R∗}`: second-period profit per unit of first-period share (repeat consumers). -/
  piR : ℝ
  /-- `π^{S∗}`: second-period profit per unit of the rival's first-period share (switchers). -/
  piS : ℝ
  /-- `V`: consumers' gross present value of a first-period purchase of either good (p. 15). -/
  V : ℝ
  /-- `u0`: consumers' present value of not buying in the first period (zero on p. 15). -/
  u0 : ℝ

/-- Standing assumptions: `c ≥ 0`, `δ ∈ [0, 1]` (p. 6) and a tie share `λ ∈ [0, 1]` (Theorem 1). -/
def Params.Standing (G : Params) : Prop :=
  0 ≤ G.c ∧ 0 ≤ G.delta ∧ G.delta ≤ 1 ∧ 0 ≤ G.lam ∧ G.lam ≤ 1

/-- Present value of consumer surplus from buying a good at first-period price `p`: `V - p`. -/
def Params.CS (G : Params) (p : ℝ) : ℝ := G.V - p

/-- Firm A's first-period market share at prices `(pA, pB)` (share rule, p. 15): `1` if A's surplus
is strictly greater than B's and no less than the outside value, `λ` if the two surpluses are equal
and no less than the outside value, `0` otherwise. -/
noncomputable def Params.shareA (G : Params) (pA pB : ℝ) : ℝ :=
  if G.u0 ≤ G.CS pA ∧ G.CS pB < G.CS pA then 1
  else if G.u0 ≤ G.CS pA ∧ G.CS pA = G.CS pB then G.lam else 0

/-- Firm B's first-period market share at prices `(pA, pB)`; on a tie B gets `1 - λ`. -/
noncomputable def Params.shareB (G : Params) (pA pB : ℝ) : ℝ :=
  if G.u0 ≤ G.CS pB ∧ G.CS pA < G.CS pB then 1
  else if G.u0 ≤ G.CS pB ∧ G.CS pB = G.CS pA then 1 - G.lam else 0

/-- Firm A's two-period profit: first-period margin on its share, plus the discounted
second-period profit `λ_A π^{R∗} + λ_B π^{S∗}`. -/
noncomputable def Params.profitA (G : Params) (pA pB : ℝ) : ℝ :=
  G.shareA pA pB * (pA - G.c) + G.delta * (G.shareA pA pB * G.piR + G.shareB pA pB * G.piS)

/-- Firm B's two-period profit: `λ_B (p_B - c) + δ (λ_B π^{R∗} + λ_A π^{S∗})`. -/
noncomputable def Params.profitB (G : Params) (pA pB : ℝ) : ℝ :=
  G.shareB pA pB * (pB - G.c) + G.delta * (G.shareB pA pB * G.piR + G.shareA pA pB * G.piS)

/-- A symmetric (pure-strategy) equilibrium of the first-period price game: the profile `(p, p)`
is a Nash equilibrium with real prices, i.e. no firm gains from any unilateral price `p' ∈ ℝ`. -/
def Params.IsSymEq (G : Params) (p : ℝ) : Prop :=
  CrossLicensing.ExPost.IsNE Set.univ Set.univ G.profitA (fun pB pA => G.profitB pA pB) (p, p)

/-- The price of Theorem 1: `p∗ = c - δ (π^{R∗} - π^{S∗})`. -/
def Params.pStar (G : Params) : ℝ := G.c - G.delta * (G.piR - G.piS)

end SpilloverDuopoly.Switchers


