-- Prove2me | Definitions.Def_ReviewBlackmail_SemiDec_Setting
-- name    : ReviewBlackmail_SemiDec_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:10.053985+00:00
-- url     : https://prove2.me/theorems/029934bb-0739-4ae5-89c9-3e0c501f10e9
-- title:
--   §3, §5, Proof of Propositions 4–5 — the review-blackmail game under semi-decentralized dispute resolution: Bayes posteriors, seller payoffs, equilibrium, selection, purchase rule, b̲
-- statement:
--   This file fixes the review-blackmail game of Papanastasiou, Yang and Zhang under the **semi-decentralized** dispute-resolution mechanism ("D"), in which the seller may remove a negative review at once and the platform later checks the removal.
--
--   **Primitives.** A model consists of the prior $a$ that the product's quality is high, the probability $\theta$ that a high-quality product gives a buyer a positive experience, the probability $\beta$ that the consumer is malicious, the price $p$, the platform's timeliness $\gamma$ (probability that a dispute is judged immediately), its accuracy $\delta$ (probability that a malicious review is recognised as malicious), the penalty $b$ for a wrongful removal, and the seller's future payoff $\pi(a')$ as a function of the market's posterior belief $a'$. The **standing assumptions** are
--   $$a,\theta,\beta\in(0,1),\qquad \gamma,\delta\in[0,1],\qquad b\ge 0,\qquad 0<p<a\theta,$$
--   and $\pi$ is nonnegative, convex and strictly increasing on $[0,1]$.
--
--   **Reviews and posteriors.** A regular consumer buys with probability $\rho=1-p/(a\theta)$ (the valuation $v_j$ is standard uniform) and reviews truthfully: positive ($P$) with probability $\theta$ if the quality is high, negative ($N$) otherwise; no purchase means no review ($R=0$). A malicious consumer always buys and posts $N$. If a malicious negative review stays visible with probability $m$ and a genuine one with probability $g$, and a removed review is observed as $R=0$, the likelihoods are
--   $$\begin{aligned}
--   P(N\mid h)&=\beta m+(1-\beta)\rho(1-\theta)g, & P(N\mid l)&=\beta m+(1-\beta)\rho g,\\
--   P(P\mid h)&=(1-\beta)\rho\theta, & P(P\mid l)&=0,\\
--   P(0\mid h)&=\beta(1-m)+(1-\beta)\big[(1-\rho)+\rho(1-\theta)(1-g)\big], & P(0\mid l)&=\beta(1-m)+(1-\beta)\big[(1-\rho)+\rho(1-g)\big],
--   \end{aligned}$$
--   and the market's posterior is given by Bayes' rule,
--   $$a_R(m,g)=\frac{a\,P(R\mid h)}{a\,P(R\mid h)+(1-a)\,P(R\mid l)}.$$
--   Against a malicious review the seller settles ($s$, $m=0$), does nothing ($n$, $m=1$) or removes it through the mechanism ($d$, $m=\gamma(1-\delta)$: the review is reinstated only when the platform judges immediately and wrongly). The paper's $a^i_R$ is $a_R(m_i,1)$ (genuine reviews kept), and its $a^{sd}_R$ of (38) is $a_R(0,\gamma)$.
--
--   **Payoffs and equilibrium.** When the market believes the seller's response is $i$ and a malicious consumer demands ransom $r$, response $j$ pays
--   $$\pi(a^i_0)-r\ (j=s),\qquad \pi(a^i_N)\ (j=n),\qquad (1-\gamma(1-\delta))\pi(a^i_0)+\gamma(1-\delta)\pi(a^i_N)-(1-\delta)b\ (j=d).$$
--   Response $i$ is an **equilibrium** at $r$ if no response pays more given that belief. **Settling prevails** at $r$ if settling is an equilibrium and no equilibrium pays the seller strictly more. The malicious consumer **purchases** iff some ransom at which settling prevails exceeds $p$.
--
--   **Genuine reviews.** $\underline b:=(1-\gamma)[\pi(a)-\pi(a^s_N)]$. Under the belief "settle malicious, keep genuine", removing a genuine negative review is not profitable when $(1-\gamma)\pi(a^s_0)+\gamma\pi(a^s_N)-b\le\pi(a^s_N)$ (condition (21)); under the belief "settle malicious, remove genuine", keeping it is not profitable when $\pi(a^{sd}_N)\le(1-\gamma)\pi(a^{sd}_0)+\gamma\pi(a^{sd}_N)-b$.
--
--   These objects are the common ground of every statement of this mission: the posterior (5), Proposition 4, the equilibrium conditions of Step 1 of the proof of Proposition 5, and Proposition 5.
--
--   **Formalization Note** The paper's $\pi$ is the structure field `fut`; `Real.pi` is never used. The review $R=0$ is the constructor `Z`. Posteriors are defined by Bayes' rule, never by their closed forms, and the equilibrium ransom is not defined at all: theorems state it as the greatest element of the set of ransoms at which settling prevails. Ties in the selection rule are resolved for settling, as in the proof of Proposition 2 ("$\pi_s\ge\pi_c$"). The hypothesis $0<p<a\theta$ is not on the page; it makes $\rho\in(0,1)$, which the paper's closed forms use. The game fixes $g=1$ for the seller's payoffs: Proposition 5 is posed for penalties $b\ge\underline b$, under which (Proposition 4) genuine reviews are kept.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), pp. 6–13, §3, §4.2–§4.3; pp. 20–21, §5, Proposition 4, (5); pp. 40–42, Proofs of Propositions 4–5, (21); pp. 51–52, Proof of Proposition 13, (38)

import Mathlib

namespace ReviewBlackmail.SemiDec

/-- The publicly observed review `R ∈ {N, 0, P}` (§3, p. 7): `N` negative, `Z` no review (the
paper's `R = 0`), `P` positive. -/
inductive Review
  | N
  | Z
  | P
  deriving DecidableEq

/-- Product quality `q ∈ {l, h}` (§3, p. 7). -/
inductive Quality
  | l
  | h
  deriving DecidableEq

/-- The seller's response to a malicious negative review under the semi-decentralized
mechanism: settle (`s`, pay the ransom), do nothing (`n`), remove it through the mechanism (`d`). -/
inductive Resp
  | s
  | n
  | d
  deriving DecidableEq

/-- One instance of the model of §3 under the semi-decentralized mechanism: prior `a`, probability
`θ` of a positive experience with a high-quality product, probability `β` that the consumer is
malicious, price `p`, timeliness `γ`, accuracy `δ`, penalty `b`, and the seller's future payoff
`fut` (the paper's `π`, a function of the market's posterior belief). -/
structure Model where
  a : ℝ
  θ : ℝ
  β : ℝ
  p : ℝ
  γ : ℝ
  δ : ℝ
  b : ℝ
  fut : ℝ → ℝ

namespace Model

variable (M : Model)

/-- Standing assumptions (§3, pp. 7–9): `a, θ, β ∈ (0, 1)`; `π` nonnegative, convex and strictly
increasing on `[0, 1]`; `γ, δ ∈ [0, 1]`; `b ≥ 0`; and the disclosed `0 < p < aθ`, under which the
regular consumer buys with a probability in `(0, 1)`. -/
def Standing : Prop :=
  0 < M.a ∧ M.a < 1 ∧ 0 < M.θ ∧ M.θ < 1 ∧ 0 < M.β ∧ M.β < 1 ∧
  (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.fut x) ∧
  ConvexOn ℝ (Set.Icc (0 : ℝ) 1) M.fut ∧ StrictMonoOn M.fut (Set.Icc (0 : ℝ) 1) ∧
  0 ≤ M.γ ∧ M.γ ≤ 1 ∧ 0 ≤ M.δ ∧ M.δ ≤ 1 ∧ 0 ≤ M.b ∧
  0 < M.p ∧ M.p < M.a * M.θ

/-- Probability that a regular consumer buys: `F̄(p/(aθ)) = P(aθ vⱼ − p ≥ 0) = 1 − p/(aθ)` for
`vⱼ` standard uniform (p. 7), valid because `0 < p < aθ`. -/
noncomputable def buyProb : ℝ := 1 - M.p / (M.a * M.θ)

/-- Likelihood `P(R | q)` of each review given the quality, when a malicious negative review stays
visible with probability `m` and a genuine negative review stays visible with probability `g`.
A malicious consumer (probability `β`) always buys and posts `N`; a regular consumer buys with
probability `ρ = buyProb`, then posts `P` with probability `θ` (only if `q = h`) and `N` otherwise.
A removed review is observed as no review `Z`. -/
noncomputable def lik (m g : ℝ) : Quality → Review → ℝ
  | .h, .N => M.β * m + (1 - M.β) * M.buyProb * (1 - M.θ) * g
  | .l, .N => M.β * m + (1 - M.β) * M.buyProb * g
  | .h, .P => (1 - M.β) * M.buyProb * M.θ
  | .l, .P => 0
  | .h, .Z => M.β * (1 - m) +
      (1 - M.β) * ((1 - M.buyProb) + M.buyProb * (1 - M.θ) * (1 - g))
  | .l, .Z => M.β * (1 - m) + (1 - M.β) * ((1 - M.buyProb) + M.buyProb * (1 - g))

/-- The market's posterior belief that the quality is high after observing `R`, by Bayes' rule
from the prior `a` and the likelihoods `lik m g`. The paper's `a^i_R` is `post (vis i) 1 R`
(genuine reviews kept), and its `a^{sd}_R` of (38) is `post 0 γ R`. -/
noncomputable def post (m g : ℝ) (R : Review) : ℝ :=
  M.a * M.lik m g .h R / (M.a * M.lik m g .h R + (1 - M.a) * M.lik m g .l R)

/-- Probability that a malicious negative review stays visible under each response: settled
reviews are removed (`0`), ignored ones stay (`1`), and reviews removed through the mechanism are
reinstated when the platform judges immediately and wrongly (`γ(1 − δ)`). -/
noncomputable def vis : Resp → ℝ
  | .s => 0
  | .n => 1
  | .d => M.γ * (1 - M.δ)

/-- Seller's payoff from response `j` to a malicious review demanding ransom `r` when the market
believes the response is `i` (genuine reviews kept). Settling pays `π(a^i_0) − r`; doing nothing
pays `π(a^i_N)`; the mechanism pays
`(1 − γ(1 − δ))π(a^i_0) + γ(1 − δ)π(a^i_N) − (1 − δ)b`. -/
noncomputable def pay (i j : Resp) (r : ℝ) : ℝ :=
  match j with
  | .s => M.fut (M.post (M.vis i) 1 .Z) - r
  | .n => M.fut (M.post (M.vis i) 1 .N)
  | .d => (1 - M.γ * (1 - M.δ)) * M.fut (M.post (M.vis i) 1 .Z) +
      M.γ * (1 - M.δ) * M.fut (M.post (M.vis i) 1 .N) - (1 - M.δ) * M.b

/-- `i` is an equilibrium response at ransom `r`: no response is more profitable for the seller
given that the market believes he plays `i` (§4.2, p. 12). -/
def IsEq (i : Resp) (r : ℝ) : Prop := ∀ j, M.pay i j r ≤ M.pay i i r

/-- Settling is an equilibrium at ransom `r` and prevails: no other equilibrium gives the seller a
strictly higher payoff (selection rule, p. 13; ties resolved for settling). -/
def SettlePrevails (r : ℝ) : Prop :=
  M.IsEq .s r ∧ ∀ i, M.IsEq i r → M.pay i i r ≤ M.pay .s .s r

/-- The malicious consumer purchases iff some ransom at which settling prevails exceeds the price
(§4.3, p. 13). -/
def Purchases : Prop := ∃ r, M.SettlePrevails r ∧ M.p < r

/-- The penalty threshold `b̲ := (1 − γ)[π(a) − π(a^s_N)]` of Proposition 4. -/
noncomputable def bLow : ℝ := (1 - M.γ) * (M.fut M.a - M.fut (M.post 0 1 .N))

/-- Under the belief `ij = sn` (settle malicious, keep genuine), removing a genuine negative review
through the mechanism is not profitable: condition (21), p. 41. -/
def KeepGenuineBR : Prop :=
  (1 - M.γ) * M.fut (M.post 0 1 .Z) + M.γ * M.fut (M.post 0 1 .N) - M.b ≤
    M.fut (M.post 0 1 .N)

/-- Under the belief `ij = sd` (settle malicious, remove genuine), keeping a genuine negative
review is not profitable (proof of Proposition 13, p. 52), with the posteriors `a^{sd}_R` of (38), p. 51. -/
def RemoveGenuineBR : Prop :=
  M.fut (M.post 0 M.γ .N) ≤
    (1 - M.γ) * M.fut (M.post 0 M.γ .Z) + M.γ * M.fut (M.post 0 M.γ .N) - M.b

end Model

end ReviewBlackmail.SemiDec


