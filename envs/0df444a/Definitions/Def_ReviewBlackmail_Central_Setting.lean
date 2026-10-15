-- Prove2me | Definitions.Def_ReviewBlackmail_Central_Setting
-- name    : ReviewBlackmail_Central_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:12.927736+00:00
-- url     : https://prove2.me/theorems/23865232-ec2a-4a29-a13f-f8981f38411c
-- title:
--   §3, §4.1–§4.3 — the review-blackmail game under centralized dispute resolution: Bayes posteriors $a^i_R$, seller payoffs, equilibrium, seller-preferred selection, purchase rule
-- statement:
--   This file sets up the one-shot review-blackmail game of Papanastasiou, Yang and Zhang under **centralized dispute resolution**.
--
--   **Primitives.** A monopolist sells a product whose quality $q\in\{l,h\}$ is unobservable; the prior probability of high quality is $a\in(0,1)$. A consumer who buys a high-quality product has gross utility $v_j$ with probability $\theta\in(0,1)$ and $0$ otherwise, where $v_j$ is standard uniform; a low-quality product always gives $0$. With probability $\beta\in(0,1)$ the consumer is *malicious*: he buys, posts a negative review $N$ and demands a ransom $r$ for removing it. Otherwise he is *regular*: at price $p$ he buys iff $a\theta v_j-p\ge 0$, i.e. with probability
--   $$\rho=\bar F\Big(\frac{p}{a\theta}\Big)=1-\frac{p}{a\theta},$$
--   and posts a truthful review, positive ($P$) after a positive experience and negative ($N$) after a zero one; no purchase means no review, written $R=0$. After observing the review the market forms the posterior $a'$ by Bayes' rule and the seller earns $\pi(a')$, where $\pi$ is nonnegative, convex and strictly increasing on $[0,1]$. Reporting a review to the platform's centralized mechanism costs the seller a hassle cost $c\ge 0$; the platform removes a reported malicious review only if it investigates immediately (probability $\gamma$) and judges correctly (probability $\delta$), i.e. with the **mechanism efficiency** $e=\gamma\delta$.
--
--   **Standing assumptions** (`Standing`): $a,\theta,\beta\in(0,1)$; $\pi\ge 0$, convex and strictly increasing on $[0,1]$; $c\ge 0$; and $0<p<a\theta$.
--
--   **Responses and posteriors.** Facing a ransom demand the seller can settle ($s$), do nothing ($n$) or report to the mechanism ($c$). If the market believes the seller's response is $i$, a malicious review stays visible with probability $m_i$, where $m_s=0$, $m_n=1$, $m_c=1-e$ (`keep e i`). The review likelihoods given quality are
--   $$\Pr(P\mid h)=(1-\beta)\rho\theta,\quad \Pr(P\mid l)=0,$$
--   $$\Pr(N\mid h)=\beta m_i+(1-\beta)\rho(1-\theta),\quad \Pr(N\mid l)=\beta m_i+(1-\beta)\rho,$$
--   $$\Pr(0\mid q)=\beta(1-m_i)+(1-\beta)(1-\rho)\quad(q=l,h),$$
--   and the posterior is Bayes' rule
--   $$a^i_R=\frac{a\Pr(R\mid h)}{a\Pr(R\mid h)+(1-a)\Pr(R\mid l)}.$$
--
--   **Payoffs and equilibrium.** When the market believes $i$ and the seller actually plays $j$ against ransom $r$, his payoff is $\pi(a^i_0)-r$ for $j=s$, $\pi(a^i_N)$ for $j=n$, and $e\,\pi(a^i_0)+(1-e)\pi(a^i_N)-c$ for $j=c$. A response $i$ is an **equilibrium** at ransom $r$ if no $j$ gives a strictly higher payoff given the market's belief $i$. **Settling prevails** at $r$ if settling is an equilibrium and no equilibrium gives the seller a strictly higher payoff than settling (the seller-preferred equilibrium prevails; ties go to settling). The malicious consumer **purchases** iff some ransom $r$ at which settling prevails exceeds the price, $r>p$. The equilibrium ransom $r^*$ is the greatest ransom at which settling prevails.
--
--   These objects are shared by every statement of the mission: Lemma 2, the ordering of posteriors, Propositions 1–2 and Corollary 1.
--
--   **Formalization Note** The paper's $R=0$ is the constructor `Z`, its $\pi(\cdot)$ is the field `π`, and $a^i_R$ is `M.post (keep e i) R`. The posterior is defined by Bayes' rule from the likelihood table (proof of Lemma 2, pp. 35–36), never by its closed form. The uniform valuation enters only through $\rho=1-p/(a\theta)$, which equals $\bar F(p/(a\theta))$ because $0<p<a\theta$; the bounds $0<p<a\theta$ are an implicit assumption of the paper made explicit (they make $\rho\in(0,1)$, which Lemma 2 needs). The timeliness $\gamma$ and accuracy $\delta$ enter only through their product $e$; the theorems that the paper states in $\gamma,\delta$ instantiate $e=\gamma\delta$.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), pp. 6–13, §3, §4.1–§4.3; proof of Lemma 2, pp. 35–36

import Mathlib

namespace ReviewBlackmail.Central

/-- The product's quality, `q ∈ {l, h}` (§3, p. 7). -/
inductive Quality
  | l
  | h
  deriving DecidableEq

/-- The publicly visible review: negative `N`, positive `P`, or no review `Z`
(the paper's `R = 0`) (§3, p. 7). -/
inductive Review
  | N
  | Z
  | P
  deriving DecidableEq

/-- The seller's response to a malicious consumer's ransom demand under centralized dispute
resolution (§3, pp. 7–8): settle and pay the ransom (`s`), refuse and do nothing (`n`), or refuse
and report the review to the platform's centralized mechanism (`c`). -/
inductive Resp
  | s
  | n
  | c
  deriving DecidableEq

/-- One instance of the review-blackmail model under centralized dispute resolution (§3).
`a` is the prior probability of high quality, `θ` the probability that a high-quality product
gives a positive experience, `β` the probability that the consumer is malicious, `p` the price,
`π` the seller's future payoff as a function of the market's posterior belief, and `c` the
seller's hassle cost of using the mechanism. -/
structure Model where
  a : ℝ
  θ : ℝ
  β : ℝ
  p : ℝ
  π : ℝ → ℝ
  c : ℝ

namespace Model

variable (M : Model)

/-- The standing assumptions of §3 (pp. 7–8): `a, θ, β ∈ (0,1)`; `π` nonnegative, convex and
strictly increasing on `[0,1]`; hassle cost `c ≥ 0`; and the disclosed price range `0 < p < aθ`,
which makes the regular consumer's purchase probability `1 - p/(aθ)` lie in `(0,1)`. -/
def Standing : Prop :=
  0 < M.a ∧ M.a < 1 ∧ 0 < M.θ ∧ M.θ < 1 ∧ 0 < M.β ∧ M.β < 1 ∧
  (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.π x) ∧
  ConvexOn ℝ (Set.Icc (0 : ℝ) 1) M.π ∧ StrictMonoOn M.π (Set.Icc (0 : ℝ) 1) ∧
  0 ≤ M.c ∧ 0 < M.p ∧ M.p < M.a * M.θ

/-- The regular consumer's purchase probability `F̄(p/(aθ)) = P(aθ v_j - p ≥ 0)` for the
standard uniform valuation `v_j ~ U[0,1]` (§3, p. 7); equal to `1 - p/(aθ)` because
`0 < p < aθ`. -/
noncomputable def buyProb : ℝ := 1 - M.p / (M.a * M.θ)

/-- The likelihood `P(R | q)` of the visible review `R` given quality `q`, when a malicious
consumer's negative review stays visible with probability `m` (§3; proof of Lemma 2, pp. 35–36).
A consumer is malicious with probability `β` (buys, posts `N`, which stays visible with
probability `m` and is otherwise removed, giving `R = 0`); otherwise regular, buying with
probability `ρ = buyProb` and reporting a positive experience (probability `θ` under `h`, `0`
under `l`) as `P` and a zero experience as `N`; no purchase gives `R = 0`. -/
noncomputable def lik (q : Quality) (m : ℝ) : Review → ℝ
  | .P => match q with
    | .h => (1 - M.β) * M.buyProb * M.θ
    | .l => 0
  | .N => match q with
    | .h => M.β * m + (1 - M.β) * M.buyProb * (1 - M.θ)
    | .l => M.β * m + (1 - M.β) * M.buyProb
  | .Z => M.β * (1 - m) + (1 - M.β) * (1 - M.buyProb)

/-- The market's posterior belief that quality is high after observing review `R`, by Bayes'
rule with prior `a`, when a malicious review stays visible with probability `m`. -/
noncomputable def post (m : ℝ) (R : Review) : ℝ :=
  M.a * M.lik .h m R / (M.a * M.lik .h m R + (1 - M.a) * M.lik .l m R)

end Model

/-- The probability that a malicious consumer's negative review stays visible when the market
believes the seller's response is `i`, for mechanism efficiency `e = γδ` (§3, pp. 8–9; proof of
Lemma 2, p. 36): settling removes it (`0`), doing nothing keeps it (`1`), reporting it keeps it
unless the platform judges immediately and correctly (`1 - e`). The paper's `a^i_R` is
`M.post (keep e i) R`. -/
def keep (e : ℝ) : Resp → ℝ
  | .s => 0
  | .n => 1
  | .c => 1 - e

namespace Model

variable (M : Model)

/-- The seller's payoff (§4.2, p. 12) from response `j` to a malicious review demanding ransom
`r`, when the market believes the seller's response is `i` and the mechanism efficiency is `e`:
settling gives `π(a^i_0) - r`, doing nothing `π(a^i_N)`, and reporting
`e π(a^i_0) + (1 - e) π(a^i_N) - c`. -/
noncomputable def pay (e : ℝ) (i j : Resp) (r : ℝ) : ℝ :=
  match j with
  | .s => M.π (M.post (keep e i) .Z) - r
  | .n => M.π (M.post (keep e i) .N)
  | .c => e * M.π (M.post (keep e i) .Z) + (1 - e) * M.π (M.post (keep e i) .N) - M.c

/-- `i` is an equilibrium response to ransom `r` (§4.2, p. 12): given that the market believes
the seller plays `i`, no response `j` gives the seller a strictly higher payoff. -/
def IsEq (e : ℝ) (i : Resp) (r : ℝ) : Prop :=
  ∀ j : Resp, M.pay e i j r ≤ M.pay e i i r

/-- Settling prevails at ransom `r` (§4.2, p. 13, "the equilibrium which maximizes the seller's
expected payoff prevails"): settling is an equilibrium, and no equilibrium gives the seller a
strictly higher payoff (ties are resolved in favour of settling). -/
def SettlePrevails (e : ℝ) (r : ℝ) : Prop :=
  M.IsEq e .s r ∧ ∀ i : Resp, M.IsEq e i r → M.pay e i i r ≤ M.pay e .s .s r

/-- The malicious consumer's purchase rule (§4.3, p. 13): he purchases iff there is a ransom `r`
that the seller accepts in the prevailing equilibrium and that exceeds the price, `r > p`. -/
def Purchases (e : ℝ) : Prop :=
  ∃ r : ℝ, M.SettlePrevails e r ∧ M.p < r

end Model

end ReviewBlackmail.Central


