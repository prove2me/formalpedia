-- Prove2me | Definitions.Def_FlexGroupBuy_REE_Model
-- name    : FlexGroupBuy_REE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:05.687874+00:00
-- url     : https://prove2.me/theorems/6d0b9774-9344-41e3-a8b9-84ab57826029
-- title:
--   §3.1, §4.1, Online Appendix pp. 2–5 — two-segment group buying with waiting cost: wG, binding prices, tipping state, long-run average profit πG
-- statement:
--   A monopolist sells a regular product of quality $1$ and a group-buying premium product of quality $\theta$ to customers arriving as a Poisson process of rate $\lambda$. A fraction $\gamma$ of customers are high-end, with valuation $H$; the rest are low-end, with valuation $L$. A group-buying campaign completes when $N$ customers have signed up; a customer arriving when $n$ further sign-ups are still needed (the *pledge-to-go state*, $1\le n\le N$) waits in expectation $w^G(n)$ and incurs a waiting cost $c$ per unit time. The **standing assumptions** of §3.1 are
--   $$
--   H>L>0,\qquad 0<\gamma<1,\qquad \lambda>0,\qquad c>0,\qquad \theta>1 .
--   $$
--
--   When high-end customers sign up first and both segments sign up once the state has dropped to the **tipping state** $\bar x^G\in[0,N]$, the expected waiting time is
--   $$
--   w^G(n)=\begin{cases}\dfrac{n-1}{\lambda}, & n\le \bar x^G,\\[4pt] \dfrac{\bar x^G}{\lambda}+\dfrac{n-\bar x^G-1}{\gamma\lambda}, & n>\bar x^G;\end{cases}
--   $$
--   the low-end-first variant $w^{II}$ has $(1-\gamma)\lambda$ in place of $\gamma\lambda$. With $r^G=L$ (the regular price at which low-end customers are indifferent), the two candidate premium prices are
--   $$
--   \bar p^G_1(\bar x^G)=\theta L-c\,w^G(\bar x^G),\qquad \bar p^G_2(\bar x^G)=(\theta-1)H+L-c\,w^G(N),
--   $$
--   and $\bar x^G_1=N-1+\gamma-(\theta-1)(H-L)\gamma\lambda/c$. The group-buying price is $p^G(0)=\bar p^G_2(0)$ and $p^G(\bar x^G)=\min\{\bar p^G_1(\bar x^G),\bar p^G_2(\bar x^G)\}$ for $\bar x^G>0$. The firm's **long-run average profit** is the renewal-cycle ratio
--   $$
--   \pi^G(\bar x^G)=\frac{\bigl[p^G\gamma\lambda+r^G(1-\gamma)\lambda\bigr]\dfrac{N-\bar x^G}{\gamma\lambda}+\bigl[p^G\lambda\bigr]\dfrac{\bar x^G}{\lambda}}{\dfrac{\bar x^G}{\lambda}+\dfrac{N-\bar x^G}{\gamma\lambda}},
--   $$
--   with $p^G=p^G(\bar x^G)$. The batch-size thresholds are $\bar N_1=(\theta-1)(1-\gamma)L\lambda/c+1-\gamma$ and $\bar N_2=(\theta-1)(H-L)\gamma\lambda/c+1-\gamma$, and $\pi^G_1$ is the closed form printed on Online Appendix p. 5. A tipping state is **optimal** if it lies in $[0,N]$ and maximizes $\pi^G$ over $[0,N]$.
--
--   These objects are the firm's reduced pricing problem as the proof of Proposition 2 solves it; every theorem of the mission is stated about them.
--
--   **Formalization Note.** Parameters are bundled in `Params`, with `gam` $=\gamma$, `lam` $=\lambda$, `theta` $=\theta$; `Standing` is the conjunction above ($\lambda>0$ is implicit in the paper). The tipping state is real, as in the paper's appendix (footnote 1, Online Appendix p. 2). At $n=\bar x^G$ the waiting time takes the first branch, as printed. $p^G(0)=\bar p^G_2(0)$ because no low-end customer signs up at $\bar x^G=0$, so only ICH binds. The constraints IRH, IRL2 and ICL1, which the proof never checks, are not part of the model.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), pp. 10–13, §3.1, §4.1; Online Appendix pp. 2–5, proofs of Propositions 1 and 2

import Mathlib

namespace FlexGroupBuy.REE

/-- Parameters of the base model, §3.1 (pp. 10–11): valuations `H` (high end) and `L` (low end),
high-end share `gam` (γ), Poisson arrival rate `lam` (λ), waiting cost `c` per unit time, and quality
`theta` (θ) of the group-buying premium product (the regular product has quality 1). -/
structure Params where
  H : ℝ
  L : ℝ
  gam : ℝ
  lam : ℝ
  c : ℝ
  theta : ℝ

/-- Standing assumptions of §3.1: `H > L > 0`, `0 < γ < 1`, `λ > 0`, `c > 0`, `θ > 1`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.L ∧ P.L < P.H ∧ 0 < P.gam ∧ P.gam < 1 ∧ 0 < P.lam ∧ 0 < P.c ∧ 1 < P.theta

/-- Case I (high-end customers sign up first) expected waiting time at pledge-to-go state `n`
when the tipping state is `x` (Online Appendix p. 3): `(n - 1)/λ` for `n ≤ x`, and
`x/λ + (n - x - 1)/(γλ)` for `x < n`. -/
noncomputable def wG (P : Params) (x n : ℝ) : ℝ :=
  if n ≤ x then (n - 1) / P.lam else x / P.lam + (n - x - 1) / (P.gam * P.lam)

/-- Case II (low-end customers sign up first) expected waiting time (Online Appendix p. 3, proof of
Proposition 1): `(n - 1)/λ` for `n ≤ x`, and `x/λ + (n - x - 1)/((1 - γ)λ)` for `x < n`. -/
noncomputable def wII (P : Params) (x n : ℝ) : ℝ :=
  if n ≤ x then (n - 1) / P.lam else x / P.lam + (n - x - 1) / ((1 - P.gam) * P.lam)

/-- `p̄G1(x) = θL − c·wG(x)`: the price at which ICL2 binds at state `x`. -/
noncomputable def pbar1 (P : Params) (x : ℝ) : ℝ := P.theta * P.L - P.c * wG P x x

/-- `p̄G2(x) = (θ − 1)H + L − c·wG(N)`: the price at which ICH binds at state `N` (given `rG = L`). -/
noncomputable def pbar2 (P : Params) (N : ℕ) (x : ℝ) : ℝ :=
  (P.theta - 1) * P.H + P.L - P.c * wG P x N

/-- `x̄G1 = N − 1 + γ − (θ − 1)(H − L)γλ/c`. -/
noncomputable def xbar1 (P : Params) (N : ℕ) : ℝ :=
  (N : ℝ) - 1 + P.gam - (P.theta - 1) * (P.H - P.L) * P.gam * P.lam / P.c

/-- Uniform group-buying price as a function of the tipping state `x`: the largest price satisfying
ICH at state `N` and, when low-end customers sign up (`x > 0`), ICL2 at state `x`. At `x = 0` no
low-end customer signs up, so ICL2 is vacuous and only ICH binds (case (ii-1) of the proof of
Proposition 2); taking the minimum at `x = 0` as well would make case (ii-1) false. -/
noncomputable def pG (P : Params) (N : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then pbar2 P N 0 else min (pbar1 P x) (pbar2 P N x)

/-- Regular-product price: IRL1 binds, `rG = L`. -/
def rG (P : Params) : ℝ := P.L

/-- Long-run average profit as a function of the tipping state (second line of the display on Online
Appendix p. 4): revenue rates in the high-end-only phase (expected length `(N − x)/(γλ)`) and in the
both-segment phase (expected length `x/λ`), weighted by the expected phase lengths and divided by the
expected cycle length. -/
noncomputable def piG (P : Params) (N : ℕ) (x : ℝ) : ℝ :=
  ((pG P N x * P.gam * P.lam + rG P * (1 - P.gam) * P.lam) * ((N - x) / (P.gam * P.lam))
      + (pG P N x * P.lam) * (x / P.lam))
    / (x / P.lam + (N - x) / (P.gam * P.lam))

/-- `N̄1 = (θ − 1)(1 − γ)Lλ/c + 1 − γ`. -/
noncomputable def Nbar1 (P : Params) : ℝ :=
  (P.theta - 1) * (1 - P.gam) * P.L * P.lam / P.c + 1 - P.gam

/-- `N̄2 = (θ − 1)(H − L)γλ/c + 1 − γ`. -/
noncomputable def Nbar2 (P : Params) : ℝ :=
  (P.theta - 1) * (P.H - P.L) * P.gam * P.lam / P.c + 1 - P.gam

/-- `πG1`, Online Appendix p. 5. -/
noncomputable def piG1 (P : Params) (N : ℕ) : ℝ :=
  ((P.theta - 1) * (P.H - P.L) * P.L * (1 - P.gam) * P.gam * P.lam ^ 2
      + (P.theta - 1) * P.c * P.H * N * P.gam ^ 2 * P.lam
      + P.c * P.L * P.lam * (1 + P.theta * (1 - P.gam) * P.gam * N
          + P.gam ^ 2 * (N + 1) - 2 * P.gam)
      - P.c ^ 2 * P.gam * N * ((N : ℝ) - 2 + P.gam))
    / (P.c * (1 + P.gam * ((N : ℝ) - 2 + P.gam)) + (P.theta - 1) * (P.H - P.L) * (1 - P.gam) * P.gam * P.lam)

/-- `x` is an optimal tipping state: it lies in `[0, N]` and maximizes `piG` over `[0, N]`. -/
def IsOptimalTip (P : Params) (N : ℕ) (x : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) N ∧ ∀ y ∈ Set.Icc (0 : ℝ) N, piG P N y ≤ piG P N x

end FlexGroupBuy.REE


