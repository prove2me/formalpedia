-- Prove2me | Definitions.Def_MatchCongestion_Welfare_Setting
-- name    : MatchCongestion_Welfare_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:00.494995+00:00
-- url     : https://prove2.me/theorems/a4ff87c2-f37c-4b06-803d-4acb5b1a45b4
-- title:
--   §3–§4.3, pp. 623–628 — parameters, Assumption 1, payoffs (2), (5), best responses (3)–(4), consistency (6)–(7), Definition 1, equations (13)–(14)
-- statement:
--   This file sets up the stationary mean-field model of a congested two-sided matching market (Arnosti, Johari and Kanoria, §3–§4.3).
--
--   **Parameters.** A market is described by $r>0$, the number of applicants per employer; $\beta\in(0,1]$, the probability that an applicant is qualified (compatible) for a given employer; $c_a$, the cost of sending one application; and $c_s$, the cost of screening one applicant. The standing hypothesis is Assumption 1,
--   $$\max(c_a, c_s) < \beta,$$
--   together with $0<r$, $0<\beta\le 1$, $0<c_a$, $0<c_s$. The reduced screening cost is $c'_s = c_s/\beta$, as in (1).
--
--   **The Poisson ratio.** For $x\in\mathbb R$ let $E(x) = (1-e^{-x})/x$ if $x\neq 0$ and $E(0)=1$. For $X\sim\mathrm{Poisson}(x)$ this is $P(X>0)/\mathbb E[X]$, the ratio appearing in the consistency conditions.
--
--   **Applicants.** An applicant who sends a Poisson($m$) number of applications, each of which becomes an offer with probability $p$, has expected payoff (2)
--   $$W_a(m,p) = 1 - e^{-mp} - c_a m,$$
--   and the best response (3) is $\mathcal M(p) = 0$ if $p\le c_a$ and $\mathcal M(p) = \frac1p\log\frac{p}{c_a}$ if $p>c_a$.
--
--   **Employers.** Given the availability $q$ of applicants, the employer best-response correspondence (4) is
--   $$\mathcal A(q) = \{0\}\ (q<c'_s),\qquad [0,1]\ (q=c'_s),\qquad \{1\}\ (q>c'_s),$$
--   where $\alpha\in[0,1]$ is the probability of screening. An employer who screens with probability $\alpha$ has expected payoff (5)
--   $$W_e(\alpha,m,q) = \alpha\bigl(1-e^{-rm\beta q}\bigr)\bigl(1-c'_s/q\bigr).$$
--
--   **Steady state and equilibrium.** A pair $(p,q)$ is a mean-field steady state of the strategies $(m,\alpha)$ if it satisfies the consistency conditions (6) and (7):
--   $$q = E(mp),\qquad p = \alpha\beta\, E(rm\beta q).$$
--   A mean-field equilibrium (Definition 1) is a pair $(m^*,\alpha^*)$ admitting a steady state $(p,q)$ with $m^* = \mathcal M(p)$ and $\alpha^*\in\mathcal A(q)$.
--
--   **The equations of Theorem 2.** For $p\in\mathbb R$, equation (13) is $r(1-c_a/p) = 1 - e^{-(r\beta/p)(1-c_a/p)}$ and equation (14) is $1 - c_a/p + (c_s/\beta)\log(c_a/p) = 0$; both are recorded as properties of $p$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The positivity $0<r$, $0<\beta\le1$, $0<c_a$, $0<c_s$ is added to Assumption 1; the paper uses it without listing it. The page leaves (6) and (7) undefined at $mp=0$ and $rm\beta q=0$; they are written through $E$ with $E(0)=1$, because Lean's convention $x/0=0$ would make $(m,\alpha,p,q)=(0,0,0,0)$ a spurious equilibrium. $\mathcal A$ is a set, not a function. Definition 1 composes $\mathcal M$ and $\mathcal A$ with the steady-state maps $\mathcal P,\mathcal Q$ of Proposition 2; here the steady state is existentially quantified, which is equivalent by Proposition 2. $\log$ is the natural logarithm.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), pp. 623–628, Assumption 1, (1)–(7), Definition 1, Theorem 2 (13)–(14)

import Mathlib

namespace MatchCongestion.Welfare

/-! The stationary mean-field model of Arnosti, Johari, Kanoria, *Managing Congestion in Matching
Markets*, M&SOM 23(3):620–636 (2021), §3 and §4.1–4.3, pp. 623–627, together with the two root
equations (13), (14) of Theorem 2, p. 628.

**Formalization Note.**
* `Params.Standing` is Assumption 1 (p. 624, `max(c_a, c_s) < β`) plus the positivity the paper uses
  without stating it as an assumption: `0 < r` (p. 624), `0 < β ≤ 1` (β is a probability),
  `0 < c_a`, `0 < c_s` (the paper only says "costs").
* `E x = (1 - e^{-x}) / x` for `x ≠ 0` and `E 0 = 1` (its continuous extension). The consistency
  conditions (6), (7) are undefined on the page at `mp = 0`, resp. `rmβq = 0`; Lean's `x / 0 = 0`
  would create the spurious mean-field equilibrium `(m, α) = (0, 0)`.
* `Acorr` is the employer best-response *correspondence* (4), a set of probabilities.
* `IsMFE` reads Definition 1 as: there is a mean-field steady state `(p, q)` of `(m, α)` with
  `m = M(p)` and `α ∈ A(q)`. By Proposition 2 (unique steady state) this is Definition 1.
* `log` is the natural logarithm `Real.log`. -/

/-- Market primitives (p. 623–624): `r` applicants per employer, compatibility probability `β`,
application cost `ca` (c_a), screening cost `cs` (c_s). -/
structure Params where
  r : ℝ
  β : ℝ
  ca : ℝ
  cs : ℝ

/-- Assumption 1 (p. 624), `max(c_a, c_s) < β`, together with the disclosed positivity
`0 < r`, `0 < β ≤ 1`, `0 < c_a`, `0 < c_s`. -/
def Params.Standing (P : Params) : Prop :=
  max P.ca P.cs < P.β ∧ 0 < P.r ∧ 0 < P.β ∧ P.β ≤ 1 ∧ 0 < P.ca ∧ 0 < P.cs

/-- The reduced screening cost `c′_s = c_s / β`, (1), p. 624. -/
noncomputable def csp (P : Params) : ℝ := P.cs / P.β

/-- `E x = (1 - e^{-x}) / x` for `x ≠ 0`, extended continuously by `E 0 = 1`. This is
`P(X > 0) / E[X]` for `X ∼ Poisson(x)`, the ratio in (6) and (7), p. 626. -/
noncomputable def E (x : ℝ) : ℝ := if x = 0 then 1 else (1 - Real.exp (-x)) / x

/-- Applicant expected payoff (2), p. 625: `W_a(m, p) = 1 - e^{-mp} - c_a m`. -/
noncomputable def Wa (P : Params) (m p : ℝ) : ℝ := 1 - Real.exp (-(m * p)) - P.ca * m

/-- Applicant best response (3), p. 625: `M(p) = 0` if `p ≤ c_a`, and `(1/p) log(p/c_a)` if
`p > c_a`. -/
noncomputable def Mbr (P : Params) (p : ℝ) : ℝ :=
  if p ≤ P.ca then 0 else (1 / p) * Real.log (p / P.ca)

/-- Employer best-response correspondence (4), p. 626: `A(q) = {0}` if `q < c′_s`, `[0, 1]` if
`q = c′_s`, `{1}` if `q > c′_s`. -/
noncomputable def Acorr (P : Params) (q : ℝ) : Set ℝ :=
  if q < csp P then {0} else if q = csp P then Set.Icc 0 1 else {1}

/-- Employer expected payoff (5), p. 626: `W_e(α, m, q) = α (1 - e^{-rmβq}) (1 - c′_s/q)`. -/
noncomputable def We (P : Params) (α m q : ℝ) : ℝ :=
  α * (1 - Real.exp (-(P.r * m * P.β * q))) * (1 - csp P / q)

/-- Mean-field steady state, p. 626: `(p, q)` solves the consistency equations
(6) `q = (1 - e^{-mp}) / (mp)` and (7) `p = αβ (1 - e^{-rmβq}) / (rmβq)`, both written through `E`. -/
def IsMFSS (P : Params) (m α p q : ℝ) : Prop :=
  q = E (m * p) ∧ p = α * P.β * E (P.r * m * P.β * q)

/-- Mean-field equilibrium, Definition 1, p. 627: `m = M(P(m, α))` and `α ∈ A(Q(m, α))`, with the
steady state `(P(m, α), Q(m, α))` of Proposition 2 written as an existentially quantified `(p, q)`. -/
def IsMFE (P : Params) (m α : ℝ) : Prop :=
  ∃ p q : ℝ, IsMFSS P m α p q ∧ m = Mbr P p ∧ α ∈ Acorr P q

/-- Equation (13) of Theorem 2, p. 628, as a predicate on `p`:
`r (1 - c_a/p) = 1 - e^{-(rβ/p)(1 - c_a/p)}`. -/
def Eq13 (P : Params) (p : ℝ) : Prop :=
  P.r * (1 - P.ca / p) = 1 - Real.exp (-(P.r * P.β / p) * (1 - P.ca / p))

/-- Equation (14) of Theorem 2, p. 628, as a predicate on `p`:
`1 - c_a/p + (c_s/β) log(c_a/p) = 0`. -/
def Eq14 (P : Params) (p : ℝ) : Prop :=
  1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p) = 0

end MatchCongestion.Welfare


