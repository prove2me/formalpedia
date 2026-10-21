-- Prove2me | Definitions.Def_ReputationLies_Matching_Model
-- name    : ReputationLies_Matching_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:15.208175+00:00
-- url     : https://prove2.me/theorems/6b9a4a9e-6307-41bc-b0c5-e660fea0e9a4
-- title:
--   §2–§4.2, pp. 8–15 — recommendation game: skills, bias, reputation loss L, outside option, strategy profiles, Bayes beliefs, perfect Bayesian equilibrium
-- statement:
--   This file sets up the recommendation game of Câmara, Jia and Raffiee.
--
--   **Primitives.** A focal candidate has skill $s \in \{s_L, s_H\}$ with $0 < s_L < s_H < 1$; the skill is high with probability $p \in (0,1)$, so the average skill is
--   $$\hat s = p\,s_H + (1-p)\,s_L .$$
--   An adviser with reputation $r > 0$ privately knows $s$ and a personal bias $b$, drawn from a continuous distribution with CDF $Z$ and full support on $B = [0,1]$. After a successful hire (a recommended high-skilled candidate is hired) his reputation becomes $r + g(r)$ with $g(r) > 0$; after an unsuccessful hire (a recommended low-skilled candidate is hired) it becomes $r - c(r)$ with $c(r) \in (0, r)$; otherwise it stays at $r$. His reputation payoff is $v(\tilde r)$, with $v(0)=0$ and $v' > 0$. The loss from an unsuccessful hire is eq. (1),
--   $$L(r) = v(r) - v\big(r - c(r)\big),$$
--   and Assumption (A1) states $L'(r) > 0$. The firm privately observes the value $x$ of an outside candidate, drawn from a continuously differentiable CDF $F$ with density $f$ and full support on $X = [0,1]$.
--
--   **Derived quantities.** For a bias threshold $b^*$, the belief after a recommendation (eq. (2)) is
--   $$s_R(b^*) = \frac{p\,s_H + (1-p)(1-Z(b^*))\,s_L}{p + (1-p)(1-Z(b^*))},$$
--   the benefit from lying at the threshold (left-hand side of eq. (12)) is $b^*\,[F(s_R(b^*)) - F(s_L)]/F(s_R(b^*))$, and its largest value is eq. (13), $\bar B = [F(s_H) - F(s_L)]/F(s_H)$. The market is **top-heavy** (**bottom-heavy**) if $f$ is strictly increasing (decreasing). The hiring probability of the fair gamble that puts belief $s$ with probability $(\hat s - s_L)/(s - s_L)$ and belief $s_L$ otherwise is $\frac{\hat s - s_L}{s - s_L}F(s) + \big(1 - \frac{\hat s - s_L}{s - s_L}\big)F(s_L)$.
--
--   **Strategies and equilibrium.** A profile consists of the adviser's strategy $\sigma_A(b, s) \in \{R, NR\}$, the firm's hiring rule $\sigma_F(x, m)$, and the firm's beliefs $s_R, s_{NR}$ (expected skill after $R$ and after $NR$). Message probabilities, Bayes beliefs, and the hiring probability after each message are computed from the bias and outside-option laws. The adviser's expected utility of each message is given by eqs. (6)–(8):
--   $$U(NR, s) = b\,\Pr(\text{hire}\mid NR) + v(r),\qquad U(R, s) = \Pr(\text{hire}\mid R)\,[\,b + v(\tilde r_s)\,] + (1 - \Pr(\text{hire}\mid R))\,v(r),$$
--   with $\tilde r_{s_H} = r + g(r)$ and $\tilde r_{s_L} = r - c(r)$. A profile is an **equilibrium** at reputation $r$ (perfect Bayesian equilibrium with the page's tie-breaks) if:
--   1. every bias type $b \in [0,1]$ chooses a message maximizing its expected utility, and a low-skill type that is indifferent does not recommend (tie-break (ii));
--   2. every outside-option type $x \in [0,1]$ hires the focal candidate if and only if $x \le s_m$ (best reply with tie-break (i));
--   3. the beliefs lie in $[s_L, s_H]$, and they are given by Bayes' rule after every message sent with positive probability.
--
--   The ex-ante hiring probability of eq. (14) is $E[F(s_m)] = \Pr(m{=}R)\Pr(\text{hire}\mid R) + \Pr(m{=}NR)\Pr(\text{hire}\mid NR)$, and the lying probability is $\Pr(m = R \mid s = s_L)$.
--
--   This is the common model for every statement of the mission.
--
--   **Formalization Note.** The laws of $b$ and $x$ are probability measures $\mu_B$, $\mu_X$ on $\mathbb R$ with mass $1$ on $[0,1]$, no atoms, and strictly increasing CDFs on $[0,1]$ (full support). $Z$ and $F$ are their CDFs, and $f$ is the derivative of $F$ on $(0,1)$. $F$ is required to be $C^1$ on $[0,1]$ only: a CDF that is $C^1$ on all of $\mathbb R$ has $f(1) = 0$, which would make top-heavy markets impossible. $v$, $g$, $c$ are differentiable on $(0,\infty)$, the reputation domain $\mathbb R_{++}$. The paper takes pure strategies without loss of generality (footnotes 15–16); here they are Boolean functions (`true` = recommend / high skill / hire the focal candidate), required to be measurable so that the message and hiring probabilities are defined (this is a disclosed addition; equilibrium strategies are threshold rules, so nothing is lost). Best responses are imposed on the supports $[0,1]$ of $b$ and $x$. Off-path beliefs may be any expected skill in $[s_L, s_H]$. Eq. (7) is written with $v(r + g(r))$; the sentence leading into (7) on p. 36 misprints it as $v(1 + g(r))$.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), pp. 8–15 (PDF 10–17), §2 Model, eqs. (1)–(2), Assumption (A1), Definition (top-/bottom-heavy), p. 15; Appendix A, eqs. (6)–(8), (11), (13), (14), pp. 36–40 (PDF 38–42)

import Mathlib

namespace ReputationLies.Matching

open MeasureTheory Set

/-- The primitives of the recommendation game (§2, pp. 8–12): the two skill levels `sL < sH`, the
prior probability `p` of a high skill, the reputation gain `g` and loss `c`, the reputation payoff
`v`, the law `μB` of the adviser's bias `b` (CDF `Z`) and the law `μX` of the firm's outside option
`x` (CDF `F`). -/
structure Primitives where
  sL : ℝ
  sH : ℝ
  p : ℝ
  g : ℝ → ℝ
  c : ℝ → ℝ
  v : ℝ → ℝ
  μB : Measure ℝ
  μX : Measure ℝ

namespace Primitives

variable (P : Primitives)

/-- Eq. (1): the adviser's payoff loss from an unsuccessful hire, `L(r) = v(r) − v(r − c(r))`. -/
def L (r : ℝ) : ℝ := P.v r - P.v (r - P.c r)

/-- The CDF `Z` of the adviser's bias. -/
noncomputable def Z (b : ℝ) : ℝ := (P.μB (Iic b)).toReal

/-- The CDF `F` of the firm's outside option. -/
noncomputable def F (x : ℝ) : ℝ := (P.μX (Iic x)).toReal

/-- The average skill `ŝ = p sH + (1 − p) sL`. -/
def shat : ℝ := P.p * P.sH + (1 - P.p) * P.sL

/-- Eq. (2)/(11): the firm's belief after a recommendation when the adviser uses the bias threshold
`b∗`, `sR(b∗) = [p sH + (1 − p)(1 − Z(b∗)) sL] / [p + (1 − p)(1 − Z(b∗))]`. -/
noncomputable def sRof (b : ℝ) : ℝ :=
  (P.p * P.sH + (1 - P.p) * (1 - P.Z b) * P.sL) / (P.p + (1 - P.p) * (1 - P.Z b))

/-- Eq. (13): `B̄ = [F(sH) − F(sL)] / F(sH)`. -/
noncomputable def Bbar : ℝ := (P.F P.sH - P.F P.sL) / P.F P.sH

/-- The left-hand side of eq. (12): `b [F(sR(b)) − F(sL)] / F(sR(b))`. -/
noncomputable def lieGain (b : ℝ) : ℝ :=
  b * ((P.F (P.sRof b) - P.F P.sL) / P.F (P.sRof b))

/-- The standing assumptions of §2 (pp. 8–12): `0 < sL < sH < 1`, `p ∈ (0, 1)`; for `r > 0`,
`g(r) > 0` and `c(r) ∈ (0, r)`; `v(0) = 0` and `v′ > 0` on `(0, ∞)`; `v, g, c` differentiable on
`(0, ∞)`; Assumption (A1) `L′(r) > 0`; the bias law is a continuous probability law with full
support on `[0, 1]`; the outside-option law is a continuous probability law with full support on
`[0, 1]` whose CDF is continuously differentiable on `[0, 1]`. -/
def Standing : Prop :=
  0 < P.sL ∧ P.sL < P.sH ∧ P.sH < 1 ∧ 0 < P.p ∧ P.p < 1 ∧
  (∀ r, 0 < r → 0 < P.g r ∧ 0 < P.c r ∧ P.c r < r) ∧
  P.v 0 = 0 ∧ DifferentiableOn ℝ P.v (Ioi 0) ∧ (∀ r, 0 < r → 0 < deriv P.v r) ∧
  DifferentiableOn ℝ P.g (Ioi 0) ∧ DifferentiableOn ℝ P.c (Ioi 0) ∧
  (∀ r, 0 < r → 0 < deriv P.L r) ∧
  IsProbabilityMeasure P.μB ∧ P.μB (Icc 0 1) = 1 ∧ NullSingletonClass P.μB ∧
  StrictMonoOn P.Z (Icc 0 1) ∧
  IsProbabilityMeasure P.μX ∧ P.μX (Icc 0 1) = 1 ∧ NullSingletonClass P.μX ∧
  StrictMonoOn P.F (Icc 0 1) ∧ ContDiffOn ℝ 1 P.F (Icc 0 1)

/-- Definition, p. 15: a top-heavy outside market (the density `f = F′` is strictly increasing on
the interior of `X = [0, 1]`). -/
def TopHeavy : Prop := StrictMonoOn (deriv P.F) (Ioo 0 1)

/-- Definition, p. 15: a bottom-heavy outside market (the density `f = F′` is strictly decreasing
on the interior of `X = [0, 1]`). -/
def BottomHeavy : Prop := StrictAntiOn (deriv P.F) (Ioo 0 1)

/-- The hiring probability of the fair gamble on `{sL, s}` with mean `ŝ`: the message is `s` with
probability `(ŝ − sL)/(s − sL)` and `sL` otherwise, and the focal candidate is hired with
probability `F(·)` of the belief (eq. (14) for `sNR = sL`, `sR = s`). -/
noncomputable def gambleHire (s : ℝ) : ℝ :=
  (P.shat - P.sL) / (s - P.sL) * P.F s + (1 - (P.shat - P.sL) / (s - P.sL)) * P.F P.sL

end Primitives

/-- A pure-strategy profile at a fixed reputation, with the firm's beliefs. `Bool` encodes
`true` = recommend (`R`) / high skill / hire the focal candidate.
* `σA b hi`: does the adviser with bias `b` and a high-skilled (`hi = true`) or low-skilled
  candidate recommend?
* `σF x m`: does the firm with outside option `x`, after message `m` (`true` = `R`), hire the
  focal candidate?
* `sR`, `sNR`: the firm's beliefs (expected skill of the focal candidate) after `R` and `NR`. -/
structure Profile where
  σA : ℝ → Bool → Bool
  σF : ℝ → Bool → Bool
  sR : ℝ
  sNR : ℝ

variable (P : Primitives) (σ : Profile)

/-- `Pr(m = R | s)`: the probability that the adviser recommends, given the skill. -/
noncomputable def recProb (hi : Bool) : ℝ := (P.μB {b | σ.σA b hi = true}).toReal

/-- `Pr(m | s)`. -/
noncomputable def sendProb (hi m : Bool) : ℝ := if m then recProb P σ hi else 1 - recProb P σ hi

/-- `Pr(m)`, averaged over the skill. -/
noncomputable def msgProb (m : Bool) : ℝ :=
  P.p * sendProb P σ true m + (1 - P.p) * sendProb P σ false m

/-- Bayes' rule: `E[s | m]` under the adviser's strategy (meaningful when `Pr(m) > 0`). -/
noncomputable def bayesBelief (m : Bool) : ℝ :=
  (P.p * sendProb P σ true m * P.sH + (1 - P.p) * sendProb P σ false m * P.sL) / msgProb P σ m

/-- The probability that the firm hires the focal candidate after message `m`. -/
noncomputable def hireProb (m : Bool) : ℝ := (P.μX {x | σ.σF x m = true}).toReal

/-- Eqs. (6)–(8): the adviser's expected utility, at reputation `r` with bias `b` and a
high-skilled (`hi = true`) or low-skilled candidate, of sending message `m`. -/
noncomputable def utility (r b : ℝ) (hi m : Bool) : ℝ :=
  if m then
    hireProb P σ true * (b + (if hi then P.v (r + P.g r) else P.v (r - P.c r)))
      + (1 - hireProb P σ true) * P.v r
  else b * hireProb P σ false + P.v r

/-- The perfect Bayesian equilibrium of §2 (pp. 11–12) at reputation `r`, with the page's
tie-breaks: measurable strategies; every bias type in `B = [0, 1]` best-responds, and a
low-skilled type indifferent between `R` and `NR` does not recommend (tie-break (ii)); every
outside-option type in `X = [0, 1]` hires the focal candidate iff its belief is at least `x`
(best reply with tie-break (i)); beliefs are expected skills in `[sL, sH]`, given by Bayes' rule
after every message sent with positive probability. -/
def IsEquilibrium (r : ℝ) : Prop :=
  (∀ hi, Measurable fun b => σ.σA b hi) ∧ (∀ m, Measurable fun x => σ.σF x m) ∧
  (∀ b ∈ Icc (0 : ℝ) 1, ∀ hi m, utility P σ r b hi m ≤ utility P σ r b hi (σ.σA b hi)) ∧
  (∀ b ∈ Icc (0 : ℝ) 1,
      utility P σ r b false true = utility P σ r b false false → σ.σA b false = false) ∧
  (∀ x ∈ Icc (0 : ℝ) 1, (σ.σF x true = true ↔ x ≤ σ.sR) ∧ (σ.σF x false = true ↔ x ≤ σ.sNR)) ∧
  σ.sR ∈ Icc P.sL P.sH ∧ σ.sNR ∈ Icc P.sL P.sH ∧
  (0 < msgProb P σ true → σ.sR = bayesBelief P σ true) ∧
  (0 < msgProb P σ false → σ.sNR = bayesBelief P σ false)

/-- Eq. (14): the ex-ante probability that the focal candidate is hired, `E[F(s_m)]`. -/
noncomputable def exAnteHireProb : ℝ :=
  msgProb P σ true * hireProb P σ true + msgProb P σ false * hireProb P σ false

/-- The probability that an adviser with a low-skilled candidate lies (recommends). -/
noncomputable def lieProb : ℝ := recProb P σ false

end ReputationLies.Matching


