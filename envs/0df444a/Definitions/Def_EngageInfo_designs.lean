-- Prove2me | Definitions.Def_EngageInfo_designs
-- name    : EngageInfo_designs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:03.797319+00:00
-- url     : https://prove2.me/theorems/c67fc054-efb8-4b60-bc77-822980957b11
-- title:
--   Signals $(\pi_h,\pi_l)$, signal probabilities and posteriors $\alpha_h,\alpha_l$; designs (3)
-- statement:
--   A **design** is a pair $\pi=(\pi_h,\pi_l)$ with $\pi_h=\Pr(h\mid H)$ and $\pi_l=\Pr(l\mid L)$. It is feasible if
--
--   $$0\le\pi_h\le1,\qquad 0\le\pi_l\le1,\qquad \pi_h\ge 1-\pi_l .$$
--
--   For a prior $\alpha^0$ the signal probabilities are $\Pr(h)=\alpha^0\pi_h+(1-\alpha^0)(1-\pi_l)$ and $\Pr(l)=\alpha^0(1-\pi_h)+(1-\alpha^0)\pi_l$, and the posteriors of the state $H$ are
--
--   $$\alpha_h=\frac{\alpha^0\pi_h}{\Pr(h)},\qquad \alpha_l=\frac{\alpha^0(1-\pi_h)}{\Pr(l)} .$$
--
--   A design **induces** $(a,b)$ if $\alpha_l=a$ and $\alpha_h=b$. It is **uninformative** if it is feasible and $\pi_h+\pi_l=1$. The design (3) for a target pair $(a,b)$ is
--
--   $$\pi_h=\frac{b(\alpha^0-a)}{\alpha^0(b-a)},\qquad \pi_l=\frac{(b-\alpha^0)(1-a)}{(1-\alpha^0)(b-a)} .$$
--
--   **Formalization Note** The posterior after a signal of probability $0$ is set to the prior $\alpha^0$ (Lean's $x/0=0$ would make it $0$); its weight in every expectation is $0$.
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, (2), p.6; posteriors αh ∈ [α⁰, 1], αl ∈ [0, α⁰], p.6; (3), p.7

import Mathlib

namespace EngageInfo

/-- **Binary signals, signal probabilities and Bayesian posteriors.**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §2, pp.6–7. (2), p.6:
"πh ≡ Pr(h|H) and πl ≡ Pr(l|L), where πh ≥ 1 − πl"; "let αh ∈ [α⁰, 1] and αl ∈ [0, α⁰] be the
updated probabilities for the state H, conditional on the realized signal h or l"; (3), p.7:
"πh = αh(α⁰ − αl)/(α⁰(αh − αl)) and πl = (αh − α⁰)(1 − αl)/((1 − α⁰)(αh − αl))".

A design is a pair `π = (π_h, π_l)`. `designs` is the set of feasible designs:
`π_h, π_l ∈ [0, 1]` and `π_h ≥ 1 − π_l`. For a prior `a0 = α⁰`,

* `probH a0 π = α⁰π_h + (1 − α⁰)(1 − π_l)` and `probL a0 π = α⁰(1 − π_h) + (1 − α⁰)π_l` are the
  probabilities of the signals `h` and `l`;
* `postH a0 π = α⁰π_h / Pr(h)` and `postL a0 π = α⁰(1 − π_h) / Pr(l)` are the posteriors `α_h`, `α_l`
  of the state H by Bayes' rule.

`Induces a0 π a b` says that `π` induces the posterior pair `(α_l, α_h) = (a, b)`;
`IsUninformative π` says `π` is feasible and `π_h + π_l = 1` (both posteriors equal the prior);
`designOf a0 a b` is the design (3) that induces `(a, b)`.

**Formalization Note** The posterior after a signal of probability `0` is set to the prior `α⁰`
(Lean's `x / 0 = 0` would otherwise make it `0`); its weight in every expectation is `0`. Designs
are pairs in `ℝ × ℝ`, first component `π_h`, second `π_l`. -/
def designs : Set (ℝ × ℝ) :=
  {π | 0 ≤ π.1 ∧ π.1 ≤ 1 ∧ 0 ≤ π.2 ∧ π.2 ≤ 1 ∧ 1 ≤ π.1 + π.2}

/-- `Pr(h) = α⁰π_h + (1 − α⁰)(1 − π_l)`. -/
def probH (a0 : ℝ) (π : ℝ × ℝ) : ℝ := a0 * π.1 + (1 - a0) * (1 - π.2)

/-- `Pr(l) = α⁰(1 − π_h) + (1 − α⁰)π_l`. -/
def probL (a0 : ℝ) (π : ℝ × ℝ) : ℝ := a0 * (1 - π.1) + (1 - a0) * π.2

/-- The posterior `α_h` of the state H after the signal `h` (the prior if `Pr(h) = 0`). -/
noncomputable def postH (a0 : ℝ) (π : ℝ × ℝ) : ℝ :=
  if probH a0 π = 0 then a0 else a0 * π.1 / probH a0 π

/-- The posterior `α_l` of the state H after the signal `l` (the prior if `Pr(l) = 0`). -/
noncomputable def postL (a0 : ℝ) (π : ℝ × ℝ) : ℝ :=
  if probL a0 π = 0 then a0 else a0 * (1 - π.1) / probL a0 π

/-- `π` induces the posterior pair `(α_l, α_h) = (a, b)` at the prior `a0`. -/
def Induces (a0 : ℝ) (π : ℝ × ℝ) (a b : ℝ) : Prop := postL a0 π = a ∧ postH a0 π = b

/-- `π` is a feasible uninformative design: `π_h + π_l = 1`. -/
def IsUninformative (π : ℝ × ℝ) : Prop := π ∈ designs ∧ π.1 + π.2 = 1

/-- The design (3), p.7, that induces the posteriors `α_l = a`, `α_h = b` at the prior `a0`. -/
noncomputable def designOf (a0 a b : ℝ) : ℝ × ℝ :=
  (b * (a0 - a) / (a0 * (b - a)), (b - a0) * (1 - a) / ((1 - a0) * (b - a)))

end EngageInfo


