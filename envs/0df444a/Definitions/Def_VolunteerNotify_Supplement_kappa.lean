-- Prove2me | Definitions.Def_VolunteerNotify_Supplement_kappa
-- name    : VolunteerNotify_Supplement_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:24:03.76748+00:00
-- url     : https://prove2.me/theorems/9ac0dc8d-e1ef-4008-a885-52b93032592d
-- title:
--   (18) — the upper bound $\kappa(q)$ of Theorem 2
-- statement:
--   For $q\in(0,1]$ let
--   $$
--   \kappa_2(q)=1+q-\frac{q(1-q)}{\log\!\big(\frac1{1-q}\big)(1+q)}\big(1-e^{-1}\big),
--   $$
--   with $\log$ the natural logarithm, and set
--   $$
--   \kappa(q)=\min\Big\{\frac1{2-q},\ \kappa_2(q)\Big\}\quad(q>0),\qquad \kappa(0)=0.334 .
--   $$
--   $\kappa$ is the upper bound of Theorem 2 on the competitive ratio of any online policy when the MDHR is $q$; $\kappa_2(q)$ alone is the bound of Lemma 5 for instance $\mathcal I_2$.
--
--   **Formalization Note** At $q=1$ the printed $\kappa_2$ is undefined ($\log(1/0)$). Lean's conventions ($1/0=0$, $\log 0=0$, $x/0=0$) give $\kappa_2(1)=2$, which is also the limit as $q\to1$, so $\kappa(1)=1$, the value footnote 21 gives. $0.334$ is the exact decimal $334/1000$.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Theorem 2 and (18), p.21; fn. 21, p.21

import Mathlib

namespace VolunteerNotify.Supplement

/-- The second term of (18), Manshadi–Rodilitz, arXiv:2002.08474v7, p.21, which is also the bound
of Lemma 5, p.22: `1 + q − q(1 − q) / (log(1/(1 − q)) (1 + q)) · (1 − e^{−1})`.

**Formalization Note.** `log` is the natural logarithm `Real.log`. At `q = 1` the printed
expression is undefined (`log(1/0)`); Lean's `1/0 = 0`, `log 0 = 0` and `x/0 = 0` give the value
`2` there. -/
noncomputable def kappaTwo (q : ℝ) : ℝ :=
  1 + q - q * (1 - q) / (Real.log (1 / (1 - q)) * (1 + q)) * (1 - Real.exp (-1))

/-- `κ(q)` of Theorem 2 and (18), arXiv:2002.08474v7, p.21: for `q > 0`,
`κ = min{1/(2 − q), kappaTwo q}`, and for `q = 0`, `κ = 0.334`.

**Formalization Note.** At `q = 1`, `kappaTwo 1 = 2` by Lean's conventions, so `κ(1) = 1`, the
value fn. 21 (p.21) gives. Theorem 2 only uses `q ∈ [0, 1]`. -/
noncomputable def kappa (q : ℝ) : ℝ :=
  if q = 0 then 334 / 1000 else min (1 / (2 - q)) (kappaTwo q)

end VolunteerNotify.Supplement


