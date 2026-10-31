-- Prove2me | Definitions.Def_LatentRobust_sgn
-- name    : LatentRobust_sgn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:33.250783+00:00
-- url     : https://prove2.me/theorems/9a6ae33d-1d96-4e45-a493-827437af08be
-- title:
--   The $\{\pm1\}$-valued sign function
-- statement:
--   The paper's classifiers take values in $\{+1,-1\}$, and the Bayes-optimal classifier is written $\operatorname{sign}(\eta(x)-1/2)$. Here
--   $$
--   \operatorname{sgn}(t)=\begin{cases}+1,& t>0,\\ -1,& t\le 0.\end{cases}
--   $$
--
--   This is the sign used in every classifier of the mission (the Bayes classifier of Proposition 2.2 and the closed forms of Corollary 2.3).
--
--   **Formalization Note** Ties ($t=0$) go to the label $-1$, as on the page: p.7 assigns $+1$ when $+1$ has the higher likelihood, and App. A.1, p.19, gives the negative label to $\{x:\eta(x)\le 1/2\}$. Mathlib's `Real.sign`, which sends $0$ to $0$, is not used, since it does not produce a $\{\pm1\}$-valued classifier.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, §2.3, p.7 (h_Bayes(x) = sign(η(x) − 1/2), a classifier into {+1, −1}, p.5; ties to the negative label, App. A.1, p.19)

import Mathlib

namespace LatentRobust

/-- The sign function with values in `{+1, −1}` used by the paper's classifiers
(Javanmard, Mehrabi, arXiv:2110.11950v2, §2.3, p.7: `h_Bayes(x) = sign(η(x) − 1/2)` is a
classifier `ℝ^d → {+1, −1}`).

**Formalization Note** `sgn t = 1` for `t > 0` and `sgn t = −1` for `t ≤ 0`, so ties go to the
label `−1`, as on the page: p.7 assigns `+1` when `+1` has the higher likelihood, and App. A.1,
p.19, gives the negative label to `{x : η(x) ≤ 1/2}`. Mathlib's `Real.sign` (with
`sign 0 = 0`) is not used: it would not produce a `{±1}`-valued classifier. -/
noncomputable def sgn (t : ℝ) : ℝ :=
  if 0 < t then 1 else -1

end LatentRobust


