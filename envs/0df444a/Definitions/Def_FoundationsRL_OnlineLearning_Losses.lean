-- Prove2me | Definitions.Def_FoundationsRL_OnlineLearning_Losses
-- name    : FoundationsRL_OnlineLearning_Losses
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:47.698372+00:00
-- url     : https://prove2.me/theorems/dda25071-506a-48ed-9b44-2999bb84d098
-- title:
--   Square loss and log loss, with $-\log 0=+\infty$
-- statement:
--   The two losses of the fast-rate part of Proposition 3.
--
--   1. **Square loss.** $\ell(a,b)=(a-b)^2$ for $a,b\in\mathbb R$.
--   2. **Extended negative logarithm.** $-\log p$ for $p>0$, and $+\infty$ otherwise.
--   3. **Log loss.** For a conditional density $p=f(\cdot\mid x)$ on $\mathcal Y$,
--   $$
--   \ell_{\log}(p,y)=-\log p(y)\in(-\infty,+\infty].
--   $$
--
--   The log loss is what makes exponential weights a mixture of densities: at learning rate $1$ the algorithm's loss is exactly an increment of the potential.
--
--   **Formalization Note** `Real.log 0 = 0` in Lean, which would make a zero density look like a perfect prediction, so the logarithm is extended by hand. A density above $1$ has negative log loss, so the values lie in `EReal` and not in `ℝ≥0∞`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.6.2, proof of Proposition 3, p. 16, and Lemma 6, p. 15

import Mathlib

namespace FoundationsRL.OnlineLearning

/-- **Square loss** `ℓ(a, b) = (a - b)²` on predictions and outcomes in `ℝ`, §1.6, Lemma 6, p. 15, and
Proposition 3, p. 16, arXiv:2312.16730v1. -/
def squareLoss (a b : ℝ) : ℝ := (a - b) ^ 2

/-- **`-log` with values in `(-∞, +∞]`**: `-log p` for `p > 0` and `+∞` otherwise.

**Formalization Note.** `Real.log` returns `0` at `0`, which would make a zero density look like a
perfect prediction. Here `-log 0 = +∞`, the value the notes' log loss takes on a zero density. A
density above `1` has negative log loss, so `ℝ≥0∞` would not do. Negative `p` is excluded by the
hypotheses of every statement that uses this function. -/
noncomputable def negLog (p : ℝ) : EReal :=
  if 0 < p then ((-Real.log p : ℝ) : EReal) else ⊤

/-- **Log loss**, §1.6.2, proof of Proposition 3, p. 16, arXiv:2312.16730v1:
`ℓ_log(p, y) = -log p(y)`, for a conditional density `p = f(· | x)` on `Y`.

**Formalization Note.** A density is a function `Y → ℝ`, so `f : X → Y → ℝ` is the notes' `f(y | x)`.
The value is `+∞` where the density vanishes (see `negLog`). -/
noncomputable def logLoss {Y : Type*} (p : Y → ℝ) (y : Y) : EReal := negLog (p y)

end FoundationsRL.OnlineLearning


