-- Prove2me | Definitions.Def_PolyVoting_fAlpha
-- name    : PolyVoting_fAlpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:24.393746+00:00
-- url     : https://prove2.me/theorems/1a463eab-c770-4461-a87b-52127d861f7a
-- title:
--   The large-deviation function $f_\alpha$ of Theorem 3
-- statement:
--   For $\alpha\ge0$ and $\lambda\in(0,\infty)$,
--   $$f_\alpha(\lambda)=(1+\alpha)\lambda\log\lambda-(1+\alpha)\lambda+\frac1{\lambda^\alpha}.$$
--   It is the exponential rate in the large-deviation bounds for the volume $N_t$ at scale $t^{1/(1+\alpha)}$.
--
--   **Formalization Note** The value at $\lambda\le0$ is a Lean default and is never used.
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, Theorem 3, p.7

import Mathlib

namespace PolyVoting

/-- **The large-deviation function of Theorem 3** (Tang & Yao, *Polynomial Voting Rules*,
arXiv:2206.10105v5, p.7):
`f_α(λ) = (1 + α) λ log λ - (1 + α) λ + 1 / λ ^ α`, for `λ ∈ (0, ∞)`.

**Formalization Note.** The paper's domain is `(0, ∞)`; for `lam ≤ 0` the value is Lean's junk
value and is never used: every statement of this mission restricts to `0 < lam`. -/
noncomputable def fAlpha (α lam : ℝ) : ℝ :=
  (1 + α) * lam * Real.log lam - (1 + α) * lam + 1 / lam ^ α

end PolyVoting


