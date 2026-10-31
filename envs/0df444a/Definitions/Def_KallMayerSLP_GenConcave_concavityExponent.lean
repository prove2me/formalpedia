-- Prove2me | Definitions.Def_KallMayerSLP_GenConcave_concavityExponent
-- name    : KallMayerSLP_GenConcave_concavityExponent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:55.159457+00:00
-- url     : https://prove2.me/theorems/063de64f-de39-4c53-b253-15474540705f
-- title:
--   The exponent $\gamma/(1+r\gamma)$ with its limits $-\infty$ at $\gamma=-1/r$ and $1/r$ at $\gamma=\infty$
-- statement:
--   For a dimension $r \ge 1$ and $\gamma \in [-1/r, \infty]$ the **concavity exponent** of Theorem 2.8 is
--
--   $$
--   \frac{\gamma}{1+r\gamma}\in[-\infty,\tfrac1r],
--   $$
--
--   with the two boundary values given by their limits: it equals $-\infty$ at $\gamma=-1/r$ (where $1+r\gamma=0$) and $1/r$ at $\gamma=+\infty$. These are the values displayed in Figure 2.6 of the book: a density with $f^{-1/r}$ convex gives a quasi-concave distribution, a density constant on its support gives a distribution function with $F^{1/r}$ concave.
--
--   It is the exponent by which $\gamma$-concavity of a density on $\mathbb R^r$ transfers to the probability measure it generates.
--
--   **Formalization Note** Values are extended reals (`EReal`). The case $1+r\gamma=0$ is a separate branch, so the exponent at $\gamma=-1/r$ is $-\infty$, never a junk value from division by zero. The values at $\gamma=-\infty$ and $\gamma<-1/r$, which the book never uses, are unspecified conventions ($-\infty$ and the formula).
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 2.8, p.127 (PDF 137); Figure 2.6, p.128 (PDF 138)

import Mathlib

namespace KallMayerSLP.GenConcave

/-- The **concavity exponent** `γ / (1 + rγ)` of Theorem 2.8
(Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, Theorem 2.8, p. 127,
PDF p. 137; Figure 2.6, p. 128, PDF p. 138).

For a dimension `r ≥ 1` and `γ ∈ [−1/r, ∞]` it is the exponent `γ/(1 + rγ)` with its two
limiting values made explicit:
* `γ = −1/r` (where `1 + rγ = 0`) gives `−∞`;
* `γ = +∞` gives `1/r`;
* otherwise `γ/(1 + rγ) ∈ ℝ`.

**Formalization Note.** Values in `EReal`. The two boundary values are the limits of
`γ/(1 + rγ)` as `γ ↓ −1/r` and `γ → ∞`, and are the ones Figure 2.6 (p. 128) displays
(`−1/r ↦ −∞` "F quasiconcave", `+∞ ↦ 1/r` "F^{1/r} concave"). The case `1 + rγ = 0` is
handled by an explicit branch, so no junk division by zero turns the exponent at
`γ = −1/r` into `0`. The book never uses `γ < −1/r` or `γ = −∞`; there the value
(`⊥` for `γ = −∞`, the formula otherwise) is unused. -/
noncomputable def concavityExponent (r : ℕ) (γ : EReal) : EReal :=
  if γ = ⊥ then ⊥
  else if γ = ⊤ then ((1 / (r : ℝ) : ℝ) : EReal)
  else if 1 + (r : ℝ) * γ.toReal = 0 then ⊥
  else ((γ.toReal / (1 + (r : ℝ) * γ.toReal) : ℝ) : EReal)

end KallMayerSLP.GenConcave


