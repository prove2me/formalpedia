-- Prove2me | Definitions.Def_KallMayerSLP_GenConcave_genMean
-- name    : KallMayerSLP_GenConcave_genMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:52.645667+00:00
-- url     : https://prove2.me/theorems/39701b0a-8202-40cf-b71e-25207be0dc8a
-- title:
--   Generalized means $\mathcal M_\gamma^\lambda(a,b)$, $\gamma\in[-\infty,\infty]$
-- statement:
--   Let $a \ge 0$, $b \ge 0$ and $\lambda \in [0,1]$, and let $\gamma \in \mathbb R \cup \{-\infty\} \cup \{\infty\}$. The **generalized mean** $\mathcal M_\gamma^\lambda(a,b)$ is $0$ whenever $ab = 0$, for every $\gamma$. If $ab > 0$,
--
--   $$
--   \mathcal M_\gamma^\lambda(a,b)=\begin{cases}
--   \bigl[\lambda a^\gamma+(1-\lambda)b^\gamma\bigr]^{1/\gamma}, & -\infty<\gamma<\infty,\ \gamma\neq 0,\\
--   a^\lambda b^{1-\lambda}, & \gamma=0,\\
--   \min\{a,b\}, & \gamma=-\infty,\\
--   \max\{a,b\}, & \gamma=\infty.
--   \end{cases}
--   $$
--
--   These means, after Hardy, Littlewood and Pólya, are the scale on which generalized concavity of functions and of probability measures is measured: $\gamma$-concave functions and $\gamma$-concave measures are defined by comparing a value at a convex combination with $\mathcal M_\gamma^\lambda$ of the values at the endpoints.
--
--   **Formalization Note** The exponent $\gamma$ is an extended real (`EReal`, with $\bot=-\infty$ and $\top=+\infty$) and the weight $\lambda$ is the argument `lam`. The convention $\mathcal M_\gamma^\lambda(a,b)=0$ for $ab=0$ is kept for every $\gamma$, including $+\infty$; this is not Mathlib's weighted power mean. Outside $a,b\ge 0$, $\lambda\in[0,1]$ the value is never used.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.5.1, eq. (2.63), pp.122–123 (PDF 132–133)

import Mathlib

namespace KallMayerSLP.GenConcave

/-- The **generalized mean** `M_γ^λ(a, b)` of two nonnegative numbers
(Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §2.5.1, eq. (2.63),
pp. 122–123, PDF pp. 132–133; after Hardy, Littlewood and Pólya).

For `a, b ≥ 0`, `λ ∈ [0, 1]` and `γ ∈ ℝ ∪ {−∞} ∪ {∞}`:
`M_γ^λ(a, b) = 0` if `ab = 0`; otherwise
* `[λ a^γ + (1 − λ) b^γ]^{1/γ}` if `−∞ < γ < ∞`, `γ ≠ 0`;
* `a^λ b^{1−λ}` if `γ = 0`;
* `min {a, b}` if `γ = −∞`;
* `max {a, b}` if `γ = ∞`.

**Formalization Note.** The exponent `γ` ranges over the extended reals `EReal`
(`⊥ = −∞`, `⊤ = +∞`); the weight `λ` is the argument `lam`. The convention
`M_γ^λ(a, b) = 0` whenever `ab = 0` is the book's, for every `γ` including `+∞`; this is
not Mathlib's weighted power mean. The book defines the mean only for `a, b ≥ 0` and
`λ ∈ [0, 1]`; every statement of the mission supplies these, and the value outside that
domain is never used. -/
noncomputable def genMean (γ : EReal) (lam a b : ℝ) : ℝ :=
  if a * b = 0 then 0
  else if γ = ⊥ then min a b
  else if γ = ⊤ then max a b
  else if γ.toReal = 0 then a ^ lam * b ^ (1 - lam)
  else (lam * a ^ γ.toReal + (1 - lam) * b ^ γ.toReal) ^ (1 / γ.toReal)

end KallMayerSLP.GenConcave


