-- Prove2me | Definitions.Def_PhiDivRobust_Counterpart_perspConj
-- name    : PhiDivRobust_Counterpart_perspConj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:48:15.811985+00:00
-- url     : https://prove2.me/theorems/c8c8e09f-838c-482c-b646-0ddfa18fc142
-- title:
--   The term λφ*(s/λ) of the robust counterpart (13), with 0φ*(s/0) := 0 for s ≤ 0 and +∞ for s > 0
-- statement:
--   For $\lambda\ge0$ and $s\in\mathbb R$, the term of the robust counterpart (13) is
--
--   $$\lambda\phi^*(s/\lambda) = \begin{cases} \lambda\,\phi^*(s/\lambda), & \lambda>0,\\ 0, & \lambda=0,\ s\le 0,\\ +\infty, & \lambda = 0,\ s>0,\end{cases}$$
--
--   where $\phi^*$ is the conjugate (4). The two lower lines are the paper's convention $0\phi^*(s/0):=0$ if $s\le0$ and $0\phi^*(s/0):=+\infty$ if $s>0$, stated with Theorem 1.
--
--   **Formalization Note** The case $\lambda=0$ is an explicit case split, not the product $0\cdot\phi^*(s/0)$ with Lean's $s/0=0$ (which would always give $0$). Only $\lambda\ge0$ is ever used; for $\lambda<0$ the Lean definition falls into the $\lambda=0$ branch, a value no statement relies on.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, Theorem 1 (the convention after (13))

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_conj
open Matrix

namespace PhiDivRobust.Counterpart

/-- The term `λ φ*(s/λ)` of the robust counterpart (13) (Ben-Tal et al. 2013, p. 347, Theorem 1),
with the paper's convention for `λ = 0`: `0 φ*(s/0) := 0` if `s ≤ 0` and `:= +∞` if `s > 0`.
Only `λ ≥ 0` is ever used; the `else` branch is the `λ = 0` convention. -/
noncomputable def perspConj (φ : ℝ → EReal) (lam s : ℝ) : EReal :=
  if 0 < lam then (lam : EReal) * conj φ (s / lam) else if s ≤ 0 then 0 else ⊤

end PhiDivRobust.Counterpart


