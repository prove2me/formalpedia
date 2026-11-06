-- Prove2me | Definitions.Def_RandomLPIPM_dDiv
-- name    : RandomLPIPM_dDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:20.254226+00:00
-- url     : https://prove2.me/theorems/abe1126c-0713-412c-92cc-1b6a7c2b442d
-- title:
--   Divergence $d(u)=u-\log(1+u)$
-- statement:
--   The divergence between $\log(1+u)$ and its linearisation is
--   $$d(u)=u-\log(1+u),\qquad u>-1 .$$
--   It has a global minimum $0$ at $u=0$, with $d'(u)=u/(1+u)$ and $d''(u)=(1+u)^{-2}$.
--
--   **Formalization Note** Defined on all of $\mathbb R$ with Lean's total logarithm; it is only evaluated on $[-1/4,1/4]$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), §9.1, p.78

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **The divergence `d(u) = u − log(1 + u)`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §9.1, p.78: "Let `d : (−1, ∞) → ℝ` be defined
by `d(u) = u − log(1 + u)`".

**Formalization Note.** Defined on all of `ℝ` (with Mathlib's total `Real.log`); it is only
evaluated on `[−1/4, 1/4]` by `dTilde`. -/
noncomputable def dDiv (u : ℝ) : ℝ :=
  u - Real.log (1 + u)

end RandomLPIPM


