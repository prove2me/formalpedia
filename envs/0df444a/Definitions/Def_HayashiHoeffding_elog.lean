-- Prove2me | Definitions.Def_HayashiHoeffding_elog
-- name    : HayashiHoeffding_elog
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:16.659992+00:00
-- url     : https://prove2.me/theorems/037e225a-1ea0-43ea-9b93-37e6cc518229
-- title:
--   Extended-real logarithm ($\log 0 = -\infty$)
-- statement:
--   The **extended-real logarithm** of a real number $x$ is
--
--   $$\operatorname{elog} x = \begin{cases} \log x, & x > 0,\\ -\infty, & x \le 0. \end{cases}$$
--
--   It is used for the logarithms of error probabilities and of $\operatorname{Tr}\rho^{1-s}\sigma^s$, so that a vanishing probability has exponent $-\log 0 = +\infty$.
--
--   **Formalization Note** Valued in `EReal`. Mathlib's `Real.log 0 = 0` would make a zero error probability have exponent $0$ instead of $+\infty$.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.3

import Mathlib

namespace HayashiHoeffding

/-- The natural logarithm of a real number with values in the extended reals: `log x` for
`x > 0`, and `−∞` for `x ≤ 0`.

Hayashi, arXiv:quant-ph/0611013v2, p.3: the logarithms in `B(r|ρ‖σ)` and in
`φ(s|ρ‖σ) = log Tr ρ^{1−s} σ^s`, where a vanishing error probability or trace has logarithm
`−∞`.

**Formalization Note.** Mathlib's `Real.log 0 = 0` would turn a zero error probability into a
zero exponent; `elog 0 = ⊥` keeps the paper's value `−log 0 = +∞`. Only applied to
probabilities and traces of positive operators, which are `≥ 0`. -/
noncomputable def elog (x : ℝ) : EReal :=
  if 0 < x then (Real.log x : EReal) else ⊥

end HayashiHoeffding


