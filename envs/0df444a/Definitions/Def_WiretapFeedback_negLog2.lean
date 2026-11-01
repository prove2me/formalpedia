-- Prove2me | Definitions.Def_WiretapFeedback_negLog2
-- name    : WiretapFeedback_negLog2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:49.214493+00:00
-- url     : https://prove2.me/theorems/29263fbc-4095-4363-85be-8ed158664a8a
-- title:
--   $-\log_2 b$ of a probability, with $-\log_2 0=+\infty$
-- statement:
--   For a probability $b\in[0,1]$ (more generally $b\in[0,\infty]$) define
--   $$
--   \operatorname{negLog2}(b)=-\log_2 b=-\frac{\ln b}{\ln 2}\in[-\infty,+\infty],
--   $$
--   with the conventions $-\log_2 0=+\infty$ and $-\log_2(+\infty)=-\infty$.
--
--   This is the quantity $-\log\beta$ in which optimal type-II error probabilities enter Theorems 4, 5 and 6 of the paper. Since an optimal type-II error can be exactly $0$, the value $+\infty$ must be representable.
--
--   **Formalization Note** Computed in the extended reals from `ENNReal.log` (which sends $0$ to $-\infty$), not from `Real.log`, whose value at $0$ is the junk $0$. Logarithms are base 2 throughout, as the rate is defined through $\lfloor 2^{nR}\rfloor$.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, Theorems 4–6, p.3 (the quantity −log β)

import Mathlib

open scoped ENNReal

namespace WiretapFeedback

/-- The quantity `−log₂ b` of a probability `b ∈ [0, 1]`, as an extended real number:
`negLog2 b = −(ln b) / ln 2`, with `negLog2 0 = +∞`.

It is the form in which the type-II error optimum enters Hayashi–Tyagi–Watanabe,
*Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing*,
arXiv:1410.0443v1, Theorems 4, 5 and 6 (pp. 3), `−log β_ϵ(·)`.

**Formalization Note** Logarithms are base 2 throughout the paper (rates are defined through
`⌊2^{nR}⌋`, p. 2). A type-II error optimum `β` can be `0`, and then `−log β = +∞`; the value is
therefore computed with `ENNReal.log : ℝ≥0∞ → EReal` (`ENNReal.log 0 = ⊥`) rather than with
`Real.log`, whose junk value `Real.log 0 = 0` would make the paper's bounds false at `β = 0`. -/
noncomputable def negLog2 (b : ℝ≥0∞) : EReal :=
  -(ENNReal.log b) * (((Real.log 2)⁻¹ : ℝ) : EReal)

end WiretapFeedback


