-- Prove2me | Definitions.Def_StochAutoreg_klBernE
-- name    : StochAutoreg_klBernE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:48.650018+00:00
-- url     : https://prove2.me/theorems/7b1e49b6-4bd9-4953-b6ef-c0c79bdabd17
-- title:
--   Forward Bernoulli KL divergence with values in $[0,\infty]$
-- statement:
--   For $u,v\in[0,1]$, the forward KL divergence between Bernoulli laws is
--
--   $$\mathrm{KL}(u\|v)=u\log\frac uv+(1-u)\log\frac{1-u}{1-v},$$
--
--   with natural logarithms, a summand of zero target mass set to zero, and the value $+\infty$ when the prediction puts zero mass on an outcome that the target charges. The first argument is the target and the second the prediction.
--
--   **Formalization Note** The value lies in $[0,\infty]$. It is $\top$ when $v=0\ne u$ or $v=1\ne u$, and otherwise the non-negative real number given by the published formula `RegretBandits.Stochastic.klBern`.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §2, p.7

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

namespace StochAutoreg

/-- The forward **KL divergence between Bernoulli laws** with the values of the paper:
`KL(u‖v) = u log(u/v) + (1-u) log((1-u)/(1-v))`, natural logarithms, a summand with zero target mass
is zero, and the divergence is `+∞` when the prediction puts zero mass on an outcome the target charges.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §2, p.7.

**Formalization Note.** `⊤` when (`v = 0` and `u ≠ 0`) or (`v = 1` and `u ≠ 1`); otherwise
`ENNReal.ofReal` of the published real formula `RegretBandits.Stochastic.klBern`, which is nonnegative
for `u, v ∈ [0,1]` and which returns `0` at `u = v ∈ {0,1}` by `0 * _ = 0` and `log 1 = 0`. Only
`u, v ∈ [0,1]` occur in this mission. -/
noncomputable def klBernE (u v : ℝ) : ENNReal := by
  classical
  exact if (v = 0 ∧ u ≠ 0) ∨ (v = 1 ∧ u ≠ 1) then ⊤
    else ENNReal.ofReal (RegretBandits.Stochastic.klBern u v)

end StochAutoreg


