-- Prove2me | Definitions.Def_LightningNetwork_RateBounds_bidiCost
-- name    : LightningNetwork_RateBounds_bidiCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:46:34.567507+00:00
-- url     : https://prove2.me/theorems/02f76cc3-d67f-42e3-9c7b-be67080f9cc0
-- title:
--   Cost of a bidirectional channel, Theorem 1(ii), eq. (3)
-- statement:
--   In a **bidirectional channel** node 1 commits $l_1$ and node 2 commits $l_2$; node 1 pays node 2 at Poisson rate $\lambda_1$ and node 2 pays node 1 at rate $\lambda_2$. The channel is reset at cost $B$ whenever a balance is exhausted, and capital costs interest at rate $r$. By Theorem 1(ii) of the paper, with $\alpha_\pm$ from (4), its expected discounted cost is
--
--   $$
--   c^{l_1,l_2}(\lambda_1,\lambda_2) \;=\; l_1 + l_2 - B\,\frac{\alpha_-^{l_1}\bigl(1-\alpha_+^{l_1+l_2}\bigr) - \alpha_+^{l_1}\bigl(1-\alpha_-^{l_1+l_2}\bigr)}{\alpha_-^{l_1}\bigl(1-\alpha_+^{l_1+l_2}\bigr) - \alpha_+^{l_1}\bigl(1-\alpha_-^{l_1+l_2}\bigr) + \alpha_+^{l_1+l_2} - \alpha_-^{l_1+l_2}}.
--   $$
--
--   Theorem 2(ii) uses it at $\lambda_1 = \lambda_2 = \lambda$ (a symmetric channel).
--
--   **Formalization Note** The printed general form (3) is taken as the definition of the channel's cost; that it is the expected discounted cost of the Poisson model is the content of Theorem 1, which is not formalized here. Powers are real powers, so the commitments are real numbers. Theorem 1 assumes $\lambda_1 \le \lambda_2$; the definition carries no hypothesis.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, Theorem 1(ii), eqs. (3)–(4), p. 6

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_alphaPlus
import Definitions.Def_LightningNetwork_RateBounds_alphaMinus

namespace LightningNetwork.RateBounds

/-- **Cost of a bidirectional channel**, Theorem 1(ii), display (3).
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, Theorem 1(ii), eqs. (3)–(4), p. 6:
"A bidirectional channel costs
c^{l1,l2}(λ1, λ2) = l1 + l2 − B (α₋^{l1}(1 − α₊^{l1+l2}) − α₊^{l1}(1 − α₋^{l1+l2})) /
(α₋^{l1}(1 − α₊^{l1+l2}) − α₊^{l1}(1 − α₋^{l1+l2}) + α₊^{l1+l2} − α₋^{l1+l2})", with α± of (4).

With `a₊ = alphaPlus lam1 lam2 r`, `a₋ = alphaMinus lam1 lam2 r`, `L = l1 + l2` and
`N = a₋^{l1}(1 − a₊^L) − a₊^{l1}(1 − a₋^L)`, `bidiCost B r lam1 lam2 l1 l2 = l1 + l2 − B·N/(N + a₊^L − a₋^L)`:
the expected discounted cost of a bidirectional channel in which node 1 commits `l1` and node 2
commits `l2`, node 1 pays node 2 at rate `lam1` and node 2 pays node 1 at rate `lam2`.

**Formalization Note.** Literal transcription of the closed form (3) in its general (asymmetric)
printed form, taken as the definition of the channel's cost; the stochastic content of Theorem 1
is not formalized. Powers are `Real.rpow` (real commitments). Theorem 1 assumes `λ1 ≤ λ2`; the
definition itself carries no hypothesis. -/
noncomputable def bidiCost (B r lam1 lam2 l1 l2 : ℝ) : ℝ :=
  let ap := alphaPlus lam1 lam2 r
  let am := alphaMinus lam1 lam2 r
  let N := am ^ l1 * (1 - ap ^ (l1 + l2)) - ap ^ l1 * (1 - am ^ (l1 + l2))
  l1 + l2 - B * N / (N + ap ^ (l1 + l2) - am ^ (l1 + l2))

end LightningNetwork.RateBounds


