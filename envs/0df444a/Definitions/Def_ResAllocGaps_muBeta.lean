-- Prove2me | Definitions.Def_ResAllocGaps_muBeta
-- name    : ResAllocGaps_muBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:33.360082+00:00
-- url     : https://prove2.me/theorems/a9fc065f-34c3-4471-92e8-67824a1debf2
-- title:
--   The bimodal law $F_\beta$ of Example 3, display (1)
-- statement:
--   For $\beta\ge0$ the distribution function of display (1) is
--   $$F_\beta(x)=\begin{cases}-2\cdot4^\beta\,(\tfrac14-x)^{\beta+1}+\tfrac12,&0\le x\le\tfrac14,\\ \tfrac12,&\tfrac14\le x\le\tfrac34,\\ 2\cdot4^\beta\,(x-\tfrac34)^{\beta+1}+\tfrac12,&\tfrac34\le x\le1,\end{cases}$$
--   extended by $0$ to the left of $0$ and by $1$ to the right of $1$. Its density is $f_\beta(x)=2(\beta+1)4^\beta(\tfrac14-x)^\beta$ on $[0,\tfrac14]$, $2(\beta+1)4^\beta(x-\tfrac34)^\beta$ on $[\tfrac34,1]$, and $0$ elsewhere. The law $F_\beta$ has one gap $(\tfrac14,\tfrac34)$ and two clusters $[0,\tfrac14]$, $[\tfrac34,1]$, with mass accumulating like $\mathrm{distance}^{\beta+1}$ at the edges of the gap.
--
--   It is the hard instance of the universal lower bound for $\beta>0$.
--
--   **Formalization Note** The law is Lebesgue measure with density $f_\beta$ (`withDensity`). That it is a probability measure on $[0,1]$ whose distribution function equals (1) is a clause of the milestone `ResAllocGaps.example_3`, not an assumption.
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, §3.1, p.13, Example 3, display (1); Appendix EC.1, (EC.1), p.ec1

import Mathlib

open MeasureTheory

namespace ResAllocGaps

/-- The cumulative distribution function `F_β` of Example 3, display (1), Besbes, Kanoria & Kumar,
arXiv:2205.09078v2, p.13 (and (EC.1), p.ec1, with `g = 1/2`, `ℓ = 1/4`, `u = 3/4`):
`F_β(x) = −2·4^β·(1/4 − x)^{β+1} + 1/2` on `[0, 1/4]`, `1/2` on `[1/4, 3/4]`,
`2·4^β·(x − 3/4)^{β+1} + 1/2` on `[3/4, 1]`.

**Formalization Note.** Powers are `Real.rpow` with nonnegative bases. Outside `[0, 1]` the
function is extended by `0` (left) and `1` (right), the values of a distribution function supported
on `[0, 1]`. -/
noncomputable def FbetaCdf (β x : ℝ) : ℝ :=
  if x < 0 then 0
  else if x ≤ 1 / 4 then -2 * (4 : ℝ) ^ β * (1 / 4 - x) ^ (β + 1) + 1 / 2
  else if x ≤ 3 / 4 then 1 / 2
  else if x ≤ 1 then 2 * (4 : ℝ) ^ β * (x - 3 / 4) ^ (β + 1) + 1 / 2
  else 1

/-- The density `f_β = F_β'` of the law of Example 3 (Figure 1 (L), p.13):
`2(β+1)·4^β·(1/4 − x)^β` on `[0, 1/4]`, `2(β+1)·4^β·(x − 3/4)^β` on `[3/4, 1]`, `0` elsewhere. -/
noncomputable def fbetaDensity (β x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x ≤ 1 / 4 then 2 * (β + 1) * (4 : ℝ) ^ β * (1 / 4 - x) ^ β
  else if 3 / 4 ≤ x ∧ x ≤ 1 then 2 * (β + 1) * (4 : ℝ) ^ β * (x - 3 / 4) ^ β
  else 0

/-- The **bimodal candidate-ability law** `F_β` of Example 3, display (1), Besbes, Kanoria & Kumar,
arXiv:2205.09078v2, p.13, used in the proof of Theorem 1 (p.ec1): one gap `(1/4, 3/4)` and two
clusters `[0, 1/4]`, `[3/4, 1]`, with mass accumulating like `distance^{β+1}` at the gap's edges.

**Formalization Note.** Defined as Lebesgue measure with density `fbetaDensity β`, the derivative
of the distribution function `FbetaCdf β` of (1). That its distribution function is (1) on
`[0, 1]` and that it is a probability measure for every `β ≥ 0` are part of the milestone
`ResAllocGaps.example_3`, not assumptions. -/
noncomputable def muBeta (β : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (fbetaDensity β x))

end ResAllocGaps


