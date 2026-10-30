-- Prove2me | Definitions.Def_BBPSSW_Distill_wernerYield
-- name    : BBPSSW_Distill_wernerYield
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:54.143029+00:00
-- url     : https://prove2.me/theorems/fb9e3528-ceeb-4de9-bff4-bd73b38592f9
-- title:
--   Werner breeding yield $1+F\log_2F+(1-F)\log_2\frac{1-F}{3}$, Eq. (8)
-- statement:
--   The right side of Eq. (8):
--
--   $$y(F)=1+F\log_2F+(1-F)\log_2\frac{1-F}{3}.$$
--
--   For $0\le F\le1$ this is $1-S(W_F)$, the breeding yield of Werner states.
--
--   **Formalization Note** $\log_2 0$ is $0$ in Lean, so $0\log_20=0$ at $F=0$ and $F=1$, the entropy convention.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Eq. (8), p. 3

import Mathlib

namespace BBPSSW.Distill

/-- **The breeding yield of a Werner state, right side of Eq. (8).**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Eq. (8), p. 3: "For Werner states the yield
1 − S(W_F) = 1 + F log2 F + (1−F) log2 ((1−F)/3) (8)".

`wernerYield F = 1 + F log₂ F + (1 − F) log₂((1 − F)/3)`.

**Formalization Note.** `Real.logb 2 0 = 0`, so at `F = 0` and `F = 1` the terms
`0 · log₂ 0` are `0`, the entropy convention. -/
noncomputable def wernerYield (F : ℝ) : ℝ :=
  1 + F * Real.logb 2 F + (1 - F) * Real.logb 2 ((1 - F) / 3)

end BBPSSW.Distill


