-- Prove2me | Definitions.Def_KatyushaNs_alphaS
-- name    : KatyushaNs_alphaS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:46:59.421658+00:00
-- url     : https://prove2.me/theorems/5f71eba8-0926-4d07-abec-621f01912a61
-- title:
--   Step size $\alpha_s = 1/(3\tau_{1,s}L)$
-- statement:
--   For the epoch index $s$ and the smoothness constant $L > 0$,
--   $$\alpha_s = \frac{1}{3\,\tau_{1,s}\,L} = \frac{s+4}{6L}.$$
--   It is the step size of the mirror-descent step (line 11) of Algorithm 2.
--
--   **Formalization Note** At $L = 0$ the value is the junk $0$; every theorem using it assumes $L > 0$.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Algorithm 2, line 5, p. 15

import Mathlib
import Definitions.Def_KatyushaNs_tau1

namespace KatyushaNs

/-- **The step size `α_s = 1/(3 τ_{1,s} L)` (Algorithm 2, line 5).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Algorithm 2, line 5, p. 15 (PDF p. 16): "α_s ← 1/(3τ_{1,s}L)".

`alphaS L s = 1 / (3 · tau1 s · L)`.

**Formalization Note.** At `L = 0` the value is the junk `0`; every theorem using it assumes
`0 < L`. -/
noncomputable def alphaS (L : ℝ) (s : ℕ) : ℝ := 1 / (3 * tau1 s * L)

end KatyushaNs


