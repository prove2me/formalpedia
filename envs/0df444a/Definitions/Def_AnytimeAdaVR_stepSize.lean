-- Prove2me | Definitions.Def_AnytimeAdaVR_stepSize
-- name    : AnytimeAdaVR_stepSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:31.606873+00:00
-- url     : https://prove2.me/theorems/96ebcf78-dfbe-4388-afcb-8668e227499b
-- title:
--   Block step length $\eta$
-- statement:
--   Within a block with scale $a$ and length $b$, the normalized step length is
--   $$
--   \eta=\begin{cases}\sqrt2/(a\,b^{3/2}), & \text{for S},\\ 1/(ab), & \text{for M}.\end{cases}
--   $$
--   Equivalently $\eta_j=(2/b_j)^{(p-1)/2}/(a_jb_j)$ with $p=2$ for S and $p=1$ for M.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.1, eq. (11), p.7; eq. (36), p.19

import Mathlib
import Definitions.Def_AnytimeAdaVR_SMKind

namespace AnytimeAdaVR

/-- **The block step length `η`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.1, p.7, eq. (11): "η = √2/(ab^{3/2}) for S,
1/(ab) for M", where `a` is the block's scale and `b` its length; equivalently (36), p.19,
`η_j = (2/b_j)^{(p−1)/2}/(a_j b_j)` with `p = 2` for S and `p = 1` for M.

**Formalization Note.** The block length `b` is a natural number, cast to `ℝ`; `b^{3/2}` is
`Real.rpow`. -/
noncomputable def stepSize : SMKind → ℝ → ℕ → ℝ
  | .S, a, b => Real.sqrt 2 / (a * (b : ℝ) ^ (3 / 2 : ℝ))
  | .M, a, b => 1 / (a * (b : ℝ))

end AnytimeAdaVR


