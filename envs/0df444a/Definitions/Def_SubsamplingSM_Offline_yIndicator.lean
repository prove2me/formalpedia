-- Prove2me | Definitions.Def_SubsamplingSM_Offline_yIndicator
-- name    : SubsamplingSM_Offline_yIndicator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:57:05.369192+00:00
-- url     : https://prove2.me/theorems/3570bd80-380f-4a92-9c4c-a79ae405671b
-- title:
--   Indicator $Y_u$
-- statement:
--   For coins $b$ and $u\in N$, $Y_u=1$ if $u\in S$ and, in addition, $u$ does not belong to $O$ at the beginning of the iteration in which $u$ is considered; in every other case $Y_u=0$.
--
--   The random variables $Y_u$ appear in Lemmas 9 and 10, which tighten the analysis for linear objectives.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, §4.1.2, p. 15

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_alg2Run

namespace SubsamplingSM.Offline

/-- **The indicator `Y_u`.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, §4.1.2, p. 15 (unnumbered): "For every `u ∈ N`, let `Yu` be a random variable which takes
the value 1 if `u ∈ S` and, in addition, `u` does not belong to `O` at the beginning of the
iteration in which `u` is considered. In every other case the value of `Yu` is 0."

`yIndicator f I sel O₀ b u` is `1` if `u` was recorded in `Ys` during the run with coins
`b` (it was added to `S` and was not in `O` at the start of that iteration), and `0`
otherwise. -/
noncomputable def yIndicator {α : Type*} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (sel : Finset α → Finset α → Finset α) (O₀ b : Finset α) (u : α) : ℝ :=
  if u ∈ (alg2Run f I sel O₀ b).Ys then 1 else 0

end SubsamplingSM.Offline


