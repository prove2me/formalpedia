-- Prove2me | Definitions.Def_SubsamplingSM_Offline_considered
-- name    : SubsamplingSM_Offline_considered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:56:08.162894+00:00
-- url     : https://prove2.me/theorems/12043725-a7f1-4414-97f0-dbb37deddbcb
-- title:
--   Indicator $X_u$ that $u$ is considered
-- statement:
--   An element $u\in N$ is **considered** by Algorithm 2 if it is chosen in Line 3 at some iteration. For coins $b$, $X_u\in\{0,1\}$ is the indicator of this event; equivalently, $X_u=1$ if and only if $u$ has been removed from $N'$ by the end of the run.
--
--   The random variables $X_u$ appear in Lemmas 7, 8 and 10.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, p. 11 and p. 13

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_alg2Run

namespace SubsamplingSM.Offline

/-- **The indicator `X_u` that `u` is considered by Algorithm 2.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, p. 13 (unnumbered): "For every element `u ∈ N`, let `Xu` be an indicator for the event
that `u` is considered by Algorithm 2 in one of its iterations", where (p. 11) "an element
`u ∈ N` is considered by Algorithm 2 if it is chosen in Line 3 at some iteration."

`considered f I sel O₀ b u` is `1` if `u` has left the pool `N′` by the end of the run with
coins `b` (Line 11 removes exactly the considered element), and `0` otherwise. -/
noncomputable def considered {α : Type*} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (sel : Finset α → Finset α → Finset α) (O₀ b : Finset α) (u : α) : ℝ :=
  if u ∈ (alg2Run f I sel O₀ b).N' then 0 else 1

end SubsamplingSM.Offline


