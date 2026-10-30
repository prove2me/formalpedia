-- Prove2me | Definitions.Def_JailletLu_rot
-- name    : JailletLu_rot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:20:55.734813+00:00
-- url     : https://prove2.me/theorems/c8c65da0-3896-42a0-aad7-63fe82fb8051
-- title:
--   Half rotation $x\mapsto x\pm r_i/2$
-- statement:
--   For $\rho\ge 0$ and $x\in[0,\rho]$,
--   $$
--   \mathrm{rot}_\rho(x)=\begin{cases}x+\rho/2,& x<\rho/2,\\ x-\rho/2,& x\ge\rho/2,\end{cases}
--   $$
--   the one of $x\pm\rho/2$ that lies in $[0,\rho]$. In the list construction, the second advertiser of the list is the one whose interval contains $\mathrm{rot}_{r_i}(x)$.
--
--   **Formalization Note** "$x\pm r_i/2$" is read as this rotation; both values lie in $[0,\rho]$ only at $x=\rho/2$, a null set.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13

import Mathlib

namespace JailletLu

/-- **Half rotation `x ↦ x ± r_i/2` of `[0, r_i]`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "if x ± r_i/2 ∈ [Σ_{l=1}^{k−1} f_{a_l,i}, Σ_{l=1}^{k} f_{a_l,i}] then a_k is the
second in the list to be considered".

`rot ρ x = x + ρ/2` if `x < ρ/2`, and `x − ρ/2` otherwise: for `x ∈ [0, ρ]` it is the one of
`x + ρ/2`, `x − ρ/2` that lies in `[0, ρ]` (a reading of "x ± r_i/2"; both lie in `[0, ρ]` only
at `x = ρ/2`, a null set). It is used with `ρ = r_i`. -/
noncomputable def rot (ρ x : ℝ) : ℝ :=
  if x < ρ / 2 then x + ρ / 2 else x - ρ / 2

end JailletLu


