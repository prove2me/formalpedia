-- Prove2me | Definitions.Def_NashStackelberg_NASP_Ftilde
-- name    : NashStackelberg_NASP_Ftilde
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:29.228786+00:00
-- url     : https://prove2.me/theorems/df39441c-3699-4f7e-9d59-b4cb10204c63
-- title:
--   The convexified strategy set $\widetilde{\mathcal F}^i=\mathrm{cl\,conv}(\mathcal F^i)$
-- statement:
--   For a NASP $N$ and a player $i$,
--   $$
--   \widetilde{\mathcal F}^i := \mathrm{cl\,conv}(\mathcal F^i),
--   $$
--   the closure of the convex hull of player $i$'s feasible region. The **convexified game** $\widetilde N=(\widetilde S^1,\dots,\widetilde S^n)$ has the same costs as $N$ and strategy sets $\widetilde{\mathcal F}^i$:
--   $$
--   \widetilde S^i=\min_{x^i}\ (c^i)^\top x^i+(C^i x^{-i})^\top x^i\quad\text{s.t.}\quad x^i\in\widetilde{\mathcal F}^i .
--   $$
--   A PNE of $\widetilde N$ is a pure Nash equilibrium of the simultaneous game with feasible sets $\widetilde{\mathcal F}^i$ and costs $f^i$. Step 4 of Algorithm 1 searches for one.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, p.11, and Algorithm 1, Steps 2–3, p.12

import Mathlib
import Definitions.Def_NashStackelberg_NASP_F

namespace NashStackelberg

/-- **The convexified strategy set `𝓕̃ⁱ := cl conv(𝓕ⁱ)` of the game `Ñ`** (Carvalho, Dragotto,
Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, p.11, and
Steps 2–3 of Algorithm 1, p.12).

In the convexified NASP `Ñ = (S̃¹, …, S̃ⁿ)` player `i` solves
`S̃ⁱ = min_{xⁱ} (cⁱ)ᵀ xⁱ + (Cⁱ x⁻ⁱ)ᵀ xⁱ  s.t.  xⁱ ∈ 𝓕̃ⁱ`: the costs are those of `N` and the
feasible region is the closure of the convex hull of `𝓕ⁱ`. A PNE of `Ñ` is
`IsPNE N.Ftilde N.cost`. -/
def NASP.Ftilde {n : ℕ} (N : NASP n) (i : Fin n) : Set (N.Var i → ℝ) :=
  closure (convexHull ℝ (N.F i))

end NashStackelberg


