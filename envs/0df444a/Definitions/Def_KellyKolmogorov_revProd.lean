-- Prove2me | Definitions.Def_KellyKolmogorov_revProd
-- name    : KellyKolmogorov_revProd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:40:06.339636+00:00
-- url     : https://prove2.me/theorems/96d1322e-770d-4ea2-92e7-b39f74434ce3
-- title:
--   Product of weights along a path traversed backwards
-- statement:
--   For nonnegative weights $w(j,k)$ on a set $\mathcal S$ and a finite sequence of states $a_0,a_1,\dots,a_m$, the product along the reversed path is
--   $$
--   w(a_1,a_0)\,w(a_2,a_1)\cdots w(a_m,a_{m-1}),
--   $$
--   equal to $1$ for a sequence with a single state. In the proof of Theorem 1.7 it is the numerator $p(j_0,j_1)p(j_1,j_2)\cdots p(j_n,j)$ of the potential
--   $$
--   \pi(j)=B\,\frac{p(j_0,j_1)p(j_1,j_2)\cdots p(j_n,j)}{p(j,j_n)p(j_n,j_{n-1})\cdots p(j_1,j_0)} .
--   $$
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25)

import Mathlib

open scoped NNReal

namespace KellyKolmogorov

/-- **Product of weights along a path traversed backwards.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22: for a
sequence of states `j, jₙ, jₙ₋₁, …, j₁, j₀` the product `p(j₀, j₁)p(j₁, j₂) ⋯ p(jₙ, j)`, the
numerator of `π(j) = B p(j₀, j₁)p(j₁, j₂) ⋯ p(jₙ, j) / (p(j, jₙ)p(jₙ, jₙ₋₁) ⋯ p(j₁, j₀))`.

`revProd w [a₀, a₁, …, aₘ] = w(a₁, a₀) w(a₂, a₁) ⋯ w(aₘ, aₘ₋₁)`; it is `1` for a path with one
state (or none). -/
def revProd {𝒮 : Type*} (w : 𝒮 → 𝒮 → ℝ≥0) (l : List 𝒮) : ℝ≥0 :=
  (List.zipWith (fun a b => w b a) l l.tail).prod

end KellyKolmogorov


