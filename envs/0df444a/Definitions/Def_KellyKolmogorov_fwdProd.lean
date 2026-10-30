-- Prove2me | Definitions.Def_KellyKolmogorov_fwdProd
-- name    : KellyKolmogorov_fwdProd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:39:53.194037+00:00
-- url     : https://prove2.me/theorems/f6a5383b-3cb9-42dd-988e-695d7948ea3a
-- title:
--   Product of weights along a path
-- statement:
--   For nonnegative weights $w(j,k)$ on a set $\mathcal S$ and a finite sequence of states $a_0,a_1,\dots,a_m$, the product along the path is
--   $$
--   w(a_0,a_1)\,w(a_1,a_2)\cdots w(a_{m-1},a_m),
--   $$
--   equal to $1$ for a sequence with a single state. In the proof of Theorem 1.7 it is the denominator $p(j,j_n)p(j_n,j_{n-1})\cdots p(j_1,j_0)$ of the potential $\pi(j)$.
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25)

import Mathlib

open scoped NNReal

namespace KellyKolmogorov

/-- **Product of weights along a path.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22: for a
sequence of states `j, jₙ, jₙ₋₁, …, j₁, j₀` the product `p(j, jₙ)p(jₙ, jₙ₋₁) ⋯ p(j₁, j₀)`.

`fwdProd w [a₀, a₁, …, aₘ] = w(a₀, a₁) w(a₁, a₂) ⋯ w(aₘ₋₁, aₘ)`; it is `1` for a path with one
state (or none). -/
def fwdProd {𝒮 : Type*} (w : 𝒮 → 𝒮 → ℝ≥0) (l : List 𝒮) : ℝ≥0 :=
  (List.zipWith w l l.tail).prod

end KellyKolmogorov


