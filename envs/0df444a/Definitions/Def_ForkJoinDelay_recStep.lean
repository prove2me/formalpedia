-- Prove2me | Definitions.Def_ForkJoinDelay_recStep
-- name    : ForkJoinDelay_recStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:07.433774+00:00
-- url     : https://prove2.me/theorems/cbe32d25-3d02-4bf5-a29a-bd41820f0898
-- title:
--   The right-hand side of the recursions (3) and (6)
-- statement:
--   For a table $g(x,y)$ of complex numbers and $h_1,h_2\ge0$,
--
--   $$\begin{aligned}\mathrm{step}(g)_{h_1,h_2}={}&\sum_{r_1=0}^{h_1-1}\sum_{r_2=0}^{h_2-1}g(h_1-r_1+1,h_2-r_2+1)\,a(r_1,r_2)+\sum_{r_1=0}^{h_1-1}g(h_1-r_1+1,1)\,b(r_1,h_2)\\&+\sum_{r_2=0}^{h_2-1}g(1,h_2-r_2+1)\,c(h_1,r_2)+g(1,1)\,d(h_1,h_2),\end{aligned}$$
--
--   with $a,b,c,d$ the coefficients of (4) and an empty sum equal to $0$. With $g=\Psi_{k-1,\cdot,\cdot}$ this is the right-hand side of (3); with $g=Z_{\cdot,\cdot}$ it is the right-hand side of (6).
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), Eq. (3), p.11; Eq. (6), p.12

import Mathlib
import Definitions.Def_ForkJoinDelay_coefA
import Definitions.Def_ForkJoinDelay_coefB
import Definitions.Def_ForkJoinDelay_coefC
import Definitions.Def_ForkJoinDelay_coefD

namespace ForkJoinDelay

/-- **The right-hand side of the recursions (3) and (6).**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, Eq. (3), p.11 and Eq. (6), p.12. For a table `g x y` (the
transforms `Ψ_{k−1,x,y}` in (3), the boundary transforms `Z_{x,y}` in (6)),

`step g h₁ h₂ = Σ_{r₁=0}^{h₁−1} Σ_{r₂=0}^{h₂−1} g(h₁−r₁+1, h₂−r₂+1) · a(r₁,r₂)
  + Σ_{r₁=0}^{h₁−1} g(h₁−r₁+1, 1) · b(r₁,h₂) + Σ_{r₂=0}^{h₂−1} g(1, h₂−r₂+1) · c(h₁,r₂)
  + g(1,1) · d(h₁,h₂)`.

**Formalization Note.** The finite sums run over `Finset.range h`, so they are empty for
`h = 0`, as p.11 ("an empty sum is defined to be zero") and p.13 prescribe. The natural
subtraction `h₁ - r₁` is exact because `r₁ < h₁`. -/
noncomputable def recStep (μ₀ μ₁ μ₂ : ℝ) (w₀ : ℂ) (g : ℕ → ℕ → ℂ) (h₁ h₂ : ℕ) : ℂ :=
  (∑ r₁ ∈ Finset.range h₁, ∑ r₂ ∈ Finset.range h₂,
      g (h₁ - r₁ + 1) (h₂ - r₂ + 1) * coefA μ₀ μ₁ μ₂ w₀ r₁ r₂) +
    (∑ r₁ ∈ Finset.range h₁, g (h₁ - r₁ + 1) 1 * coefB μ₀ μ₁ μ₂ w₀ r₁ h₂) +
    (∑ r₂ ∈ Finset.range h₂, g 1 (h₂ - r₂ + 1) * coefC μ₀ μ₁ μ₂ w₀ h₁ r₂) +
    g 1 1 * coefD μ₀ μ₁ μ₂ w₀ h₁ h₂

end ForkJoinDelay


