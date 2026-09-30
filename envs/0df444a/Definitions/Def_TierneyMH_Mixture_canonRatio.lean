-- Prove2me | Definitions.Def_TierneyMH_Mixture_canonRatio
-- name    : TierneyMH_Mixture_canonRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T02:00:38.137233+00:00
-- url     : https://prove2.me/theorems/d1d073f0-d8c1-4212-ae34-d1c7b539dac8
-- title:
--   The ratio $r(x,y) = h(x,y)/h(y,x)$ on $R$, $r = 1$ on $R^c$
-- statement:
--   Let $\mu(dx,dy)=\pi(dx)Q(x,dy)$, let $h=d\mu/d(\mu+\mu^T)$ be the density and $R$ the set of the proof of Proposition 1. The ratio $r$ is
--
--   $$r(x,y)=\begin{cases} h(x,y)/h(y,x), & (x,y)\in R,\\ 1, & (x,y)\notin R.\end{cases}$$
--
--   On $R$ it measures the relative rate of transitions from $x$ to $y$ and from $y$ to $x$ under the proposal chain started from $\pi$; the paper notes that "the function $r(x, y)$ can be set to one on $R^c$".
--
--   **Formalization Note** On the subset of $R$ where $h(x,y)=\infty$ or $h(y,x)=\infty$, a set null for $\mu+\mu^T$, the value is also set to $1$. This choice of version makes $0<r<\infty$ and $r(x,y)=1/r(y,x)$ hold at every point, as Proposition 1 asks of its version.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 2, proof of Proposition 1 (the ratio r)

import Mathlib
import Definitions.Def_TierneyMH_Mixture_canonDensity
import Definitions.Def_TierneyMH_Mixture_canonR

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

open scoped Classical in
/-- The ratio `r` of the proof of Proposition 1 (Tierney 1998, p. 2) for
`μ(dx, dy) = π(dx) Q(x, dy)`: `r(x, y) = h(x, y) / h(y, x)` on `R = canonR π Q`, and
`r = 1` on `Rᶜ` ("the function `r(x, y)` can be set to one on `Rᶜ`"), where
`h = canonDensity π Q`.

On the `(μ + μᵀ)`-null subset of `R` where `h(x, y) = ∞` or `h(y, x) = ∞` the value is also
set to `1`, so that `0 < r(x, y) < ∞` and `r(x, y) = 1 / r(y, x)` hold for **all** `(x, y)`,
as Proposition 1 requires of its version. -/
noncomputable def canonRatio {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E) :
    E × E → ℝ≥0∞ := fun p =>
  if p ∈ canonR π Q ∧ canonDensity π Q p ≠ ⊤ ∧ canonDensity π Q p.swap ≠ ⊤ then
    canonDensity π Q p / canonDensity π Q p.swap
  else 1

end TierneyMH.Mixture


