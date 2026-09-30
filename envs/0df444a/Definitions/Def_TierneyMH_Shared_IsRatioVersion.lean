-- Prove2me | Definitions.Def_TierneyMH_Shared_IsRatioVersion
-- name    : TierneyMH_Shared_IsRatioVersion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T11:37:07.978345+00:00
-- url     : https://prove2.me/theorems/2b6efd11-4381-4d92-a5f5-2b151eecb9d4
-- title:
--   Version $r$ of $d\mu_R/d\mu^T_R$ with $0<r<\infty$ and $r(x,y)=1/r(y,x)$ everywhere
-- statement:
--   Let $\mu$ be a measure on $E\times E$ with transpose $\mu^T(dx,dy)=\mu(dy,dx)$, let $R\subseteq E\times E$, and let $\mu_R$, $\mu^T_R$ be the restrictions of $\mu$ and $\mu^T$ to $R$. A function $r : E\times E\to[0,\infty]$ is a **ratio version** for $(\mu,R)$ if $r$ is measurable,
--
--   $$0<r(x,y)<\infty\quad\text{and}\quad r(x,y)=\frac{1}{r(y,x)}\qquad\text{for all }x,y\in E,$$
--
--   and $r$ is a density of $\mu_R$ with respect to $\mu^T_R$, that is $\mu_R(dx,dy) = r(x,y)\,\mu^T_R(dx,dy)$.
--
--   The positivity, finiteness and reciprocity hold at every point, not merely almost everywhere. Proposition 1 shows that such a version exists whenever $R$ is a symmetric split for a $\sigma$-finite $\mu$; Theorem 2 expresses detailed balance of a Metropolis–Hastings kernel through $r$.
--
--   It is shared by two missions of this series and reviewed once for both: `01-reversibility` (Proposition 1, p. 2, and the function $r$ of Theorem 2, p. 3) and `03-mixture-proposals` (Proposition 1, p. 2, for the density $r$ from which $\alpha_{MH}$ is built, p. 3).
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 2, Proposition 1 (the density r)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace TierneyMH.Shared

/-- `IsRatioVersion μ R r` (Tierney 1998, Proposition 1, p. 2): `r : E × E → [0, ∞]` is a
version of the Radon–Nikodym density `r(x, y) = μ_R(dx, dy) / μᵀ_R(dx, dy)` of the restriction
`μ_R` of `μ` to `R` with respect to the restriction `μᵀ_R` of `μᵀ = μ.map Prod.swap` to `R`,
chosen so that **for all** `x, y` (everywhere, not almost everywhere)
`0 < r(x, y) < ∞` and `r(x, y) = 1 / r(y, x)`. Measurability of `r` is part of being a version
of a density. -/
def IsRatioVersion {E : Type*} [MeasurableSpace E] (μ : Measure (E × E)) (R : Set (E × E))
    (r : E × E → ℝ≥0∞) : Prop :=
  Measurable r ∧ (∀ p, 0 < r p ∧ r p < ⊤) ∧ (∀ p, r p.swap = (r p)⁻¹) ∧
    μ.restrict R = ((μ.map Prod.swap).restrict R).withDensity r

end TierneyMH.Shared


