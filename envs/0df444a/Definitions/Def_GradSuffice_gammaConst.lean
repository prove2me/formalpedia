-- Prove2me | Definitions.Def_GradSuffice_gammaConst
-- name    : GradSuffice_gammaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:33.419597+00:00
-- url     : https://prove2.me/theorems/eb65552b-2b52-4beb-bd24-76962e444a81
-- title:
--   The martingale constant $\gamma(m)$
-- statement:
--   For $m\ge1$, $\gamma(m)$ is the smallest constant such that every martingale $(\xi_1,\dots,\xi_m)$ of size $m$ in $X^\star$ (not necessarily binary) satisfies
--   $$\sqrt{\mathbb E\Big[\Big\|\frac1m\sum_{i=1}^m\xi_i\Big\|_\star^2\Big]}\ \le\ \gamma(m)\,\sup_i\sqrt{\mathbb E\big[\|\xi_i\|_\star^2\big]} .\tag{17}$$
--   By the triangle inequality $\gamma(m)\le1$.
--
--   **Formalization Note** $\gamma(m)$ is the infimum of the nonnegative constants for which (17) holds for every finitely supported martingale-difference law. Restricting to nonnegative constants changes nothing when $X\neq0$ and avoids the junk value of an infimum of a set unbounded below when $X=0$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §8, p.24, Eq. (17)

import Mathlib
import Definitions.Def_NondualOpt_FinLaw
import Definitions.Def_GradSuffice_IsMDSLaw

namespace GradSuffice

/-- **The martingale constant `γ(m)`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §8, p.24: "`γ(m)` is the infimal upper bound so
that for every martingale of size `m` (not necessarily binary):
`√(E[‖(1/m) ∑_{i=1}^m ξᵢ‖⋆²]) ≤ γ(m) supᵢ √(E[‖ξᵢ‖⋆²])`" (Eq. (17)).

**Formalization Note.** Martingales are finitely supported martingale-difference laws
(`IsMDSLaw`) in `X⋆`; expectations are finite weighted sums. The infimum is over nonnegative
constants (the ratio bounded in (17) is nonnegative); for `X ≠ 0` this is the same infimum, and it
keeps `γ` from taking the junk value of `sInf` of a set unbounded below when `X = 0`. For `m ≥ 1`
the set contains `1`. -/
noncomputable def gammaConst (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (m : ℕ) : ℝ :=
  sInf {γ : ℝ | 0 ≤ γ ∧ ∀ P : NondualOpt.FinLaw (Set.univ : Set (Fin m → StrongDual ℝ X)),
    IsMDSLaw P →
      √(∑ x ∈ P.w.support, P.w x * ‖(1 / (m : ℝ)) • ∑ i : Fin m, x i‖ ^ 2) ≤
        γ * ⨆ i : Fin m, √(∑ x ∈ P.w.support, P.w x * ‖x i‖ ^ 2)}

end GradSuffice


