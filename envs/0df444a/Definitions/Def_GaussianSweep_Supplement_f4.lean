-- Prove2me | Definitions.Def_GaussianSweep_Supplement_f4
-- name    : GaussianSweep_Supplement_f4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:35:56.230086+00:00
-- url     : https://prove2.me/theorems/494df2cc-ea6a-4e95-be82-0562eab4b497
-- title:
--   Ideal 4-star function $f_{4,r}(\tau)$
-- statement:
--   Let $Z$ be standard normal and $U^*$ the regular simplex vector in four variables, independent of $Z$. For $r \in (0,1)$ put $s_r = \sqrt{1-r^2}$ and
--   $$
--   Y^*_0 = Z, \qquad Y^*_i = rZ + s_r U^*_i \quad (1 \le i \le 4).
--   $$
--   The **ideal 4-star function** is
--   $$
--   f_{4,r}(\tau) = \mathbb P\Big(Y^*_0 > \tau,\ \min_{1\le i\le 4} Y^*_i \le \tau\Big) \qquad (\tau \in \mathbb R).
--   $$
--   Its supremum over $\tau$ at $r = \sqrt3/2$ is the constant $F_4$ of the maximum-degree-4 bounds.
--
--   **Formalization Note** The probability space is $\mathbb R \times \mathbb R^3$ with the product of $N(0,1)$ (the coordinate $Z$) and the standard Gaussian measure on $\mathbb R^3$, exactly as for the published ideal 3-star function `GaussianSweep.f3`. The function is defined for all real $r, \tau$; the paper uses $r \in (0,1)$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 6.7, p.37 (PDF p.39), d = 4

import Mathlib
import Definitions.Def_GaussianSweep_Supplement_simplexVec4
open MeasureTheory ProbabilityTheory

namespace GaussianSweep.Supplement

/-- The ideal 4-star function `f_{4,r}(τ) = P(Y*₀ > τ, minᵢ Y*ᵢ ≤ τ)`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 6.7, p.37 (PDF p.39), with `d = 4`), where `Y*₀ = Z` is
standard normal, `U*` is the regular simplex vector in four variables independent of `Z`, and
`Y*ᵢ = rZ + s_r U*ᵢ` (`1 ≤ i ≤ 4`), `s_r = √(1 − r²)`.

**Formalization Note** As for the published `GaussianSweep.f3`: the probability space is
`ℝ × ℝ³` with the product of `N(0, 1)` (the coordinate `Z`) and the standard Gaussian on
`EuclideanSpace ℝ (Fin 3)` (the vector whose projections give `U*`, see `simplexVec4`).
`minᵢ Y*ᵢ ≤ τ` is "some `Y*ᵢ ≤ τ`". Defined for every real `r` and `τ`; the paper uses
`r ∈ (0, 1)`. -/
noncomputable def f4 (r τ : ℝ) : ℝ :=
  ((gaussianReal 0 1).prod (stdGaussian (EuclideanSpace ℝ (Fin 3)))).real
    {ω | τ < ω.1 ∧ ∃ k : Fin 4, r * ω.1 + Real.sqrt (1 - r ^ 2) * simplexVec4 k ω.2 ≤ τ}

end GaussianSweep.Supplement


