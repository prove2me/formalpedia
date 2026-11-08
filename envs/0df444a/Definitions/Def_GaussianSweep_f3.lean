-- Prove2me | Definitions.Def_GaussianSweep_f3
-- name    : GaussianSweep_f3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:58.035026+00:00
-- url     : https://prove2.me/theorems/742f8f30-3d68-4538-b88b-b763e4c05d58
-- title:
--   Ideal 3-star function $f_{3,r}(\tau)$
-- statement:
--   Let $r \in (0,1)$, $s_r = \sqrt{1-r^2}$, let $Z$ be standard normal and $U^*$ the regular simplex vector in three variables, independent of $Z$. The ideal 3-star at correlation $r$ is $Y^*_0 = Z$, $Y^*_i = rZ + s_r U^*_i$ ($i = 1, 2, 3$), and its **ideal star function** is
--   $$
--   f_{3,r}(\tau) = \mathbb P\Big(Y^*_0 > \tau,\ \min_i Y^*_i \le \tau\Big) \qquad (\tau \in \mathbb R).
--   $$
--   It is the probability that the center of the ideal star lies in the outer frontier at threshold $\tau$.
--
--   **Formalization Note** The probability space is $\mathbb R \times \mathbb R^2$ with $N(0,1) \otimes N(0, I_2)$; the first coordinate is $Z$ and the planar coordinate gives $U^*$ through `simplexVec`. Defined for all real $r, \tau$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 6.7, p.37 (PDF p.39), d = 3; Section 8.3, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_GaussianSweep_simplexVec
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- The ideal 3-star function `f_{3,r}(τ) = P(Y*₀ > τ, minᵢ Y*ᵢ ≤ τ)` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 6.7,
p.37 (PDF p.39), with `d = 3`), where `Y*₀ = Z` is standard normal, `U*` is the regular simplex
vector in three variables independent of `Z`, and `Y*ᵢ = rZ + s_r U*ᵢ`, `s_r = √(1 − r²)`.

**Formalization Note** The probability space is `ℝ × ℝ²` with the product of `N(0, 1)` (the
coordinate `Z`) and the standard Gaussian on `EuclideanSpace ℝ (Fin 2)` (the planar vector whose
projections give `U*`, see `simplexVec`). Defined for every real `r` and `τ`; the paper uses
`r ∈ (0, 1)`. -/
noncomputable def f3 (r τ : ℝ) : ℝ :=
  ((gaussianReal 0 1).prod (stdGaussian (EuclideanSpace ℝ (Fin 2)))).real
    {ω | τ < ω.1 ∧ ∃ k : Fin 3, r * ω.1 + Real.sqrt (1 - r ^ 2) * simplexVec k ω.2 ≤ τ}

end GaussianSweep


