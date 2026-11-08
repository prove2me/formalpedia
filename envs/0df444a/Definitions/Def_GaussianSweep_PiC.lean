-- Prove2me | Definitions.Def_GaussianSweep_PiC
-- name    : GaussianSweep_PiC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:07.756692+00:00
-- url     : https://prove2.me/theorems/bb7e3227-a9ad-462a-9578-8c9d57f85c75
-- title:
--   Two-exceedance probability $\Pi_C(h)$
-- statement:
--   For a $3 \times 3$ correlation matrix $C$ (positive semidefinite, unit diagonal) and $h > 0$,
--   $$
--   \Pi_C(h) = \mathbb P_C\big(\text{at least two of } \eta_1, \eta_2, \eta_3 \text{ exceed } h\big), \qquad \eta \sim N(0, C).
--   $$
--   It enters the switch lemma through the residuals of a star at threshold zero.
--
--   **Formalization Note** $N(0, C)$ is Mathlib's `multivariateGaussian 0 C` on $\mathbb R^3$; for a matrix that is not positive semidefinite this is a Dirac mass, and the results assume positive semidefiniteness.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 8.4, p.52 (PDF p.54)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- `Π_C(h) = P_C(at least two of η₁, η₂, η₃ exceed h)`, `η ∼ N(0, C)` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 8.4, p.52
(PDF p.54)).

**Formalization Note** `N(0, C)` is Mathlib's `multivariateGaussian 0 C` on
`EuclideanSpace ℝ (Fin 3)`. The paper uses `Π_C` for correlation matrices `C` (positive
semidefinite, unit diagonal) and `h > 0`; for a matrix that is not positive semidefinite Mathlib's
measure is a Dirac mass, and the lemmas exclude that case by hypothesis. -/
noncomputable def PiC (C : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) : ℝ :=
  (multivariateGaussian 0 C).real {η | 2 ≤ (Finset.univ.filter fun i => h < η i).card}

end GaussianSweep


