-- Prove2me | Definitions.Def_GaussianSweep_Supplement_F3
-- name    : GaussianSweep_Supplement_F3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:36:37.036571+00:00
-- url     : https://prove2.me/theorems/11917d5f-baa3-42e4-894c-bb859b4bbc8b
-- title:
--   The constant $F_3 = \sup_\tau f_{3,2\sqrt2/3}(\tau)$
-- statement:
--   With $f_{3,r}$ the ideal 3-star function and $r_{33} = 2\sqrt2/3$,
--   $$
--   F_3 = \sup_{\tau \in \mathbb R} f_{3,r_{33}}(\tau) \approx 0.1401583 .
--   $$
--
--   **Formalization Note** The supremum itself (`⨆ τ`), never the numerical enclosure of Proposition 6.9. The family is a family of probabilities, nonempty and bounded above by $1$, so the real supremum is the true supremum. $f_{3,r}$ is the published `GaussianSweep.f3`.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 6.7, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_GaussianSweep_f3

namespace GaussianSweep.Supplement

/-- The constant `F₃ := sup_{τ∈ℝ} f_{3,r₃₃}(τ)`, `r₃₃ = 2√2/3`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 6.7, p.37 (PDF p.39)), with `f_{3,r}` the published
ideal 3-star function `GaussianSweep.f3`. Numerically `F₃ ≈ 0.1401583` (Proposition 6.9).

**Formalization Note** The supremum itself, as `⨆ τ : ℝ` in `ℝ`; the family is nonempty and
bounded above by `1` (it is a probability), so `⨆` is the true supremum. -/
noncomputable def F3 : ℝ := ⨆ τ : ℝ, GaussianSweep.f3 (2 * Real.sqrt 2 / 3) τ

end GaussianSweep.Supplement


