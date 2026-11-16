-- Prove2me | Definitions.Def_GaussianSweep_Supplement_F4__069df8
-- name    : GaussianSweep_Supplement_F4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:37:15.800839+00:00
-- url     : https://prove2.me/theorems/069df8ef-f941-495c-9919-3b859f52772f
-- title:
--   The constant $F_4 = \sup_\tau f_{4,\sqrt3/2}(\tau)$
-- statement:
--   With $f_{4,r}$ the ideal 4-star function and $r_{44} = \sqrt3/2$,
--   $$
--   F_4 = \sup_{\tau \in \mathbb R} f_{4,r_{44}}(\tau) \approx 0.2457720 .
--   $$
--
--   **Formalization Note** The supremum itself (`⨆ τ`), never the numerical enclosure of Proposition 6.9; the family is nonempty and bounded above by $1$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 6.7, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_GaussianSweep_Supplement_f4

namespace GaussianSweep.Supplement

/-- The constant `F₄ := sup_{τ∈ℝ} f_{4,r₄₄}(τ)`, `r₄₄ = √3/2`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 6.7, p.37 (PDF p.39)). Numerically `F₄ ≈ 0.2457720`
(Proposition 6.9).

**Formalization Note** The supremum itself, as `⨆ τ : ℝ` in `ℝ`; the family is nonempty and
bounded above by `1` (it is a probability), so `⨆` is the true supremum. -/
noncomputable def F4 : ℝ := ⨆ τ : ℝ, f4 (Real.sqrt 3 / 2) τ

end GaussianSweep.Supplement


