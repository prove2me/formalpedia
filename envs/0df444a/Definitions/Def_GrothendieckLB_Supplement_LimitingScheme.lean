-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_LimitingScheme
-- name    : GrothendieckLB_Supplement_LimitingScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:36:32.791382+00:00
-- url     : https://prove2.me/theorems/559fb70b-c078-4c10-9e8c-6fdf4e97f78f
-- title:
--   Limiting Krivine scheme (Definition 3.6)
-- statement:
--   A $k$-dimensional **limiting Krivine scheme** is a tuple $S=(f,g,\rho)$ where
--
--   1. $f,g:\mathbb R^k\to\{-1,1\}$ are odd measurable functions,
--   2. the discontinuity sets of $f$ and of $g$ have Gaussian measure zero, and
--   3. $\rho=(\rho_1,\dots,\rho_k)$ is a tuple of allowable correlation maps (Definition 3.5).
--
--   With $\rho_i(t)=t$ for all $i$ this is an ordinary Krivine scheme. Limiting schemes describe limits of high-dimensional ordinary schemes in a fixed low dimension.
--
--   **Formalization Note** The pair $(f,g)$ is the published `KrivineScheme k` (measurable, $\pm1$-valued, odd almost everywhere, since no $\pm1$-valued function is odd at the origin). Gaussian measure and Lebesgue measure have the same null sets, so the discontinuity condition is stated with Lebesgue measure.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.6, p.18

import Mathlib
import Definitions.Def_KrivineSchemeDefs
import Definitions.Def_GrothendieckLB_Supplement_IsAllowableCorr
open MeasureTheory

namespace GrothendieckLB

namespace Supplement

/-- A `k`-dimensional limiting Krivine scheme `S = (f, g, ρ)` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.6, p.18):
`f, g : ℝ^k → {−1, 1}` odd measurable functions whose discontinuity sets have Gaussian measure
zero, and `ρ = (ρ₁, …, ρ_k)` a tuple of allowable correlation maps (Definition 3.5).

**Formalization Note** The pair `(f, g)` is the published `GrothendieckConstant.KrivineScheme k`
(measurable, `±1`-valued, odd almost everywhere: no `±1`-valued function is odd at the origin).
The discontinuity set of `f` is `{z | ¬ ContinuousAt f z}`; Gaussian and Lebesgue measure have
the same null sets, so "Gaussian measure zero" is written with `volume`. Coordinates are
indexed by `Fin k` (0-based). -/
structure LimitingScheme (k : ℕ) extends GrothendieckConstant.KrivineScheme k where
  /-- The discontinuity set of `f` is null. -/
  f_disc_null : volume {z : Fin k → ℝ | ¬ ContinuousAt f z} = 0
  /-- The discontinuity set of `g` is null. -/
  g_disc_null : volume {z : Fin k → ℝ | ¬ ContinuousAt g z} = 0
  /-- The correlation maps `ρ₁, …, ρ_k`. -/
  ρ : Fin k → ℝ → ℝ
  /-- Each `ρ_i` is allowable. -/
  ρ_allowable : ∀ i, IsAllowableCorr (ρ i)

end Supplement

end GrothendieckLB


