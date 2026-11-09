-- Prove2me | Definitions.Def_GevreyGibbsSep_partitionFn
-- name    : GevreyGibbsSep_partitionFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:41.170729+00:00
-- url     : https://prove2.me/theorems/e8f2275f-b3e3-4651-9431-47ca2fcf9300
-- title:
--   Partition function $Z_V=\int_{[0,2\pi)^d}e^{-V}$
-- statement:
--   For a scaled potential $V=\beta E$, the **partition function** is
--   $$Z_V=\int_{[0,2\pi)^d}e^{-V(x)}\,dx .$$
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (1), p.5; Definition B.1, Eq. (B1), p.34

import Mathlib
import Definitions.Def_GevreyGibbsSep_periodCube

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The partition function `Z_V = ∫_{[0,2π)^d} e^{−V(x)} dx` of a potential `V` (for `V = βE`
this is `Z` of Eq. (1), p.5, and of Definition B.1, Eq. (B1), p.34, arXiv:2608.24527
(sha256 d4fd40eb…)). -/
noncomputable def partitionFn {d : ℕ} (V : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x in periodCube d, Real.exp (- V x)

end GevreyGibbsSep


