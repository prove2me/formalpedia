-- Prove2me | Definitions.Def_Esgk_ThinAnnulus
-- name    : Esgk_ThinAnnulus
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-20T05:04:56.286403+00:00
-- url     : https://prove2.me/theorems/9495f630-3022-43be-911b-af76a3c4fba9
-- title:
--   Centroid mass and the distance-annulus radius
-- statement:
--   For an indexed configuration $p=(p_1,\dots,p_n)$ of points in the plane with centroid $c(p)$ (`configCentroid p`) and distance values $R(p)=\{|p_i-p_j|: i\ne j\}$, this module defines three real numbers.
--
--   1. `centroidSquaredMass p`: $M(p)=\sum_{i}|p_i-c(p)|^2$.
--   2. `distanceAnnulusRadiusSq p`:
--   $$
--   \rho^2(p)=\frac1n\Bigl(3\sum_{r\in R(p)}r^2-M(p)\Bigr).
--   $$
--   3. `distanceAnnulusRadius p`: the real square root $\rho(p)=\sqrt{\rho^2(p)}$.
--
--   For an injective configuration with $n\ge1$ and no four points on a common circle, every $|p_i-c(p)|^2$ is at most $\rho^2(p)$, and the theorem `Esgk.thin_annulus_sq_of_noFourCocircular` bounds it from below in terms of the number of distinct distances.
--
--   **Formalization Note** The quantity $\rho^2(p)$ is a formula, not a square, and `distanceAnnulusRadius` applies `Real.sqrt`, which returns $0$ for negative arguments. For $n=0$ the division by $n$ gives $0$ in Lean.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_ConfigurationCentroid

namespace Esgk

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

noncomputable def centroidSquaredMass (p : Config n) : ℝ :=
  ∑ i, dist (p i) (configCentroid p) ^ 2

noncomputable def distanceAnnulusRadiusSq (p : Config n) : ℝ :=
  (3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) - centroidSquaredMass p) / (n : ℝ)

noncomputable def distanceAnnulusRadius (p : Config n) : ℝ :=
  Real.sqrt (distanceAnnulusRadiusSq p)

end Esgk


