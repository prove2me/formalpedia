-- Prove2me | Definitions.Def_Esgk_ConfigurationCentroid
-- name    : Esgk_ConfigurationCentroid
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-20T05:02:02.815026+00:00
-- url     : https://prove2.me/theorems/52f42687-211f-4f96-ab23-1c41aff759ba
-- title:
--   Centroid of an indexed planar configuration
-- statement:
--   For an indexed configuration $p=(p_1,\dots,p_n)$ of $n$ points in the plane, `configCentroid p` is the centroid
--
--   $$
--   c(p)=\frac1n\sum_{j=1}^n p_j .
--   $$
--
--   It is the center of the annulus that contains a configuration with few distinct distances and no four points on a common circle, in the theorem `Esgk.thin_annulus_sq_of_noFourCocircular`.
--
--   **Formalization Note** The configuration is a map `Fin n → ℝ²`. For $n=0$ the formula gives the origin, because the Lean inverse of $0$ is $0$.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_Foundation

namespace Esgk

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

noncomputable def configCentroid (p : Config n) : Point :=
  (n : ℝ)⁻¹ • ∑ j, p j

end Esgk


