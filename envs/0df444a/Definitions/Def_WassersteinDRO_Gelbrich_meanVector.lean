-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_meanVector
-- name    : WassersteinDRO_Gelbrich_meanVector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:21:32.245976+00:00
-- url     : https://prove2.me/theorems/d3d5a887-368e-4b69-b2d2-656b301c3477
-- title:
--   Mean vector of a probability measure
-- statement:
--   The mean vector of a probability measure $Q$ on $\mathbb{R}^m$ is $E_Q[\xi] = \int \xi \, dQ(\xi)$,
--   the Bochner integral of the identity map against $Q$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, INFORMS TutORials 2019, used throughout Section 2.3, e.g. Theorem 4 p. 8, Proposition 1 p. 16

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- The mean vector of a probability measure `Q` on `ℝ^m`, `E_Q[ξ]`, used throughout Section
2.3 of Kuhn et al. 2019 (e.g. Theorem 4, p. 8; Proposition 1, p. 16). -/
noncomputable def meanVector {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin m) :=
  ∫ x, x ∂Q

end WassersteinDRO.Gelbrich


