-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_meanVector
-- name    : WassersteinDRO_Guarantees_meanVector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:29:58.272428+00:00
-- url     : https://prove2.me/theorems/acf78f2b-9662-4db9-8527-ed15de28d5f4
-- title:
--   Mean vector of a probability measure
-- statement:
--   The mean vector of a probability measure $Q$ on $\mathbb{R}^m$ is $E_Q[\xi] = \int \xi \, dQ(\xi)$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, INFORMS TutORials 2019, used throughout

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The mean vector of a probability measure `Q` on `ℝ^m`, `E_Q[ξ]`, used throughout Kuhn et
al. 2019. Redefined locally in this chapter's own namespace, matching `02-gelbrich`'s
definition of the same name: `02-gelbrich` is not yet a published mission, so a draft item
cannot import another draft (`CAPTAIN_ADDENDUM_WAVE2.md`, rule 5). -/
noncomputable def meanVector {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin m) :=
  ∫ x, x ∂Q

end WassersteinDRO.Guarantees


