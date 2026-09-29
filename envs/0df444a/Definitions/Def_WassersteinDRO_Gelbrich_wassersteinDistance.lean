-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_wassersteinDistance
-- name    : WassersteinDRO_Gelbrich_wassersteinDistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:23:19.922983+00:00
-- url     : https://prove2.me/theorems/bba194da-8763-41a3-bffb-e7f4757c4919
-- title:
--   Type-$p$ Wasserstein distance
-- statement:
--   The type-$p$ Wasserstein distance between two Borel probability measures $Q,Q'$ on
--   $\mathbb{R}^m$ is $W_p(Q,Q') = \left(\inf_\pi \int \|\xi-\xi'\|^p \, d\pi(\xi,\xi')\right)^{1/p}$,
--   the infimum over couplings $\pi$ of $Q$ and $Q'$ (probability measures on $\mathbb{R}^m \times
--   \mathbb{R}^m$ with the given marginals) of the $p$-th root of the expected $p$-th power of the
--   Euclidean distance.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Definition 1, p. 3, eq. (5)

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- The type-`p` Wasserstein distance between two Borel probability measures on `ℝ^m`
(`EuclideanSpace ℝ (Fin m)`, this chapter's fixed Euclidean norm), Kuhn et al. 2019,
Definition 1, p. 3, eq. (5). Redefined locally in this chapter's own namespace, matching
`01-duality`'s definition of the same name: `01-duality` is not yet a published mission, so a
draft item cannot import another draft (`CAPTAIN_ADDENDUM_WAVE2.md`, rule 5). -/
noncomputable def wassersteinDistance {m : ℕ} (p : ℝ)
    (Q Q' : Measure (EuclideanSpace ℝ (Fin m))) : ENNReal :=
  (⨅ (π : Measure (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))
      (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'),
      ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) ^ (1 / p)

end WassersteinDRO.Gelbrich


