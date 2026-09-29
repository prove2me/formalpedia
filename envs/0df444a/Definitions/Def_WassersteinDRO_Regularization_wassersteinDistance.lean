-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_wassersteinDistance
-- name    : WassersteinDRO_Regularization_wassersteinDistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:38:03.704829+00:00
-- url     : https://prove2.me/theorems/e09c863f-7201-4788-b8b7-65cb5c4fb5a4
-- title:
--   Type-$p$ Wasserstein distance
-- statement:
--   The type-$p$ Wasserstein distance between two Borel probability measures $Q,Q'$ on a normed
--   space $E$ is $W_p(Q,Q') = \left(\inf_\pi \int \|\xi-\xi'\|^p \, d\pi(\xi,\xi')\right)^{1/p}$,
--   the infimum over couplings $\pi$ of $Q,Q'$ of the $p$-th root of the expected $p$-th power of
--   the distance.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, INFORMS TutORials 2019, Definition 1, p. 3, eq. (5)

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- The type-`p` Wasserstein distance between two Borel probability measures on a normed
space `E`, Kuhn et al. 2019, Definition 1, p. 3, eq. (5). Redefined locally in this
chapter's own namespace, matching `01-duality`'s definition of the same name: `01-duality`
is not yet a published mission, so a draft item cannot import another draft
(`CAPTAIN_ADDENDUM_WAVE2.md`, rule 5). -/
noncomputable def wassersteinDistance {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (p : ℝ) (Q Q' : Measure E) : ENNReal :=
  (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'),
      ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) ^ (1 / p)

end WassersteinDRO.Regularization


