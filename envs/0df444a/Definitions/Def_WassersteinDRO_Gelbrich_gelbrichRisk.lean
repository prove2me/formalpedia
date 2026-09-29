-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_gelbrichRisk
-- name    : WassersteinDRO_Gelbrich_gelbrichRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:26:07.127985+00:00
-- url     : https://prove2.me/theorems/d292f699-9087-4af5-8f6d-8f3ceea93ef0
-- title:
--   Gelbrich risk $R_\varepsilon(\hat\mu,\hat\Sigma,\ell)$
-- statement:
--   The Gelbrich risk of a loss function $\ell$ is
--   $R_\varepsilon(\hat\mu,\hat\Sigma,\ell) = \sup_{Q \in G_\varepsilon(\hat\mu,\hat\Sigma)} E_Q[\ell(\xi)]$,
--   the worst-case risk of $\ell$ over the Gelbrich hull in place of the (generally intractable)
--   Wasserstein ambiguity set. Valued in the extended reals and restricted to distributions under
--   which $\ell$ is integrable, to avoid an undefined expectation.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, eq. (18), p. 18

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_gelbrichHull
import Definitions.Def_WassersteinDRO_Gelbrich_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- The Gelbrich risk `R_ε(µ̂,Ŝ,ℓ)`, Kuhn et al. 2019, eq. (18), p. 18: the worst-case risk of
`ℓ` over the Gelbrich hull, in place of the (generally intractable) Wasserstein ambiguity set.
Valued in `EReal` and guarded by `Integrable ℓ Q`, for the same reason as `worstCaseRisk`. -/
noncomputable def gelbrichRisk {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) : EReal :=
  ⨆ (Q : Measure (EuclideanSpace ℝ (Fin m))) (_ : Q ∈ gelbrichHull ε Ξ μhat SigmaHat)
    (_ : Integrable ℓ Q), (nominalRisk Q ℓ : EReal)

end WassersteinDRO.Gelbrich


