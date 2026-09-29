-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_gelbrichRisk
-- name    : WassersteinDRO_Guarantees_gelbrichRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:33:48.852606+00:00
-- url     : https://prove2.me/theorems/9c38836f-a274-4bbc-93ae-8f42b466792e
-- title:
--   Gelbrich risk $R_\varepsilon(\hat\mu,\hat\Sigma,\ell)$
-- statement:
--   $R_\varepsilon(\hat\mu,\hat\Sigma,\ell) = \sup_{Q \in G_\varepsilon(\hat\mu,\hat\Sigma)}
--   E_Q[\ell(\xi)]$, valued in the extended reals and restricted to distributions under which
--   $\ell$ is integrable.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, eq. (18), p. 18

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_gelbrichHull
import Definitions.Def_WassersteinDRO_Guarantees_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The Gelbrich risk `R_ε(µ̂,Ŝ,ℓ)`, Kuhn et al. 2019, eq. (18), p. 18. Redefined locally in
this chapter's own namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. Valued
in `EReal` and guarded by `Integrable ℓ Q`. -/
noncomputable def gelbrichRisk {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) : EReal :=
  ⨆ (Q : Measure (EuclideanSpace ℝ (Fin m))) (_ : Q ∈ gelbrichHull ε Ξ μhat SigmaHat)
    (_ : Integrable ℓ Q), (nominalRisk Q ℓ : EReal)

end WassersteinDRO.Guarantees


