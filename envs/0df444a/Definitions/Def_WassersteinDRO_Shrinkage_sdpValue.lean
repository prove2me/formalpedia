-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_sdpValue
-- name    : WassersteinDRO_Shrinkage_sdpValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:51:39.578984+00:00
-- url     : https://prove2.me/theorems/159ebe7c-eed1-454f-9ccd-431a41ddc023
-- title:
--   Optimal value of the nonlinear convex SDP (36)
-- statement:
--   The optimal value of SDP (36) is $\max_{S \in \text{feasible set}} f(S)$, valued in the
--   extended reals.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, eq. (36), p. 29

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet
import Definitions.Def_WassersteinDRO_Shrinkage_sdpObjective

namespace WassersteinDRO.Shrinkage

/-- The optimal value of the nonlinear convex SDP (36), Kuhn et al. 2019, p. 29:
`max_{S ∈ feasible set} f(S)`. Valued in `EReal` so the supremum is a genuine least upper
bound with no junk value, matching the series' convention for worst-case-risk-style suprema. -/
noncomputable def sdpValue {mx my : ℕ} (ε : ℝ)
    (SigmaHat : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ) (lambdaMin : ℝ) : EReal :=
  ⨆ (S : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ)
    (_ : S ∈ sdpFeasibleSet ε SigmaHat lambdaMin), (sdpObjective S : EReal)

end WassersteinDRO.Shrinkage


