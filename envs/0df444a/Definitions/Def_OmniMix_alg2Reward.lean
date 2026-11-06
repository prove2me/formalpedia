-- Prove2me | Definitions.Def_OmniMix_alg2Reward
-- name    : OmniMix_alg2Reward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:45.671743+00:00
-- url     : https://prove2.me/theorems/92f39538-876e-4afb-a4f2-6938aa95d79e
-- title:
--   Expert reward $z_{t,f,v}$ of Algorithm 2
-- statement:
--   For forecasts $D_t$, contexts $x_t$, outcomes $y_t$, a predictor $f$ and a threshold $v$,
--   $$
--   z_{t,f,v}=\mathbb E_{P\sim D_t}\big[b_v(P,f(x_t))\,(y_t-P)\big].
--   $$
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 2, p.15

import Mathlib
import Definitions.Def_OmniMix_FinDist_expectR
import Definitions.Def_OmniMix_bV
import Definitions.Def_OmniMix_outVal

namespace OmniMix

/-- **Expert reward `z_{t,f,v}` of Algorithm 2.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, Algorithm 2, p.15: "For every expert
`(f, v) ∈ F × I_δ`, define its reward as `z_{t,f,v} = E_{P∼D_t}[b_v(P, f(x_t))(y_t − P)]`". -/
noncomputable def alg2Reward {X : Type*} {T : ℕ} (x : Fin T → X) (y : Fin T → Bool)
    (D : Fin T → FinDist) (t : Fin T) (f : X → unitInterval) (v : ℝ) : ℝ :=
  (D t).expectR (fun P => bV v P (f (x t)) * (outVal (y t) - P))

end OmniMix


