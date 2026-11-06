-- Prove2me | Definitions.Def_OmniMix_alg2Var
-- name    : OmniMix_alg2Var
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:54.611113+00:00
-- url     : https://prove2.me/theorems/3753ed6e-e206-4dd0-9dc3-cae08b9e18ec
-- title:
--   Second-order term of Algorithm 2
-- statement:
--   $$
--   \mathbb E_{P\sim D_t}\big[P(1-P)\,b_v(P,f(x_t))^2\big],
--   $$
--   the Bernoulli-variance correction in Algorithm 2's weight update (22).
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 2, p.15 and Eq. (22), p.13

import Mathlib
import Definitions.Def_OmniMix_FinDist_expectR
import Definitions.Def_OmniMix_bV

namespace OmniMix

/-- **Second-order term `E_{P∼D_t}[P(1 − P)b_v(P, f(x_t))²]` of Algorithm 2.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023,
Algorithm 2, p.15 and Eq. (22), p.13. -/
noncomputable def alg2Var {X : Type*} {T : ℕ} (x : Fin T → X) (D : Fin T → FinDist) (t : Fin T)
    (f : X → unitInterval) (v : ℝ) : ℝ :=
  (D t).expectR (fun P => (P : ℝ) * (1 - P) * bV v P (f (x t)) ^ 2)

end OmniMix


