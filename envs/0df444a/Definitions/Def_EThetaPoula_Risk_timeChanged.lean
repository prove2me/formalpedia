-- Prove2me | Definitions.Def_EThetaPoula_Risk_timeChanged
-- name    : EThetaPoula_Risk_timeChanged
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:30.405776+00:00
-- url     : https://prove2.me/theorems/09d53c66-a1c3-42d5-a7cb-7f1f30a6b338
-- title:
--   The time-changed Brownian motion $B^\lambda_t:=B_{\lambda t}/\sqrt\lambda$
-- statement:
--   For a process $(B_t)_{t\ge0}$ and $\lambda>0$, $B^\lambda_t:=B_{\lambda t}/\sqrt\lambda$, $t\ge0$. This is again a Brownian motion, on the time scale of the algorithm's steps.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, p.22

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model

open scoped NNReal

namespace EThetaPoula.Risk

/-- The time-changed Brownian motion `B^λ_t := B_{λt}/√λ`, Lim, Neufeld, Sabanis, Zhang,
arXiv:2210.13193v3, §6.1, p.22. -/
noncomputable def timeChangedBM {d : ℕ} {Ω : Type*} (B : ℝ≥0 → Ω → Eucl d) (lam : ℝ) :
    ℝ≥0 → Ω → Eucl d :=
  fun t ω => (√lam)⁻¹ • B (Real.toNNReal (lam * t)) ω

end EThetaPoula.Risk


