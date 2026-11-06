-- Prove2me | Definitions.Def_DRSub4633_Bbudget
-- name    : DRSub4633_Bbudget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:08:02.418472+00:00
-- url     : https://prove2.me/theorems/bf22a16b-7f03-460c-a665-7733e5c1cffd
-- title:
--   The budget $B(\tau)$
-- statement:
--   $$B(\tau)=e^{-s\tau}\int_0^\tau[\theta(t)-\rho_1(t)]e^{st}\,dt.$$
--   It is the right side of the scalar averaging inequality (47).
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 4.7, Eq. (46), p.20

import Mathlib
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_theta
import Definitions.Def_DRSub4633_rho1

namespace DRSub4633

/-- **The budget `B(τ) = e^(−sτ) ∫_0^τ [θ(t) − ρ₁(t)] e^(st) dt`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 4.7, Eq. (46),
p.20. -/
noncomputable def Bbudget (τ : ℝ) : ℝ :=
  Real.exp (-(sPar * τ)) * ∫ t in (0 : ℝ)..τ, (theta t - rho1 t) * Real.exp (sPar * t)

end DRSub4633


