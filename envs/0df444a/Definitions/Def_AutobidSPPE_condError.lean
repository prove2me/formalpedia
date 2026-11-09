-- Prove2me | Definitions.Def_AutobidSPPE_condError
-- name    : AutobidSPPE_condError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:05:11.589035+00:00
-- url     : https://prove2.me/theorems/ac3d3e2a-877d-412d-bfb3-2bb6c1a03446
-- title:
--   Conditional-target error $e_i(y)=y_i-h_i(y_{>i})$
-- statement:
--   The **conditional-target error** of bidder $i$ at the endpoint profile $y$ is
--   $$
--   e_i(y) = y_i - h_i(y_{>i}).
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §2.8, p.21

import Mathlib
import Definitions.Def_AutobidSPPE_target

namespace AutobidSPPE

/-- The conditional-target error `eᵢ(y) = yᵢ − hᵢ(y_{>i})` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §2.8, p.21). -/
noncomputable def condError {n : ℕ} (vbar ρ : Fin n → ℝ) (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  y i - target vbar ρ i y

end AutobidSPPE


