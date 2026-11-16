-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_LrT
-- name    : AutobidSPPE_Supplement_LrT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:46:33.516214+00:00
-- url     : https://prove2.me/theorems/f3d12106-60a3-4ae6-924c-47730a5f3111
-- title:
--   Throttling response Lipschitz bound $L_r$
-- statement:
--   $$
--   L_r=\max\{1,(n-1)U/(4\rho_{\min})\},\qquad U=\max_i\hat v_i,\quad \rho_{\min}=\min_i\rho_i .
--   $$
--   It bounds the max-norm Lipschitz constant of the throttling response. (It is not the pacing constant of (11).)
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (59), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_supU
import Definitions.Def_AutobidSPPE_rhoMin

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The throttling response Lipschitz bound `L_r = max{1, (n − 1)U/(4ρ_min)}` of (59)
(Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (59), p.28), `U = maxᵢ v̂ᵢ`, `ρ_min = minᵢ ρᵢ`. (Not the SPPE constant `AutobidSPPE.Lr` of (11).) -/
noncomputable def LrT {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ :=
  max 1 (((n : ℝ) - 1) * supU vhat / (4 * rhoMin ρ))

end AutobidSPPE.Supplement


