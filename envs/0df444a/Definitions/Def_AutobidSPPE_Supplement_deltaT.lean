-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_deltaT
-- name    : AutobidSPPE_Supplement_deltaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:54:28.104961+00:00
-- url     : https://prove2.me/theorems/0d6fab9b-4ef5-490f-ba29-436df37ef6c1
-- title:
--   $\delta=\varepsilon/W$
-- statement:
--   $\delta=\varepsilon/W$, the factor between consecutive steps in (63).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (62), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_epsT
import Definitions.Def_AutobidSPPE_Supplement_WT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `δ = ε/W` of (62) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (62), p.28). -/
noncomputable def deltaT {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) : ℝ := epsT vhat ρ m / WT vhat ρ m

end AutobidSPPE.Supplement


