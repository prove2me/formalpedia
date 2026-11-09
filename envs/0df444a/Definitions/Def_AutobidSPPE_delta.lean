-- Prove2me | Definitions.Def_AutobidSPPE_delta
-- name    : AutobidSPPE_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:04:36.404185+00:00
-- url     : https://prove2.me/theorems/56630675-02d1-4dc5-93f1-8e9493bd60fe
-- title:
--   Step separation $\delta=\varepsilon/W$
-- statement:
--   The required step separation
--   $$
--   \delta=\varepsilon/W .
--   $$
--   The paper notes that $0<a\le1$, $b_0>1$ and $0<\delta<1$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (12), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_eps
import Definitions.Def_AutobidSPPE_W

namespace AutobidSPPE

/-- The required step separation `δ = ε/W` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (12), p.11). -/
noncomputable def delta {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ := eps vhat ρ / W vhat ρ

end AutobidSPPE


