-- Prove2me | Definitions.Def_LL_KLEndpointBudget_tailMass
-- name    : LL_KLEndpointBudget_tailMass
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:55:06.224899+00:00
-- url     : https://prove2.me/theorems/8d25a41a-b473-435a-a85c-35aded25a092
-- title:
--   Endpoint mass $\nu_m(a)$ of the weight
-- statement:
--   For $m\in\mathbb N$ and real $a$, $\nu_m(a)=\int_0^{a}w_m(t)\,dt+\int_{1-a}^{1}w_m(t)\,dt$ (oriented interval integrals).

import Mathlib
import Definitions.Def_LL_KLEndpointBudget_weight

namespace LL_KLEndpointBudget

noncomputable section

open Real Set MeasureTheory intervalIntegral

noncomputable def tailMass (m : ℕ) (a : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..a, weight m t) + (∫ t in (1 - a)..1, weight m t)

end

end LL_KLEndpointBudget


