-- Prove2me | solution 1 for AlgoTransparency.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:50:01.537214+00:00
-- url     : https://prove2.me/submissions/10b35689-6a4d-4251-841f-0650fdc93a4e

import Mathlib
import Definitions.Def_AlgoTransparency_beta1

open AlgoTransparency in
theorem solution (p : AlgoTransparency.Params) :
    p.lam * p.θ * p.α - (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R <
        p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R ↔
      AlgoTransparency.beta1 p < p.β := by
  unfold AlgoTransparency.beta1
  constructor <;> intro h <;> linarith
