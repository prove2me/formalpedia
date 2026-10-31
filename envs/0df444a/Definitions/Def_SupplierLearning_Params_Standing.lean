-- Prove2me | Definitions.Def_SupplierLearning_Params_Standing
-- name    : SupplierLearning_Params_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:28.743022+00:00
-- url     : https://prove2.me/theorems/db5208d8-5827-4895-b015-136d3216dcf7
-- title:
--   Standing assumptions of the model
-- statement:
--   The standing assumptions: $\delta\in(0,1)$, $\nu,\rho\in(0,1)$, $c^\ell<c^h$, and $r^\ell,r^h>0$.
--
--   **Formalization Note** The paper states $\delta\in(0,1)$ and $c^\ell<c^h$ on p.5 and $r^\theta>0$ on p.9. Strict $\nu,\rho\in(0,1)$ is a reading: they are called priors, and the problem degenerates at the endpoints. The signs of $a_t$ and $c^\theta$ are not restricted.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, pp.5–6; §3, p.9

import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **Standing assumptions of the model.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, pp.5–6; §3, p.9 (PDF p.5, 6, 9).

**Formalization Note.** `δ ∈ (0,1)` and `c^ℓ < c^h` are stated on p.5, `r^θ > 0` on p.9 ("Public learning (r^θ > 0)"). `ν, ρ ∈ (0,1)` is a reading: the paper calls them priors and divides by `1 − ν`. The signs of `a_t` and `c^θ` are left free. -/
structure Params.Standing (P : Params) : Prop where
  δ_pos : 0 < P.δ
  δ_lt_one : P.δ < 1
  ν_pos : 0 < P.ν
  ν_lt_one : P.ν < 1
  ρ_pos : 0 < P.ρ
  ρ_lt_one : P.ρ < 1
  cost_lt : P.cl < P.ch
  rl_pos : 0 < P.rl
  rh_pos : 0 < P.rh

end SupplierLearning


